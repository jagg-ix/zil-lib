import Zil.Json.Ordered

/-!
# Traces in the Informal Trace Format

Apalache writes a counterexample as ITF (ADR-015). This module reads such a trace into typed values, writes it back, and prints
it as a list of states. The encodings were taken from traces the tool wrote (`test/fixtures/apalache/`, `docs/tool-notes.md`):
an integer is `{"#bigint": "3"}`, a set `{"#set": [...]}`, a tuple `{"#tup": [...]}`, a function `{"#map": [[key, value], ...]}`,
a record a plain object, and a value of an uninterpreted sort a string such as `"a_OF_NODE"`. Constants are listed under `params`;
their values are in the first state.
-/

namespace ZilLib.Apalache.Itf

open Zil.Json

/-- One value of a state. -/
inductive Value where
  | bool (value : Bool)
  | int (value : Int)
  | str (value : String)
  | set (items : Array Value)
  | tup (items : Array Value)
  | map (entries : Array (Value × Value))
  | record (fields : Array (String × Value))
  /-- A value the tool could not serialize, kept as the text it gave. -/
  | unserializable (text : String)
  deriving Inhabited

namespace Value

partial def beq : Value → Value → Bool
  | bool a, bool b => a == b
  | int a, int b => a == b
  | str a, str b => a == b
  | set a, set b => a.size == b.size && (a.zip b).all fun (x, y) => beq x y
  | tup a, tup b => a.size == b.size && (a.zip b).all fun (x, y) => beq x y
  | map a, map b => a.size == b.size && (a.zip b).all fun ((k, x), (l, y)) => beq k l && beq x y
  | record a, record b => a.size == b.size && (a.zip b).all fun ((k, x), (l, y)) => k == l && beq x y
  | unserializable a, unserializable b => a == b
  | _, _ => false

instance : BEq Value := ⟨beq⟩

/-- Read a value from its JSON encoding. -/
partial def ofJson : J → Except String Value
  | .bool value => pure (bool value)
  | .int value => pure (int value)
  | .str value => pure (str value)
  | .number text => throw s!"{text} is not an integer"
  | .null => throw "null is not a value of a trace"
  | .arr _ => throw "an array that is not tagged as a set or a tuple"
  | .obj fields =>
      match fields with
      | #[("#bigint", .str digits)] =>
          match digits.toInt? with
          | some value => pure (int value)
          | none => throw s!"{digits} is not an integer"
      | #[("#set", .arr items)] => set <$> items.mapM ofJson
      | #[("#tup", .arr items)] => tup <$> items.mapM ofJson
      | #[("#map", .arr pairs)] => do
          let mut entries := #[]
          for pair in pairs do
            match pair with
            | .arr #[key, value] => entries := entries.push (← ofJson key, ← ofJson value)
            | _ => throw "an entry of a map must be a pair"
          pure (map entries)
      | #[("#unserializable", .str text)] => pure (unserializable text)
      | _ =>
          if let some (tag, _) := fields.find? (·.1.startsWith "#") then
            throw s!"unknown tag {tag}"
          else
            record <$> fields.mapM fun (name, value) => do pure (name, ← ofJson value)

/-- The JSON encoding of a value. Integers are always written in the `#bigint` form. -/
partial def toJson : Value → J
  | bool value => .bool value
  | int value => .obj #[("#bigint", .str (toString value))]
  | str value => .str value
  | set items => .obj #[("#set", .arr (items.map toJson))]
  | tup items => .obj #[("#tup", .arr (items.map toJson))]
  | map entries => .obj #[("#map", .arr (entries.map fun (key, value) => .arr #[toJson key, toJson value]))]
  | record fields => .obj (fields.map fun (name, value) => (name, toJson value))
  | unserializable text => .obj #[("#unserializable", .str text)]

/-- The value as TLA+ text: `{a, b}`, `<<a, b>>`, `(k :> v @@ k2 :> v2)`, `[f |-> v]`. -/
partial def render : Value → String
  | bool true => "TRUE"
  | bool false => "FALSE"
  | int value => toString value
  | str value => writeString value (escapeSlash := false)
  | set items => "{" ++ ", ".intercalate (items.map render).toList ++ "}"
  | tup items => "<<" ++ ", ".intercalate (items.map render).toList ++ ">>"
  | map entries => "(" ++ " @@ ".intercalate (entries.map fun (key, value) => render key ++ " :> " ++ render value).toList ++ ")"
  | record fields => "[" ++ ", ".intercalate (fields.map fun (name, value) => name ++ " |-> " ++ render value).toList ++ "]"
  | unserializable text => s!"<unserializable: {text}>"

end Value

/-- One state of a trace: the tool's `#meta` object and the value of each variable (and, in the first state, each constant). -/
structure State where
  info : J
  values : Array (String × Value)
  deriving Inhabited

/-- A counterexample. -/
structure Trace where
  /-- The `#meta` object as written: format, description and the type of each variable. -/
  info : J
  /-- The names of the constants. Their values are in the first state. -/
  params : Array String
  vars : Array String
  states : Array State
  /-- The index of the state a lasso-shaped trace returns to, when it is one. -/
  loop : Option Nat
  deriving Inhabited

namespace Trace

private def names (field : String) (json : J) : Except String (Array String) :=
  match json.get? field with
  | none => pure #[]
  | some (.arr items) =>
      items.mapM fun item => match item.asStr? with
        | some name => pure name
        | none => throw s!"{field} must hold strings"
  | some _ => throw s!"{field} must be an array"

private def stateOfJson : J → Except String State
  | .obj fields => do
      let mut info : J := .obj #[]
      let mut values := #[]
      for (name, value) in fields do
        if name == "#meta" then info := value
        else values := values.push (name, ← Value.ofJson value)
      pure { info, values }
  | _ => throw "a state must be an object"

/-- Read a trace from its JSON document. -/
def ofJson (json : J) : Except String Trace := do
  let info := (json.get? "#meta").getD (.obj #[])
  unless info.getStr? "format" == some "ITF" do throw "not an ITF trace: #meta.format is not ITF"
  let states ← match json.get? "states" with
    | some (.arr items) => items.mapM stateOfJson
    | _ => throw "an ITF trace needs a states array"
  let loop ← match json.get? "loop" with
    | none => pure none
    | some (.int index) => if index < 0 then throw "loop must not be negative" else pure (some index.toNat)
    | some _ => throw "loop must be an integer"
  pure { info, params := ← names "params" json, vars := ← names "vars" json, states, loop }

/-- Read a trace from the text of a file. -/
def parse (text : String) : Except String Trace := do
  ofJson (← Zil.Json.parse text)

/-- The JSON document of a trace. -/
def toJson (trace : Trace) : J :=
  let strings (items : Array String) : J := .arr (items.map .str)
  let states := trace.states.map fun state => J.obj (#[("#meta", state.info)] ++ state.values.map fun (name, value) => (name, value.toJson))
  .obj (#[("#meta", trace.info)]
    ++ (if trace.params.isEmpty then #[] else #[("params", strings trace.params)])
    ++ #[("vars", strings trace.vars), ("states", .arr states)]
    ++ (match trace.loop with | some index => #[("loop", .int index)] | none => #[]))

/-- The value of `name` in state `index`. -/
def valueOf? (trace : Trace) (index : Nat) (name : String) : Option Value :=
  trace.states[index]? >>= fun state => state.values.find? (·.1 == name) |>.map (·.2)

/-- The trace as text, one state after the other. -/
def render (trace : Trace) : String := Id.run do
  let mut out := ""
  for state in trace.states, position in [0:trace.states.size] do
    let index := (state.info.getInt? "index").map Int.toNat |>.getD position
    out := out ++ s!"State {index}\n"
    for (name, value) in state.values do
      out := out ++ s!"  {name} = {value.render}\n"
  match trace.loop with
  | some index => out := out ++ s!"The trace returns to state {index}\n"
  | none => pure ()
  return out

end Trace

end ZilLib.Apalache.Itf

import Zil.Json.Ordered

/-!
# Apalache JSON Intermediate Representation (ADR-005) and Types (ADR-002)

This module defines the typed Abstract Syntax Tree (AST) for Apalache's JSON IR (ADR-005)
and Snowcat type system (ADR-002).

It provides:
- Inductive types for Snowcat types (`TlaType`) with parser and renderer.
- Inductive types for values, expressions, declarations, modules, and root documents.
- Byte-deterministic JSON serialization through `Zil.Json`.
- Deserialization (`ofJson`, `parse`) from JSON text.
- Standard operator identifiers (`Oper.*`).
-/

namespace ZilLib.Apalache.IR

open Zil.Json

private def optToRight {α : Type} (opt : Option α) (err : String) : Except String α :=
  match opt with
  | some x => .ok x
  | none => .error err

/-! ## 1. Snowcat Types (ADR-002) -/

/-- A Snowcat type in Apalache (ADR-002). -/
inductive TlaType where
  | int
  | bool
  | str
  | uninterpreted (name : String)
  | set (elem : TlaType)
  | seq (elem : TlaType)
  | tuple (elems : Array TlaType)
  | record (fields : Array (String × TlaType))
  | fn (arg : TlaType) (res : TlaType)
  | oper (params : Array TlaType) (res : TlaType)
  | untyped
  deriving Repr, Inhabited

namespace TlaType

partial def beq : TlaType → TlaType → Bool
  | int, int => true
  | bool, bool => true
  | str, str => true
  | uninterpreted a, uninterpreted b => a == b
  | set a, set b => beq a b
  | seq a, seq b => beq a b
  | tuple a, tuple b => a.size == b.size && (a.zip b).all fun (x, y) => beq x y
  | record a, record b => a.size == b.size && (a.zip b).all fun ((k1, v1), (k2, v2)) => k1 == k2 && beq v1 v2
  | fn a1 r1, fn a2 r2 => beq a1 a2 && beq r1 r2
  | oper p1 r1, oper p2 r2 => p1.size == p2.size && (p1.zip p2).all fun (x, y) => beq x y && beq r1 r2
  | untyped, untyped => true
  | _, _ => false

instance : BEq TlaType := ⟨beq⟩

/-- Render a type as a Snowcat type string. -/
partial def render : TlaType → String
  | int => "Int"
  | bool => "Bool"
  | str => "Str"
  | uninterpreted name => name
  | set elem => s!"Set({render elem})"
  | seq elem => s!"Seq({render elem})"
  | tuple elems =>
      let inner := ", ".intercalate (elems.map render).toList
      s!"<<{inner}>>"
  | record fields =>
      let inner := ", ".intercalate (fields.map fun (k, v) => s!"{k}: {render v}").toList
      "{ " ++ inner ++ " }"
  | fn arg res => s!"({render arg} -> {render res})"
  | oper params res =>
      if params.isEmpty then
        s!"(() => {render res})"
      else
        let inner := ", ".intercalate (params.map render).toList
        s!"(({inner}) => {render res})"
  | untyped => "Untyped"

private def trim (s : String) : String :=
  s.trimAscii.toString

/-- Simple recursive descent parser for Snowcat type strings. -/
partial def parse (s : String) : Except String TlaType := do
  let (t, rem) ← parseTokens (trim s)
  let rem := trim rem
  if rem.isEmpty then pure t
  else throw s!"trailing unparsed type tokens: '{rem}'"
where
  parseTokens (text : String) : Except String (TlaType × String) := do
    let text := trim text
    if text.isEmpty then throw "unexpected empty type string"
    else if text.startsWith "Int" then
      pure (int, (text.drop 3).toString)
    else if text.startsWith "Bool" then
      pure (bool, (text.drop 4).toString)
    else if text.startsWith "Str" then
      pure (str, (text.drop 3).toString)
    else if text.startsWith "Untyped" then
      pure (untyped, (text.drop 7).toString)
    else if text.startsWith "Set(" then
      let rest := (text.drop 4).toString
      let (inner, after) ← parseTokens rest
      let after := trim after
      if after.startsWith ")" then
        pure (set inner, (after.drop 1).toString)
      else throw s!"expected ')' after Set element, got '{after}'"
    else if text.startsWith "Seq(" then
      let rest := (text.drop 4).toString
      let (inner, after) ← parseTokens rest
      let after := trim after
      if after.startsWith ")" then
        pure (seq inner, (after.drop 1).toString)
      else throw s!"expected ')' after Seq element, got '{after}'"
    else if text.startsWith "<<" then
      let mut rest := (text.drop 2).toString
      let mut elems : Array TlaType := #[]
      rest := trim rest
      if rest.startsWith ">>" then
        pure (tuple #[], (rest.drop 2).toString)
      else
        let mut done := false
        while !done do
          let (elem, after) ← parseTokens rest
          elems := elems.push elem
          let after := trim after
          if after.startsWith "," then
            rest := trim (after.drop 1).toString
          else if after.startsWith ">>" then
            rest := (after.drop 2).toString
            done := true
          else
            throw s!"expected ',' or '>>' in tuple type, got '{after}'"
        pure (tuple elems, rest)
    else if text.startsWith "{" then
      let mut rest := trim (text.drop 1).toString
      let mut fields : Array (String × TlaType) := #[]
      if rest.startsWith "}" then
        pure (record #[], (rest.drop 1).toString)
      else
        let mut done := false
        while !done do
          let fieldName := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
          if fieldName.isEmpty then
            throw s!"expected field name in record type, got '{rest}'"
          let afterName := trim (rest.drop fieldName.length).toString
          if !afterName.startsWith ":" then
            throw s!"expected ':' after field '{fieldName}', got '{afterName}'"
          let afterColon := trim (afterName.drop 1).toString
          let (fieldType, after) ← parseTokens afterColon
          fields := fields.push (fieldName, fieldType)
          let after := trim after
          if after.startsWith "," then
            rest := trim (after.drop 1).toString
          else if after.startsWith "}" then
            rest := (after.drop 1).toString
            done := true
          else
            throw s!"expected ',' or '}' in record type, got '{after}'"
        pure (record fields, rest)
    else if text.startsWith "(" then
      let rest := trim (text.drop 1).toString
      if rest.startsWith ") =>" then
        let rest := trim (rest.drop 4).toString
        let (res, after) ← parseTokens rest
        let after := trim after
        if after.startsWith ")" then
          pure (oper #[] res, (after.drop 1).toString)
        else throw s!"expected ')' after operator return type: '{after}'"
      else if rest.startsWith "(" then
        let rest := trim (rest.drop 1).toString
        let mut params : Array TlaType := #[]
        let mut curRest := rest
        let mut parenDone := false
        while !parenDone do
          curRest := trim curRest
          if curRest.startsWith ")" then
            curRest := (curRest.drop 1).toString
            parenDone := true
          else
            let (param, after) ← parseTokens curRest
            params := params.push param
            let after := trim after
            if after.startsWith "," then
              curRest := trim (after.drop 1).toString
            else if after.startsWith ")" then
              curRest := (after.drop 1).toString
              parenDone := true
            else
              throw s!"expected ',' or ')' in operator parameter list: '{after}'"
        curRest := trim curRest
        if curRest.startsWith "=>" then
          let afterOp := trim (curRest.drop 2).toString
          let (res, after) ← parseTokens afterOp
          let after := trim after
          if after.startsWith ")" then
            pure (oper params res, (after.drop 1).toString)
          else throw s!"expected ')' closing operator type: '{after}'"
        else throw s!"expected '=>' in operator type: '{curRest}'"
      else
        let (arg, after) ← parseTokens rest
        let after := trim after
        if after.startsWith "->" then
          let rest := trim (after.drop 2).toString
          let (res, after) ← parseTokens rest
          let after := trim after
          if after.startsWith ")" then
            pure (fn arg res, (after.drop 1).toString)
          else throw s!"expected ')' after function type: '{after}'"
        else throw s!"expected '->' in function type: '{after}'"
    else
      let name := (text.takeWhile fun c => c.isAlphanum || c == '_').toString
      if name.isEmpty then
        throw s!"cannot parse type token at '{text}'"
      pure (uninterpreted name, (text.drop name.length).toString)

end TlaType

/-! ## 2. Values (ADR-005) -/

/-- A primitive value in Apalache IR. -/
inductive Val where
  | int (value : Int)
  | bool (value : Bool)
  | str (value : String)
  deriving Repr, BEq, Inhabited

namespace Val

def toJson : Val → J
  | int n => .obj #[("kind", .str "TlaInt"), ("value", .int n)]
  | bool b => .obj #[("kind", .str "TlaBool"), ("value", .bool b)]
  | str s => .obj #[("kind", .str "TlaStr"), ("value", .str s)]

def ofJson (j : J) : Except String Val := do
  let kind ← optToRight (j.getStr? "kind") "Val missing 'kind'"
  match kind with
  | "TlaInt" =>
      match j.get? "value" with
      | some (.int n) => pure (int n)
      | some other => throw s!"TlaInt expected integer, got {repr other}"
      | none => throw "TlaInt missing 'value'"
  | "TlaBool" =>
      match j.get? "value" with
      | some (.bool b) => pure (bool b)
      | some other => throw s!"TlaBool expected boolean, got {repr other}"
      | none => throw "TlaBool missing 'value'"
  | "TlaStr" =>
      match j.getStr? "value" with
      | some s => pure (str s)
      | none => throw "TlaStr missing string 'value'"
  | other => throw s!"unknown Val kind: {other}"

end Val

/-! ## 3. Expressions and Operator Declarations (Mutual AST) -/

structure FormalParam where
  name : String
  kind : String := "OperParam"
  arity : Int := 0
  deriving Repr, BEq, Inhabited

namespace FormalParam

def toJson (p : FormalParam) : J :=
  .obj #[("kind", .str p.kind), ("name", .str p.name), ("arity", .int p.arity)]

def ofJson (j : J) : Except String FormalParam := do
  let name ← optToRight (j.getStr? "name") "FormalParam missing 'name'"
  let kind := j.getStr? "kind" |>.getD "OperParam"
  let arity := match j.get? "arity" with
    | some (.int n) => n
    | _ => 0
  pure { name, kind, arity }

end FormalParam

mutual
  /-- An expression in Apalache IR (ADR-005). -/
  inductive Ex where
    | name (name : String) (type : String) (source : String := "UNKNOWN")
    | val (value : Val) (type : String) (source : String := "UNKNOWN")
    | oper (oper : String) (args : Array Ex) (type : String) (source : String := "UNKNOWN")
    | letIn (decls : Array OperDecl) (body : Ex) (type : String) (source : String := "UNKNOWN")
    deriving Repr, Inhabited

  /-- An operator declaration in Apalache IR (ADR-005). -/
  inductive OperDecl where
    | mk (name : String) (type : String) (formalParams : Array FormalParam) (isRecursive : Bool) (body : Ex) (source : String := "UNKNOWN")
    deriving Repr, Inhabited
end

mutual
  partial def exBeq : Ex → Ex → Bool
    | .name n1 t1 s1, .name n2 t2 s2 => n1 == n2 && t1 == t2 && s1 == s2
    | .val v1 t1 s1, .val v2 t2 s2 => v1 == v2 && t1 == t2 && s1 == s2
    | .oper o1 a1 t1 s1, .oper o2 a2 t2 s2 =>
        o1 == o2 && t1 == t2 && s1 == s2 && a1.size == a2.size && (a1.zip a2).all fun (x, y) => exBeq x y
    | .letIn d1 b1 t1 s1, .letIn d2 b2 t2 s2 =>
        t1 == t2 && s1 == s2 && exBeq b1 b2 && d1.size == d2.size && (d1.zip d2).all fun (x, y) => operDeclBeq x y
    | _, _ => false

  partial def operDeclBeq : OperDecl → OperDecl → Bool
    | .mk n1 t1 p1 r1 b1 s1, .mk n2 t2 p2 r2 b2 s2 =>
        n1 == n2 && t1 == t2 && p1 == p2 && r1 == r2 && s1 == s2 && exBeq b1 b2
end

instance : BEq Ex := ⟨exBeq⟩
instance : BEq OperDecl := ⟨operDeclBeq⟩

namespace OperDecl

def name : OperDecl → String | mk n _ _ _ _ _ => n
def type : OperDecl → String | mk _ t _ _ _ _ => t
def formalParams : OperDecl → Array FormalParam | mk _ _ p _ _ _ => p
def isRecursive : OperDecl → Bool | mk _ _ _ r _ _ => r
def body : OperDecl → Ex | mk _ _ _ _ b _ => b
def source : OperDecl → String | mk _ _ _ _ _ s => s

end OperDecl

mutual
  partial def exToJson : Ex → J
    | .name n t s =>
        .obj #[
          ("source", .str s),
          ("type", .str t),
          ("kind", .str "NameEx"),
          ("name", .str n)
        ]
    | .val v t s =>
        .obj #[
          ("source", .str s),
          ("type", .str t),
          ("kind", .str "ValEx"),
          ("value", v.toJson)
        ]
    | .oper op args t s =>
        .obj #[
          ("source", .str s),
          ("type", .str t),
          ("kind", .str "OperEx"),
          ("oper", .str op),
          ("args", .arr (args.map exToJson))
        ]
    | .letIn decls body t s =>
        .obj #[
          ("source", .str s),
          ("type", .str t),
          ("kind", .str "LetInEx"),
          ("body", exToJson body),
          ("decls", .arr (decls.map operDeclToJson))
        ]

  partial def operDeclToJson (d : OperDecl) : J :=
    .obj #[
      ("source", .str d.source),
      ("type", .str d.type),
      ("kind", .str "TlaOperDecl"),
      ("name", .str d.name),
      ("formalParams", .arr (d.formalParams.map FormalParam.toJson)),
      ("isRecursive", .bool d.isRecursive),
      ("body", exToJson d.body)
    ]
end

mutual
  partial def exOfJson (j : J) : Except String Ex := do
    let kind ← optToRight (j.getStr? "kind") "Expression missing 'kind'"
    let type ← optToRight (j.getStr? "type") "Expression missing 'type'"
    let source := j.getStr? "source" |>.getD "UNKNOWN"
    match kind with
    | "NameEx" =>
        let name ← optToRight (j.getStr? "name") "NameEx missing 'name'"
        pure (.name name type source)
    | "ValEx" =>
        let valJ ← optToRight (j.get? "value") "ValEx missing 'value'"
        let v ← Val.ofJson valJ
        pure (.val v type source)
    | "OperEx" =>
        let oper ← optToRight (j.getStr? "oper") "OperEx missing 'oper'"
        match j.get? "args" with
        | some (.arr argsArr) =>
            let args ← argsArr.mapM exOfJson
            pure (.oper oper args type source)
        | _ => throw "OperEx missing array 'args'"
    | "LetInEx" =>
        let bodyJ ← optToRight (j.get? "body") "LetInEx missing 'body'"
        let body ← exOfJson bodyJ
        match j.get? "decls" with
        | some (.arr declsArr) =>
            let decls ← declsArr.mapM operDeclOfJson
            pure (.letIn decls body type source)
        | _ => throw "LetInEx missing array 'decls'"
    | other => throw s!"unknown expression kind: {other}"

  partial def operDeclOfJson (j : J) : Except String OperDecl := do
    let kind ← optToRight (j.getStr? "kind") "OperDecl missing 'kind'"
    unless kind == "TlaOperDecl" do
      throw s!"expected 'TlaOperDecl', got '{kind}'"
    let name ← optToRight (j.getStr? "name") "OperDecl missing 'name'"
    let type ← optToRight (j.getStr? "type") "OperDecl missing 'type'"
    let source := j.getStr? "source" |>.getD "UNKNOWN"
    let isRecursive := match j.get? "isRecursive" with
      | some (.bool b) => b
      | _ => false
    let paramsArr := match j.get? "formalParams" with
      | some (.arr items) => items
      | _ => #[]
    let formalParams ← paramsArr.mapM FormalParam.ofJson
    let bodyJ ← optToRight (j.get? "body") "OperDecl missing 'body'"
    let body ← exOfJson bodyJ
    pure (.mk name type formalParams isRecursive body source)
end

/-! ## 4. Declarations, Modules, and Root -/

/-- A top-level declaration in a TLA module (ADR-005). -/
inductive Decl where
  | const (name : String) (type : String) (source : String := "UNKNOWN")
  | var (name : String) (type : String) (source : String := "UNKNOWN")
  | oper (decl : OperDecl)
  | assume (body : Ex) (name : Option String := none) (source : String := "UNKNOWN")
  deriving Repr, Inhabited

namespace Decl

def beq : Decl → Decl → Bool
  | const n1 t1 s1, const n2 t2 s2 => n1 == n2 && t1 == t2 && s1 == s2
  | var n1 t1 s1, var n2 t2 s2 => n1 == n2 && t1 == t2 && s1 == s2
  | oper d1, oper d2 => d1 == d2
  | assume b1 n1 s1, assume b2 n2 s2 => b1 == b2 && n1 == n2 && s1 == s2
  | _, _ => false

instance : BEq Decl := ⟨beq⟩

def toJson : Decl → J
  | const n t s =>
      .obj #[
        ("source", .str s),
        ("type", .str t),
        ("kind", .str "TlaConstDecl"),
        ("name", .str n)
      ]
  | var n t s =>
      .obj #[
        ("source", .str s),
        ("type", .str t),
        ("kind", .str "TlaVarDecl"),
        ("name", .str n)
      ]
  | oper d => operDeclToJson d
  | assume body none s =>
      .obj #[
        ("source", .str s),
        ("kind", .str "TlaAssumeDecl"),
        ("body", exToJson body)
      ]
  | assume body (some n) s =>
      .obj #[
        ("source", .str s),
        ("kind", .str "TlaAssumeDecl"),
        ("name", .str n),
        ("body", exToJson body)
      ]

def ofJson (j : J) : Except String Decl := do
  let kind ← optToRight (j.getStr? "kind") "Decl missing 'kind'"
  let source := j.getStr? "source" |>.getD "UNKNOWN"
  match kind with
  | "TlaConstDecl" =>
      let name ← optToRight (j.getStr? "name") "ConstDecl missing 'name'"
      let type ← optToRight (j.getStr? "type") "ConstDecl missing 'type'"
      pure (.const name type source)
  | "TlaVarDecl" =>
      let name ← optToRight (j.getStr? "name") "VarDecl missing 'name'"
      let type ← optToRight (j.getStr? "type") "VarDecl missing 'type'"
      pure (.var name type source)
  | "TlaOperDecl" =>
      let d ← operDeclOfJson j
      pure (.oper d)
  | "TlaAssumeDecl" =>
      let name := j.getStr? "name"
      let bodyJ ← optToRight (j.get? "body") "AssumeDecl missing 'body'"
      let body ← exOfJson bodyJ
      pure (.assume body name source)
  | other => throw s!"unknown declaration kind: {other}"

end Decl

/-- A TLA module in Apalache IR (ADR-005). -/
structure Module where
  name : String
  declarations : Array Decl
  deriving Repr, BEq, Inhabited

namespace Module

def toJson (m : Module) : J :=
  .obj #[
    ("kind", .str "TlaModule"),
    ("name", .str m.name),
    ("declarations", .arr (m.declarations.map Decl.toJson))
  ]

def ofJson (j : J) : Except String Module := do
  let kind ← optToRight (j.getStr? "kind") "Module missing 'kind'"
  unless kind == "TlaModule" do
    throw s!"expected 'TlaModule', got '{kind}'"
  let name ← optToRight (j.getStr? "name") "Module missing 'name'"
  match j.get? "declarations" with
  | some (.arr declsArr) =>
      let declarations ← declsArr.mapM Decl.ofJson
      pure { name, declarations }
  | _ => throw "Module missing array 'declarations'"

end Module

/-- The root document containing Apalache IR modules (ADR-005). -/
structure Root where
  name : String := "ApalacheIR"
  version : String := "1.0"
  description : String := "https://apalache-mc.org/docs/adr/005adr-json.html"
  modules : Array Module
  deriving Repr, BEq, Inhabited

namespace Root

def toJson (r : Root) : J :=
  .obj #[
    ("name", .str r.name),
    ("version", .str r.version),
    ("description", .str r.description),
    ("modules", .arr (r.modules.map Module.toJson))
  ]

def ofJson (j : J) : Except String Root := do
  let name := j.getStr? "name" |>.getD "ApalacheIR"
  let version := j.getStr? "version" |>.getD "1.0"
  let description := j.getStr? "description" |>.getD "https://apalache-mc.org/docs/adr/005adr-json.html"
  match j.get? "modules" with
  | some (.arr modsArr) =>
      let modules ← modsArr.mapM Module.ofJson
      pure { name, version, description, modules }
  | _ => throw "Root missing array 'modules'"

/-- Parse an Apalache IR document from JSON text. -/
def parse (text : String) : Except String Root := do
  let j ← Zil.Json.parse text
  ofJson j

/-- Write an Apalache IR document to canonical JSON text. -/
def write (r : Root) : String :=
  Zil.Json.write (toJson r) (escapeSlash := false) ++ "\n"

end Root

/-! ## 5. Standard Apalache Operator Identifiers -/

namespace Oper

-- Logic
def AND : String := "AND"
def OR : String := "OR"
def NOT : String := "NOT"
def IMPLIES : String := "IMPLIES"
def EQUIV : String := "EQUIV"
def EQ : String := "EQ"
def NE : String := "NE"

-- Sets
def SET_ENUM : String := "SET_ENUM"
def SET_IN : String := "SET_IN"
def SET_NOT_IN : String := "SET_NOT_IN"
def SET_SUBSET : String := "SET_SUBSET"
def SET_POWERSET : String := "SET_POWERSET"
def SET_UNION : String := "SET_UNION"
def SET_INTERSECT : String := "SET_INTERSECT"
def SET_MINUS : String := "SET_MINUS"
def SET_TIMES : String := "SET_TIMES"
def SET_FILTER : String := "SET_FILTER"
def SET_MAP : String := "SET_MAP"

-- Quantifiers
def FORALL3 : String := "FORALL3"
def EXISTS3 : String := "EXISTS3"

-- Arithmetic & Numbers
def PLUS : String := "PLUS"
def MINUS : String := "MINUS"
def MULT : String := "MULT"
def DIV : String := "DIV"
def MOD : String := "MOD"
def LT : String := "LT"
def LE : String := "LE"
def GT : String := "GT"
def GE : String := "GE"
def INT_RANGE : String := "INT_RANGE"

-- Tuples & Sequences
def TUPLE : String := "TUPLE"
def TUPLE_APP : String := "TUPLE_APP"
def SUBSEQ : String := "SUBSEQ"

-- Records
def RECORD : String := "RECORD"
def RECORD_ACCESS : String := "RECORD_ACCESS"
def EXCEPT : String := "EXCEPT"

-- Functions
def FUN_CTOR : String := "FUN_CTOR"
def FUN_APP : String := "FUN_APP"

-- Control & Evaluation
def IF_THEN_ELSE : String := "IF_THEN_ELSE"
def PRIME : String := "PRIME"
def UNCHANGED : String := "UNCHANGED"
def OPER_APP : String := "OPER_APP"

end Oper

/-! ## 6. Constructor Helpers -/

def intVal (n : Int) : Ex :=
  .val (.int n) "Int"

def boolVal (b : Bool) : Ex :=
  .val (.bool b) "Bool"

def strVal (s : String) : Ex :=
  .val (.str s) "Str"

def nodeVal (name : String) : Ex :=
  .val (.str name) "NODE"

def nameEx (name : String) (type : String) : Ex :=
  .name name type

def operEx (oper : String) (args : Array Ex) (type : String) : Ex :=
  .oper oper args type

def tlaVar (name : String) (type : String) : Decl :=
  .var name type

def tlaConst (name : String) (type : String) : Decl :=
  .const name type

def tlaOper (name : String) (type : String) (body : Ex) (formalParams : Array FormalParam := #[]) (isRecursive : Bool := false) : Decl :=
  .oper (.mk name type formalParams isRecursive body)

def tlaModule (name : String) (declarations : Array Decl) : Module :=
  { name, declarations }

def tlaRoot (modules : Array Module) : Root :=
  { modules }

end ZilLib.Apalache.IR

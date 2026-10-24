/-!
# Facts in the line form of the Lean command `zil_fact`

The core's Lean syntax writes a fact as

    zil_fact node(function.detect) ⟶[kind] node(framework.function)
    zil_fact node(tier.Tier1) ⟶[name] "Tier 1: Partial"

Tools that generate facts often write these lines into a `.zc` file, which the `.zc` parser does not read. `translate` rewrites them
to the `.zc` fact with the same meaning (`function.detect#kind@framework.function.`), line for line, so that the numbers of the
lines in a parse error stay those of the file. Every other line is left as it is, and a `zil_fact` line in any other shape is an
error: a fact on several lines, a string with an escape, or an object that is neither `node(...)` nor a string.
-/

namespace ZilLib.LeanFacts

private def skipSpaces : List Char → List Char
  | c :: rest => if c.isWhitespace then skipSpaces rest else c :: rest
  | [] => []

/-- The characters up to the first `stop` (not included), and what follows it. -/
private def upTo (stop : Char) (chars : List Char) : Option (String × List Char) :=
  go [] chars
where
  go (taken : List Char) : List Char → Option (String × List Char)
    | [] => none
    | c :: rest => if c == stop then some (String.ofList taken.reverse, rest) else go (c :: taken) rest

/-- `chars` without the front `text`, when it starts with it. -/
private def strip? (text : String) (chars : List Char) : Option (List Char) :=
  let front := text.toList
  if chars.take front.length == front then some (chars.drop front.length) else none

/-- The name in `node(NAME)` at the front of `chars`, and what follows. -/
private def node? (chars : List Char) : Option (String × List Char) := do
  let (name, rest) ← upTo ')' (← strip? "node(" chars)
  if name.isEmpty || name.any (fun c => c.isWhitespace || c == '(') then none else some (name, rest)

/-- One line: the `.zc` fact for a `zil_fact` line, `none` for any other line. -/
def line? (text : String) : Except String (Option String) := do
  let chars := skipSpaces text.toList
  let some afterCommand := strip? "zil_fact" chars | return none
  -- `zil_factory ...` is not the command
  unless afterCommand.isEmpty || (afterCommand.head?.map Char.isWhitespace).getD false do return none
  let some (subject, afterSubject) := node? (skipSpaces afterCommand)
    | throw "zil_fact has to start with node(NAME)"
  let some afterArrow := strip? "⟶[" (skipSpaces afterSubject) | throw "zil_fact has to continue with ⟶[RELATION]"
  let some (relation, afterRelation) := upTo ']' afterArrow | throw "the relation of zil_fact is not closed by ]"
  if relation.isEmpty || relation.any (fun c => !(c.isAlphanum || c == '_')) then
    throw s!"the relation {relation} is not a name"
  let target := skipSpaces afterRelation
  let (object, rest) ← match node? target with
    | some (name, rest) => pure (name, rest)
    | none => match strip? "\"" target with
        | some quoted =>
            match upTo '"' quoted with
            | some (value, rest) =>
                if value.any (· == '\\') then throw "a string with an escape is not supported"
                else pure ("\"" ++ value ++ "\"", rest)
            | none => throw "the string of zil_fact is not closed"
        | none => throw "the object of zil_fact is neither node(NAME) nor a string"
  let rest := skipSpaces rest
  unless rest.isEmpty || (strip? "//" rest).isSome do throw s!"unexpected text after the object: {String.ofList rest}"
  return some s!"{subject}#{relation}@{object}."

/-- All the lines of a model; the error names the line. -/
def translate (text : String) : Except String String := do
  let mut out := #[]
  let mut number := 0
  for line in text.splitOn "\n" do
    number := number + 1
    match line? line with
    | .ok (some fact) => out := out.push fact
    | .ok none => out := out.push line
    | .error problem => throw s!"line {number}: {problem}"
  return "\n".intercalate out.toList

end ZilLib.LeanFacts

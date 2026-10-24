import ZilLib.TransitionSystem
import ZilLib.SMT.Text

/-!
# SMT-LIB 2 Model & Output Parser (TS-03)

Parses solver responses (`sat`, `unsat`, `unknown`) and model values from `(get-value ...)`
S-expressions, reconstructing authentic `TSState` vectors aligned with the `TSModule` schema.
-/

namespace ZilLib.SMT

open ZilLib.TransitionSystem

/-- Parse an SMT-LIB atom into a `TSVal`. -/
def parseSmtVal (token : String) : Except String TSVal := do
  let t := token.trimAscii.toString
  if t == "true" then pure (.bool true)
  else if t == "false" then pure (.bool false)
  else if t.startsWith "(- " && t.endsWith ")" then
    let inner := (t.drop 3).dropEnd 1 |>.trimAscii.toString
    match inner.toInt? with
    | some n => pure (.int (-n))
    | none => throw s!"cannot parse negative integer: '{t}'"
  else
    match t.toInt? with
    | some n => pure (.int n)
    | none =>
        -- Check if it is an enum symbol: sortName_elem
        let parts := t.splitOn "_"
        if parts.length >= 2 then
          let sn := parts.head!
          let elem := "_".intercalate parts.tail!
          pure (.enumVal sn elem)
        else
          throw s!"unrecognized SMT value: '{t}'"

/--
Simple recursive descent tokenizer and parser for SMT-LIB 2 `(get-value ((var val) ...))` blocks.
Handles nested parenthesized expressions like `((|v_x_0| 0) (|v_y_0| (- 1)))`.
-/
partial def parsePairs (tokens : List String) : Except String (List (String × String)) := do
  match tokens with
  | [] => pure []
  | "(" :: varTok :: valTok :: ")" :: rest =>
      let cleanVar := if varTok.startsWith "|" && varTok.endsWith "|" then
        (varTok.drop 1).dropEnd 1 |>.toString
      else varTok
      let (valStr, nextTokens) :=
        if valTok == "(" then
          -- Nested expression like `( - 5 )`
          let rec collectNested (acc : List String) (depth : Nat) (toks : List String) : (String × List String) :=
            match toks with
            | [] => (" ".intercalate acc, [])
            | ")" :: rem =>
                if depth == 1 then (" ".intercalate (acc ++ [")"]), rem)
                else collectNested (acc ++ [")"]) (depth - 1) rem
            | "(" :: rem => collectNested (acc ++ ["("]) (depth + 1) rem
            | item :: rem => collectNested (acc ++ [item]) depth rem
          let (nested, rem) := collectNested ["("] 1 (valTok :: rest).tail!
          (nested, rem)
        else
          (valTok, rest)
      let tailPairs ← parsePairs nextTokens
      pure ((cleanVar, valStr) :: tailPairs)
  | _ => throw s!"malformed pair list starting at: {tokens.take 5}"

/-- Tokenize SMT-LIB 2 text around parentheses and whitespace. -/
def tokenizeSmt (s : String) : List String :=
  let rec loop (chars : List Char) (cur : String) (acc : List String) : List String :=
    match chars with
    | [] => if cur.isEmpty then acc.reverse else (cur :: acc).reverse
    | '(' :: cs =>
        let acc' := if cur.isEmpty then acc else cur :: acc
        loop cs "" ("(" :: acc')
    | ')' :: cs =>
        let acc' := if cur.isEmpty then acc else cur :: acc
        loop cs "" (")" :: acc')
    | c :: cs =>
        if c.isWhitespace then
          let acc' := if cur.isEmpty then acc else cur :: acc
          loop cs "" acc'
        else
          loop cs (cur.push c) acc
  loop s.toList "" []

/-- Parse an SMT-LIB 2 `(get-value ...)` response into `(variableName, TSVal)` pairs. -/
def parseGetValueResponse (text : String) : Except String (List (String × TSVal)) := do
  let tokens := tokenizeSmt text
  -- Top-level should be `( ( (var1 val1) (var2 val2) ... ) )`
  match tokens with
  | "(" :: rest =>
      let inner := if rest.head? == some "(" && rest.getLast? == some ")" then
        rest.dropLast
      else rest
      let rawPairs ← parsePairs inner
      rawPairs.mapM fun (k, v) => do
        let parsedVal ← parseSmtVal v
        pure (k, parsedVal)
  | _ => throw s!"expected '(' opening get-value response, got: {text.take 30}"

/--
Reconstruct a sequence of `TSState` vectors from parsed solver variable pairs.
Each state is indexed $s \in [0 \dots depth]$ and has elements ordered strictly
by `m.variables`.
-/
def reconstructTrace (m : TSModule) (depth : Nat) (valPairs : List (String × TSVal)) : Except String (Array TSState) := do
  let mut states : Array TSState := #[]
  for s in [0:depth + 1] do
    let mut stateVals : Array TSVal := #[]
    for v in m.variables do
      let keyWithBars := s!"v_{v.name}_{s}"
      match valPairs.find? (fun (k, _) => k == keyWithBars || k == s!"|{keyWithBars}|") with
      | some (_, val) => stateVals := stateVals.push val
      | none => throw s!"solver model missing variable '{v.name}' at step {s}"
    states := states.push ⟨stateVals⟩
  pure states

end ZilLib.SMT

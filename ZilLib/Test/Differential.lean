import ZilLib.Certify
import ZilLib.Model
import ZilLib.Test.Harness
import Zil.Datalog.Certify

/-!
# The engine against the evaluator that has a proof

The core has two evaluators for rules with negation and attributes. The engine (`Zil.Engine`) is indexed and fast; the Lean-embedded
Datalog (`Zil.Datalog.deriveProgramChecked`) is a plain list implementation about which the core proves that its result is a stratified
model whose atoms all have derivations (`deriveProgramChecked_ok`). They share no code for matching or for the fixpoint loop. A
generator of small random programs (a few relations and constants, facts with attributes, rules with two positive premises, a negative
premise on a lower relation, attributes in the patterns) gives both the same program, through the translation of `ZilLib.Certify.Verified`,
and the two sets of facts must be the same.

A disagreement means a defect in the engine, in the evaluator, or in the translation; the program is printed in the syntax of a model so
that it can be run again. The same seed gives the same programs.
-/

namespace ZilLib.Test.Differential

open Zil

private def contains (text needle : String) : Bool := (text.splitOn needle).length > 1

/-- The number of fact lines of a generated program (every one starts with `n:c`; rules start with `RULE`, `IF` or `THEN`). -/
private def factLines (text : String) : Nat :=
  ((text.splitOn "\n").filter fun (line : String) => line.startsWith "n:c").length

/-- A generator of numbers, deterministic for a seed (a linear congruential generator, 64 bits). -/
structure Rng where
  state : IO.Ref Nat

namespace Rng

def new (seed : Nat) : IO Rng := do pure { state := ← IO.mkRef (seed % 18446744073709551616) }

/-- A number below `bound` (at least 1). -/
def below (rng : Rng) (bound : Nat) : IO Nat := do
  let next := (← rng.state.get) * 6364136223846793005 + 1442695040888963407
  let next := next % 18446744073709551616
  rng.state.set next
  pure ((next / 4294967296) % (max bound 1))

def pick {α : Type} [Inhabited α] (rng : Rng) (choices : Array α) : IO α := do
  pure choices[← rng.below choices.size]!

end Rng

/-- A text or number, for the keys `a` and `b`, which no rule reads with a variable. -/
private def literal (rng : Rng) : IO String := do
  rng.pick #["1", "2", "\"p\"", "\"q\""]

/-- A node, for the key `k`, which rules read with a variable (the engine binds a variable in an attribute only to a node). -/
private def nodeValue (rng : Rng) (constants : Nat) : IO String := do
  pure s!"n:c{← rng.below constants}"

/-- A fact: `n:c0#rel1@n:c2 [a=1].` -/
private def fact (rng : Rng) (relations constants : Nat) : IO String := do
  let relation ← rng.below relations
  let subject ← rng.below constants
  let object ← rng.below constants
  let attrs ← match ← rng.below 5 with
    | 0 => do pure s!" [a={← literal rng}]"
    | 1 => do pure s!" [a={← literal rng}, b={← literal rng}]"
    | 2 => do pure s!" [k={← nodeValue rng constants}]"
    | 3 => do pure s!" [a={← literal rng}, k={← nodeValue rng constants}]"
    | _ => pure ""
  pure s!"n:c{subject}#rel{relation}@n:c{object}{attrs}."

/-- A term of a pattern: one of the variables, or a constant. -/
private def term (rng : Rng) (variables : Array String) (constants : Nat) : IO String := do
  if (← rng.below 4) == 0 then pure s!"n:c{← rng.below constants}" else rng.pick variables

/-- A positive premise over a relation that is not above `ceiling`. Returns its text and the variables it binds. -/
private def premise (rng : Rng) (ceiling constants : Nat) : IO (String × Array String) := do
  let relation ← rng.below (ceiling + 1)
  let variables := #["?x", "?y", "?z"]
  let subject ← term rng variables constants
  let object ← term rng variables constants
  let attr ← match ← rng.below 5 with
    | 0 => pure (some ("k", "?v"))
    | 1 => do pure (some ("a", ← literal rng))
    | 2 => do pure (some ("k", ← nodeValue rng constants))
    | _ => pure none
  let text := s!"{subject}#rel{relation}@{object}" ++ (match attr with | some (k, v) => s!" [{k}={v}]" | none => "")
  let bound := ([subject, object] ++ (match attr with | some (_, v) => [v] | none => [])).filter (·.startsWith "?")
  pure (text, bound.toArray)

/-- A rule for the relation `head`: one or two positive premises, sometimes a negative one over a lower relation, and a head that uses
only the variables the positive premises bind. -/
private def rule (rng : Rng) (index head constants : Nat) : IO String := do
  let positives ← (List.range (1 + (← rng.below 2))).mapM fun _ => premise rng head constants
  let bound := (positives.foldl (init := #[]) fun all p => p.2.foldl (init := all) fun all v => if all.contains v then all else all.push v)
  let constantOnly := bound.isEmpty
  let headTerm : IO String := do
    if constantOnly || (← rng.below 5) == 0 then
      let constant ← rng.below constants
      pure s!"n:c{constant}"
    else rng.pick bound
  let negative ← if head > 0 && (← rng.below 2) == 0 then do
      let relation ← rng.below head
      let subject ← if constantOnly || (← rng.below 3) == 0 then pure s!"n:c{← rng.below constants}" else rng.pick bound
      let object ← if constantOnly || (← rng.below 3) == 0 then pure s!"n:c{← rng.below constants}" else rng.pick bound
      pure (some s!"{subject}#rel{relation}@{object}")
    else pure none
  let headSubject ← headTerm
  let headObject ← headTerm
  let attrs ← match ← rng.below 4 with
    | 0 => do
        if bound.any (· == "?v") then pure " [k=?v]" else pure s!" [a={← literal rng}]"
    | 1 => do pure s!" [k={← nodeValue rng constants}]"
    | _ => pure ""
  let body := " AND ".intercalate (positives.map (·.1) ++ (match negative with | some n => [s!"NOT {n}"] | none => []))
  pure s!"RULE r{index}:\nIF {body}\nTHEN {headSubject}#rel{head}@{headObject}{attrs}."

/-- One random program as model text. -/
def program (rng : Rng) : IO String := do
  let relations := 2 + (← rng.below 3)
  let constants := 2 + (← rng.below 3)
  let facts ← (List.range (3 + (← rng.below 8))).mapM fun _ => fact rng relations constants
  let rules ← (List.range (1 + (← rng.below 4))).mapM fun i => do rule rng i (← rng.below relations) constants
  pure ("MODULE random.\n" ++ "\n".intercalate facts ++ "\n" ++ "\n".intercalate rules ++ "\n")

/-- The atoms of the engine's closure and the evaluator's result, or the reason one of them could not be had. -/
private def both (text : String) : IO (Except String (Option (List Datalog.Atom × List Datalog.Atom))) := do
  let directory ← IO.FS.createTempDir
  let file := directory / "random.zc"
  IO.FS.writeFile file text
  let loaded ← (ZilLib.loadProgram file.toString).toBaseIO
  IO.FS.removeDirAll directory
  match loaded with
  | .error _ => pure (.ok none) -- the generator wrote something the parser refuses (an unsafe rule): not a program
  | .ok program =>
      unless program.valid do return .ok none
      match Zil.Engine.closureChecked program.facts program.allRules with
      | .error reason => pure (.error s!"the engine: {reason}")
      | .ok closed =>
          match ZilLib.Certify.Verified.toProgram program.facts program.allRules with
          | .error reason => pure (.error s!"translation: {reason}")
          | .ok translated =>
              match Datalog.deriveProgramChecked translated with
              | .error reason => pure (.error s!"the evaluator: {reason}")
              | .ok atoms =>
                  match closed.toList.mapM ZilLib.Certify.Verified.toAtom with
                  | .error reason => pure (.error s!"translation of the closure: {reason}")
                  | .ok engineAtoms => pure (.ok (some (engineAtoms.eraseDups, atoms)))

/-- Run `count` random programs from `seed`; report the first disagreement, if any. Returns the number run and the number refused by
the parser. -/
def run (t : Tally) (count seed : Nat) : IO Unit := do
  let rng ← Rng.new seed
  let mut ran := 0
  let mut refused := 0
  let mut failures := 0
  let mut derivedSomething := 0
  let mut withNegation := 0
  for i in [0:count] do
    let text ← program rng
    match ← both text with
    | .ok none => refused := refused + 1
    | .error reason =>
        failures := failures + 1
        t.expect s!"program {i} (seed {seed}): {reason}" false s!"\n{text}"
    | .ok (some (engine, evaluator)) =>
        ran := ran + 1
        -- how much the comparison exercised: programs that derive something, and programs with a negative premise
        if evaluator.length > factLines text then derivedSomething := derivedSomething + 1
        if contains text "NOT " then withNegation := withNegation + 1
        let same := engine.all evaluator.contains && evaluator.all engine.contains
        if !same then
          failures := failures + 1
          let onlyEngine := engine.filter (!evaluator.contains ·)
          let onlyEvaluator := evaluator.filter (!engine.contains ·)
          t.expect s!"program {i} (seed {seed}): the engine and the evaluator derive the same facts" false
            s!"\n{text}\nonly the engine: {repr onlyEngine}\nonly the evaluator: {repr onlyEvaluator}"
  IO.println s!"      {ran} programs compared, {derivedSomething} derive facts, {withNegation} have a negative premise, {refused} refused by the parser"
  t.expect s!"{ran} random programs: the engine and the evaluator with a proof derive the same facts"
    (failures == 0 && ran * 2 > count && derivedSomething * 4 > ran && withNegation * 4 > ran)

end ZilLib.Test.Differential

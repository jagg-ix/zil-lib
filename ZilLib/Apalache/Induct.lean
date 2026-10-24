import ZilLib.Apalache.Evidence

/-!
# Checking that an invariant is inductive

An invariant `Inv` is inductive when every initial state satisfies it (the base case) and every step from a state that satisfies it
leads to a state that satisfies it (the step). Then it holds in every reachable state, however long the execution.

The tool checks both cases for a given assignment of the constants:

* the base case: `check --init=Init --inv=Inv --length=0`;
* the step: `check --init=IndInit --next=Next --inv=Inv --length=1`, where `IndInit` is a predicate in assignment form that
  ranges each variable over its type and requires `Inv`. The model supplies it, because only the model knows the types of its
  variables.

Deadlocks are not looked for: a state without a successor is not a counterexample to an invariant, and the step starts in
arbitrary states of which some may have none.

What a pass means. It holds for the constants that were set, and only for them. A counterexample to the step is a state
that satisfies `IndInit` and leaves `Inv` after one step. Such a state may be unreachable, so it is a hint that the invariant
lacks a conjunct, not a defect of the model. A fixed domain size is still a bound: a statement for every size needs a proof outside
the tool.
-/

namespace ZilLib.Apalache.Induct

open Zil.Json

/-- What to check. -/
structure Config where
  model : System.FilePath
  /-- The predicate that sets the constants (`--cinit`). -/
  cinit : Option String := none
  init : String := "Init"
  next : String := "Next"
  /-- The assignment-form predicate that describes the states to step from, and includes the invariant. -/
  indInit : String
  /-- The invariant to show inductive. -/
  inv : Array String
  timeoutMs : Nat := 600000
  deriving Inhabited

/-- What the two runs came to. -/
inductive Outcome where
  /-- Both cases passed. -/
  | holds (base step : Result)
  /-- Some initial state violates the invariant. -/
  | baseFails (base : Result)
  /-- The step leaves the invariant: a counterexample to induction, in `step.trace`. -/
  | notInductive (base step : Result)
  /-- A run did not give an answer: it timed out, failed, was rejected or could not start. `phase` says which. -/
  | stopped (phase : String) (result : Result)
  deriving Inhabited

namespace Config

def base (config : Config) : ZilLib.Apalache.Config :=
  { model := config.model, init := some config.init, next := some config.next, inv := config.inv, cinit := config.cinit,
    length := 0, noDeadlock := true, timeoutMs := config.timeoutMs }

def step (config : Config) : ZilLib.Apalache.Config :=
  { model := config.model, init := some config.indInit, next := some config.next, inv := config.inv, cinit := config.cinit,
    length := 1, noDeadlock := true, timeoutMs := config.timeoutMs }

end Config

private def passes (result : Result) : Bool := result.verdict == .noError || result.verdict == .tooShort

/-- Run the base case and then the step. The step is not run when the base case already fails. -/
def run (config : Config) (tool : Tool) : IO Outcome := do
  let base ← check config.base tool
  if base.verdict == .violation then return .baseFails base
  unless passes base do return .stopped "base case" base
  let step ← check config.step tool
  if passes step then return .holds base step
  if step.verdict == .violation then return .notInductive base step
  return .stopped "step" step

namespace Outcome

/-- The verdict as the evidence names it, or `none` when the runs say nothing about the model. -/
def verdict : Outcome → Option String
  | .holds .. => some "inductive-at-the-constants"
  | .baseFails .. => some "base-case-violated"
  | .notInductive .. => some "counterexample-to-induction"
  | .stopped _ result => if result.verdict == .timedOut then some "inconclusive-timeout" else none

/-- The result whose trace, tool and timing describe the outcome. -/
def last : Outcome → Result
  | .holds _ step => step
  | .baseFails base => base
  | .notInductive _ step => step
  | .stopped _ result => result

end Outcome

private def listOf (items : Array String) : J := .arr (items.map .str)

/-- The parameters of the check, as they enter the identity of the evidence. -/
def parameters (config : Config) : J :=
  .obj #[("cinit", config.cinit.map J.str |>.getD .null), ("indinit", .str config.indInit), ("init", .str config.init),
    ("inv", listOf config.inv), ("next", .str config.next)]

/-- The sentence that says what the verdict holds for. -/
def statement (config : Config) (verdict : String) : String :=
  let invariants := ", ".intercalate config.inv.toList
  let constants := match config.cinit with | some name => s!"the constants set by {name}" | none => "the constants of the model"
  match verdict with
  | "inductive-at-the-constants" =>
      s!"{invariants} holds in every initial state and is preserved by every step from {config.indInit}, so it holds in every reachable state at {constants} and at no other constants"
  | "base-case-violated" => s!"an initial state violates {invariants} at {constants}"
  | "counterexample-to-induction" =>
      s!"a state that satisfies {config.indInit} leaves {invariants} after one step at {constants}; the state may be unreachable"
  | _ => s!"the check did not finish within its deadline, so nothing is known about {invariants} at {constants}"

/-- The envelope for the two runs, or `none` when they say nothing about the model. -/
def evidence (config : Config) (outcome : Outcome) : IO (Option (Except String J)) := do
  let some verdict := outcome.verdict | return none
  let last := outcome.last
  let toolVersion := last.tool.map (·.version) |>.getD ""
  some <$> Evidence.envelope config.model (",".intercalate config.inv.toList)
    { kind := "induction", verdict, statement := statement config verdict, outcome := last.outcome,
      parameters := parameters config, toolVersion, metadata := Evidence.runMetadata last }

private def tailOf (text : String) (characters : Nat) : String :=
  String.ofList (text.toList.drop (text.length - characters))

/-- The report: what was run, what came of it, and what it does not say. -/
def report (config : Config) (outcome : Outcome) : String := Id.run do
  let invariants := ", ".intercalate config.inv.toList
  let mut out := ""
  match outcome with
  | .holds .. =>
      out := out ++ s!"{invariants}: inductive at the constants that were set. Both cases passed.\n"
      out := out ++ "This holds for these constants only. It is not a proof for other sizes.\n"
  | .baseFails base =>
      out := out ++ s!"{invariants}: not inductive. An initial state violates it (the base case).\n"
      if let some trace := base.trace then out := out ++ trace.render
  | .notInductive _ step =>
      out := out ++ s!"{invariants}: not inductive. The state below satisfies {config.indInit} and leaves {invariants} after one step.\n"
      out := out ++ "A counterexample to induction is a finding, not a defect: the state may be unreachable, and the invariant may need a stronger conjunct.\n"
      if let some trace := step.trace then out := out ++ trace.render
  | .stopped phase result =>
      match result.verdict with
      | .timedOut => out := out ++ s!"{invariants}: inconclusive. The {phase} did not finish within its deadline.\n"
      | .failed code => out := out ++ s!"The {phase} failed: the tool exited with {code}.\n{tailOf result.stdout 600}\n"
      | .rejected reason => out := out ++ s!"The {phase} was not run: {reason}.\n"
      | .unavailable reason => out := out ++ s!"The {phase} could not be run: {reason}.\n"
      | _ => out := out ++ s!"The {phase} did not give an answer.\n"
  return out

end ZilLib.Apalache.Induct

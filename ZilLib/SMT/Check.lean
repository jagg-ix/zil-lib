import ZilLib.TransitionSystem
import ZilLib.SMT.Text
import ZilLib.SMT.Parser
import ZilLib.SMT.Run

/-!
# SMT Bounded Model Checker and $k$-Induction Engine (TS-03)

Orchestrates SMT-LIB 2 queries, executes the solver, parses counterexample traces,
and verifies every candidate counterexample against Lean's authoritative `replayTrace` reference.
-/

namespace ZilLib.SMT

open ZilLib.TransitionSystem

/-- The outcome verdict of an SMT model checking or induction run. -/
inductive SmtVerdict where
  /-- No violation exists in any trace of length up to `bound`. -/
  | noViolationWithinBound (bound : Nat)
  /-- A violation of `invariant` was found at `depth` and confirmed by Lean's `replayTrace`. -/
  | violationFound (depth : Nat) (trace : Array TSState)
  /-- The invariant is $k$-inductive (proved for all reachable states). -/
  | inductiveProved (k : Nat)
  /-- The candidate invariant is not $k$-inductive (step case counterexample). -/
  | nonInductive (k : Nat) (counterexample : Array TSState)
  /-- The solver reported unknown or timed out (inconclusive, never a pass). -/
  | inconclusive (reason : String)
  /-- Solver error, rejected input, or trace failed Lean reference replay check. -/
  | rejected (reason : String)
  /-- SMT solver executable was not found. -/
  | unavailable (reason : String)
  deriving Repr, Inhabited

namespace SmtVerdict

def isPass : SmtVerdict → Bool
  | noViolationWithinBound _ => true
  | inductiveProved _ => true
  | _ => false

def isViolation : SmtVerdict → Bool
  | violationFound _ _ => true
  | nonInductive _ _ => true
  | _ => false

def exitCode : SmtVerdict → UInt32
  | noViolationWithinBound _ => 0
  | inductiveProved _ => 0
  | violationFound _ _ => 1
  | nonInductive _ _ => 1
  | rejected _ => 2
  | unavailable _ => 3
  | inconclusive _ => 4

end SmtVerdict

/-- Comprehensive result of an SMT check run. -/
structure SmtResult where
  verdict : SmtVerdict
  moduleName : String
  invName : String
  solver : Option Tool := none
  script : String := ""
  stdout : String := ""
  elapsedMs : Nat := 0
  deriving Inhabited

/--
Perform Bounded Model Checking (BMC) of `invName` up to `maxDepth` on `m`.
Every discovered violation is checked through `ZilLib.TransitionSystem.replayTrace`.
-/
def checkBMC
    (m : TSModule)
    (invName : String)
    (maxDepth : Nat)
    (tool : Tool)
    (timeoutMs : Nat := 30000) : IO SmtResult := do
  let started ← IO.monoMsNow
  let finish (v : SmtVerdict) (script out : String) : IO SmtResult := do
    let elapsed := (← IO.monoMsNow) - started
    pure {
      verdict := v,
      moduleName := m.name,
      invName := invName,
      solver := some tool,
      script := script,
      stdout := out,
      elapsedMs := elapsed
    }

  let script ← match bmcScript m invName maxDepth with
    | .ok s => pure s
    | .error err => return ← finish (.rejected err) "" ""

  match ← runSmtScript tool script timeoutMs with
  | .error "timeout" => finish (.inconclusive "solver timed out") script ""
  | .error err => finish (.inconclusive s!"solver error: {err}") script ""
  | .ok out =>
      -- Parse step outputs
      let sections := out.splitOn "=== STEP "
      let mut foundViolation : Option (Nat × Array TSState) := none
      let mut hadError : Option String := none

      for sec in sections.tail! do
        let lines := sec.splitOn "\n" |>.map (fun s => s.trimAscii.toString) |>.filter (!·.isEmpty)
        if lines.isEmpty then continue
        let header := lines.head!
        let stepNum := (header.splitOn " ").head!.toNat?.getD 0
        let restLines := lines.tail!
        if restLines.isEmpty then continue
        let outcome := restLines.head!

        if outcome == "sat" then
          let modelText := "\n".intercalate restLines.tail!
          match parseGetValueResponse modelText with
          | .error pe => hadError := some s!"model parse error at step {stepNum}: {pe}"
          | .ok pairs =>
              match reconstructTrace m stepNum pairs with
              | .error re => hadError := some s!"trace reconstruction error at step {stepNum}: {re}"
              | .ok trace =>
                  -- Authoritative Lean reference replay verification
                  if replayTrace m trace.toList invName then
                    foundViolation := some (stepNum, trace)
                    break
                  else
                    hadError := some s!"solver model at step {stepNum} failed Lean replayTrace verification"
                    break
        else if outcome == "unknown" then
          hadError := some s!"solver returned unknown at step {stepNum}"
          break

      if let some (d, trace) := foundViolation then
        finish (.violationFound d trace) script out
      else if let some err := hadError then
        finish (.rejected err) script out
      else
        finish (.noViolationWithinBound maxDepth) script out

/--
Perform $k$-induction verification of `invName` at depth `k` on `m`.
1. Base check: ensures no violation occurs within steps $0 \dots k$ from `Init`.
2. Step check: ensures $k$ consecutive states satisfying `Inv` cannot transition to $\neg Inv$.
-/
def checkInduct
    (m : TSModule)
    (invName : String)
    (k : Nat)
    (tool : Tool)
    (timeoutMs : Nat := 30000) : IO SmtResult := do
  let started ← IO.monoMsNow
  let finish (v : SmtVerdict) (script out : String) : IO SmtResult := do
    let elapsed := (← IO.monoMsNow) - started
    pure {
      verdict := v,
      moduleName := m.name,
      invName := invName,
      solver := some tool,
      script := script,
      stdout := out,
      elapsedMs := elapsed
    }

  let (baseScript, stepScript) ← match inductScript m invName k with
    | .ok pair => pure pair
    | .error err => return ← finish (.rejected err) "" ""

  -- 1. Base case check
  match ← runSmtScript tool baseScript timeoutMs with
  | .error "timeout" => return ← finish (.inconclusive "base case timed out") baseScript ""
  | .error err => return ← finish (.inconclusive s!"base case solver error: {err}") baseScript ""
  | .ok baseOut =>
      let baseLines := baseOut.splitOn "\n" |>.map (fun s => s.trimAscii.toString) |>.filter (!·.isEmpty)
      let baseVerdict := baseLines.headD "unknown"
      if baseVerdict == "sat" then
        -- Invariant violated within base case
        let modelText := "\n".intercalate baseLines.tail!
        match parseGetValueResponse modelText with
        | .ok pairs =>
            match reconstructTrace m k pairs with
            | .ok trace =>
                return ← finish (.violationFound k trace) baseScript baseOut
            | .error _ => return ← finish (.rejected "failed to reconstruct base violation trace") baseScript baseOut
        | .error _ => return ← finish (.rejected "failed to parse base violation model") baseScript baseOut
      else if baseVerdict != "unsat" then
        return ← finish (.inconclusive s!"base case returned {baseVerdict}") baseScript baseOut

  -- 2. Step case check
  match ← runSmtScript tool stepScript timeoutMs with
  | .error "timeout" => finish (.inconclusive "step case timed out") stepScript ""
  | .error err => finish (.inconclusive s!"step case solver error: {err}") stepScript ""
  | .ok stepOut =>
      let stepLines := stepOut.splitOn "\n" |>.map (fun s => s.trimAscii.toString) |>.filter (!·.isEmpty)
      let stepVerdict := stepLines.headD "unknown"
      if stepVerdict == "unsat" then
        -- Inductive step proved!
        finish (.inductiveProved k) stepScript stepOut
      else if stepVerdict == "sat" then
        -- Step counterexample (candidate invariant is not inductive)
        let modelText := "\n".intercalate stepLines.tail!
        match parseGetValueResponse modelText with
        | .ok pairs =>
            match reconstructTrace m k pairs with
            | .ok trace => finish (.nonInductive k trace) stepScript stepOut
            | .error _ => finish (.nonInductive k #[]) stepScript stepOut
        | .error _ => finish (.nonInductive k #[]) stepScript stepOut
      else
        finish (.inconclusive s!"step case returned {stepVerdict}") stepScript stepOut

end ZilLib.SMT

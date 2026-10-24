import Lean
import ZilLib.TransitionSystem

/-!
# Transition System Unit Tests (TS-01)

Tests for AST evaluation, type synthesis, agreement, witness trace replay, and safety theorem guards.
Runs at compilation time via `run_cmd`.
-/

namespace ZilLib.Test.TransitionSystem

open Lean Elab Command
open ZilLib.TransitionSystem

-- Helper to construct state with single integer variable
def stateX (val : Int) : TSState :=
  ⟨#[.int val]⟩

run_cmd do
  -- 1. Test counterModule evaluation
  let s0 := stateX 0
  let s1 := stateX 1
  let s2 := stateX 2
  let s3 := stateX 3

  unless evalInit counterModule s0 == true do
    throwError "evalInit counterModule s0 failed"
  unless evalInit counterModule s1 == false do
    throwError "evalInit counterModule s1 should be false"

  unless evalNext counterModule s0 s1 == true do
    throwError "evalNext counterModule s0 s1 failed"
  unless evalNext counterModule s1 s2 == true do
    throwError "evalNext counterModule s1 s2 failed"
  unless evalNext counterModule s0 s2 == false do
    throwError "evalNext counterModule s0 s2 should be false"

  -- Invariant evaluation
  unless evalInv counterModule s0 (.ge (.var "x" false) (.constInt 0)) == true do
    throwError "invariant x >= 0 on s0 failed"
  unless evalInv counterModule (stateX (-1)) (.ge (.var "x" false) (.constInt 0)) == false do
    throwError "invariant x >= 0 on x=-1 should fail"

  -- 2. Test typeOf and QF_LIA constraint on multiplication
  let mulConst := TSExpr.mul (.constInt 2) (.var "x" false)
  unless typeOf counterModule mulConst == some .int do
    throwError "typeOf failed on linear multiplication"

  let mulNonConst := TSExpr.mul (.var "x" false) (.var "x" false)
  if (typeOf counterModule mulNonConst).isSome then
    throwError "typeOf allowed non-linear multiplication (violating QF_LIA)"

  -- 3. Trace Replay Reference:
  -- (a) Valid trace without violation should return false (no violation verified)
  let traceGood := [s0, s1, s2, s3]
  if replayTrace counterModule traceGood "x_nonneg" then
    throwError "replayTrace on good trace reported violation unexpectedly"

  -- (b) Module with candidate invariant that fails:
  let counterCandidateInv : TSModule := {
    counterModule with
    invariants := [("x_le_1", .le (.var "x" false) (.constInt 1))]
  }
  let traceViolating := [s0, s1, s2]
  unless replayTrace counterCandidateInv traceViolating "x_le_1" == true do
    throwError "replayTrace failed to confirm genuine violation at x=2"

  -- (c) Fabricated trace with invalid initial state must be refused (returns false)
  let traceBadInit := [s1, s2]
  if replayTrace counterCandidateInv traceBadInit "x_le_1" then
    throwError "replayTrace accepted trace with bad initial state"

  -- (d) Fabricated trace with invalid transition step must be refused
  let traceBadStep := [s0, s2] -- jumped from 0 to 2 directly
  if replayTrace counterCandidateInv traceBadStep "x_le_1" then
    throwError "replayTrace accepted trace with discontinuous transition"

  -- (e) Trace where terminal state does NOT violate invariant must be refused
  let traceNotViolating := [s0, s1]
  if replayTrace counterCandidateInv traceNotViolating "x_le_1" then
    throwError "replayTrace reported violation when invariant held at terminal state"

-- 4. Theorem and Axiom checks
run_cmd do
  for thm in [``counter_safe, ``reachable_iff_reachableIn, ``denote_agree, ``denote_init_agree, ``denote_next_agree] do
    let axioms ← liftCoreM <| collectAxioms thm
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{thm} depends on unexpected axiom {ax}"

end ZilLib.Test.TransitionSystem

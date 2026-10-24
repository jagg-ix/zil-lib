import ZilLib.Model
import ZilLib.Lower
import ZilLib.Lower.Operations
import ZilLib.Operation
import ZilLib.SMT
import ZilLib.SMT.Run
import ZilLib.SMT.Check
import ZilLib.Test.Harness

/-!
# Batch 4 Tests: Operations (APL-31), Temporal Governance (APL-32 / S2), and Non-Interference (APL-33 / S3)

Covers all required inventory tests:
- APL-31: apply_operation_guard_satisfied, apply_operation_guard_refused,
  apply_operation_adds_and_removes, apply_operation_parameter_binding,
  spec_written_and_verified, two_examples_compiled_and_expanded.
- APL-32: delegation_escalation_found, last_admin_lockout_found,
  separation_of_duty_holds, trace_replayed_by_executor.
- APL-33: leaking_policy_found, isolated_policy_passes,
  observation_function_respected.
-/

namespace ZilLib.Test.Batch4

open Zil
open ZilLib.TransitionSystem
open ZilLib.SMT
open ZilLib.Lower
open ZilLib.Lower.Operations
open ZilLib.Operation
open ZilLib.Test

def run (withTool : Bool) : IO Bool := do
  let t ← Tally.new

  -----------------------------------------------------------------------------
  -- 1. APL-31: Operations Specification and Reference Lean Executor
  -----------------------------------------------------------------------------

  -- spec_written_and_verified
  let specPath : System.FilePath := "spec/operations-v0.1.md"
  let specExists ← specPath.pathExists
  let specHasContent ← if specExists then do
    let content ← IO.FS.readFile specPath
    pure (content.contains "Operations and Temporal Governance Specification" &&
          content.contains "CHECK_OPERATION" &&
          content.contains "Non-Interference")
  else pure false

  t.expect "APL-31: spec_written_and_verified: spec exists with operations and hyperproperties"
    (specExists && specHasContent)

  -- Load the two invented examples for APL-31
  let pDepth ← ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/operations/01-delegation-depth.zc"
  let pLockout ← ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/operations/02-admin-lockout.zc"

  t.expect "APL-31: two_examples_compiled_and_expanded"
    (pDepth.facts.size > 0 && pLockout.facts.size > 0)

  -- Verify extraction
  let opsDepth := extractOperations pDepth
  let opsLockout := extractOperations pLockout

  t.expect "APL-31: extract_operations_depth"
    (opsDepth.any (·.name == "delegate_root") && opsDepth.any (·.name == "delegate_sub"))

  t.expect "APL-31: extract_operations_lockout"
    (opsLockout.any (·.name == "revoke_admin"))

  -- Test Lean Reference Executor on pDepth (01-delegation-depth.zc)
  -- 1. Alice delegates to Bob (valid guard, depth d2)
  let inv1 : OpInvocation := {
    opName := "delegate_root"
    bindings := [("p_from", "node:alice"), ("p_to", "node:bob")]
  }
  let res1 := executeOperation pDepth (opsDepth.find? (·.name == "delegate_root") |>.get!) inv1 pDepth.facts
  t.expect "APL-31: apply_operation_guard_satisfied: Alice delegates to Bob"
    res1.isOk

  let factsAfter1 := res1.toOption.getD #[]
  t.expect "APL-31: apply_operation_adds_and_removes: delegates_to edge added"
    (factsAfter1.any fun f =>
      cleanTermName f.subject == "alice" &&
      matchRelName (toString f.relation) "delegates_to" &&
      cleanTermName f.object == "bob")

  -- 2. Charlie attempting to delegate to Dave directly fails guard (Charlie has no depth)
  let invFail : OpInvocation := {
    opName := "delegate_root"
    bindings := [("p_from", "node:charlie"), ("p_to", "node:dave")]
  }
  let resFail := executeOperation pDepth (opsDepth.find? (·.name == "delegate_root") |>.get!) invFail pDepth.facts
  t.expect "APL-31: apply_operation_guard_refused: Charlie has no delegation budget"
    (!resFail.isOk)

  -- Test parameter completeness validation
  let invMissingParam : OpInvocation := {
    opName := "delegate_root"
    bindings := [("p_from", "node:alice")]
  }
  let resMissing := executeOperation pDepth (opsDepth.find? (·.name == "delegate_root") |>.get!) invMissingParam pDepth.facts
  t.expect "APL-31: apply_operation_parameter_binding: missing parameter rejected"
    (!resMissing.isOk)

  -- Test trace execution on pLockout (02-admin-lockout.zc)
  -- Step 1: admin1 revokes admin2
  -- Step 2: admin1 revokes admin1 -> lockout (0 admins remain)
  let traceLockout : List OpInvocation := [
    { opName := "revoke_admin", bindings := [("p_caller", "node:admin1"), ("p_target", "node:admin2")] },
    { opName := "revoke_admin", bindings := [("p_caller", "node:admin1"), ("p_target", "node:admin1")] }
  ]
  let resTrace := executeTrace pLockout opsLockout pLockout.facts traceLockout
  t.expect "APL-31: execute_trace_reaches_lockout"
    resTrace.isOk

  if let .ok finalFacts := resTrace then
    let anyAdminRemaining := finalFacts.any fun f =>
      cleanName (toString f.relation) == "has_role" && cleanTermName f.object == "admin"
    t.expect "APL-31: lockout_confirmed: zero admins remain after trace"
      (!anyAdminRemaining)

  -----------------------------------------------------------------------------
  -- 2. APL-32: Temporal Governance and Trace Replay (Strategic Result S2)
  -----------------------------------------------------------------------------

  let pSod ← ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/operations/03-separation-of-duty.zc"
  let opsSod := extractOperations pSod
  t.expect "APL-32: extract_operations_sod"
    (opsSod.any (·.name == "request_tx") && opsSod.any (·.name == "approve_tx"))

  let pEsc ← ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/operations/01-delegation-escalation.zc"
  let opsEsc := extractOperations pEsc
  t.expect "APL-32: extract_operations_escalation"
    (opsEsc.any (·.name == "unconstrained_delegate"))

  if withTool then
    let solverOpt ← locateInEnvironment "z3"
    match solverOpt with
    | .found tool =>
        -- separation_of_duty_holds on 03-separation-of-duty.zc
        let (tsModSod, _, _) ← match lowerOperationsModule pSod with
          | .ok res => pure res
          | .error e => throw (IO.userError s!"lowerOperationsModule pSod failed: {e}")
        let sodInvName := tsModSod.invariants.head?.map (·.1) |>.getD "no_self_approval"
        let resSod ← checkBMC tsModSod sodInvName 4 tool 30000
        let sodHolds := match resSod.verdict with
          | .noViolationWithinBound _ => true
          | _ => false
        t.expect "APL-32: separation_of_duty_holds: dual control invariant verified within bound 4"
          sodHolds

        -- last_admin_lockout_found and trace_replayed_by_executor on 02-admin-lockout.zc
        let (tsModLockout, dLockout, opsL) ← match lowerOperationsModule pLockout with
          | .ok res => pure res
          | .error e => throw (IO.userError s!"lowerOperationsModule pLockout failed: {e}")
        let lockoutInvName := tsModLockout.invariants.head?.map (·.1) |>.getD "admin_lockout"
        let resLockout ← checkBMC tsModLockout lockoutInvName 3 tool 30000

        let (lockoutFound, lockoutDepth, rawTrace) := match resLockout.verdict with
          | .violationFound d tr => (true, d, tr)
          | _ => (false, 0, #[])
        t.expect "APL-32: last_admin_lockout_found: solver detected admin lockout"
          (lockoutFound && (lockoutDepth == 1 || lockoutDepth == 2))

        -- Reconstruct high-level operation trace from solver counterexample
        let opTrace := reconstructOpTrace pLockout dLockout tsModLockout opsL rawTrace
        t.expect "APL-32: trace_reconstructed: high-level invocations extracted from solver trace"
          (opTrace.length >= 1 && opTrace.all (·.opName == "revoke_admin"))

        -- Replay counterexample in Lean reference executor
        let replayRes := executeTrace pLockout opsL pLockout.facts opTrace
        let replayConfirmed := match replayRes with
          | .ok finalFacts =>
              finalFacts.any fun f =>
                cleanTermName f.subject == "admin1" &&
                matchRelName (toString f.relation) "is_anchor" &&
                !finalFacts.any (fun f2 => cleanTermName f2.subject == "admin1" && matchRelName (toString f2.relation) "has_role")
          | .error _ => false
        t.expect "APL-32: trace_replayed_by_executor: Lean executor replayed trace and confirmed lockout"
          replayConfirmed

        -- delegation_escalation_found on 01-delegation-escalation.zc
        let (tsModEsc, _, _) ← match lowerOperationsModule pEsc with
          | .ok res => pure res
          | .error e => throw (IO.userError s!"lowerOperationsModule pEsc failed: {e}")
        let escInvName := tsModEsc.invariants.head?.map (·.1) |>.getD "no_dave_delegation"
        let resEsc ← checkBMC tsModEsc escInvName 3 tool 30000
        let escFound := match resEsc.verdict with
          | .violationFound _ _ => true
          | _ => false
        t.expect "APL-32: delegation_escalation_found: unconstrained delegation detected by solver"
          escFound

        -----------------------------------------------------------------------
        -- 3. APL-33: Non-Interference and Hyperproperty Checking (Strategic Result S3)
        -----------------------------------------------------------------------

        let pLeak ← ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/operations/04-leaking-policy.zc"
        let pIso ← ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/operations/05-isolated-policy.zc"

        -- Extract public projections
        let extractPublic (p : Program) : List String :=
          let pubFacts := p.facts.filter fun f =>
            cleanName (toString f.relation) == "relation" &&
            (nodeNameOfTerm f.subject).any (·.contains "pub_")
          pubFacts.filterMap (fun f => nodeNameOfTerm f.object |>.map cleanName) |>.toList

        let pubLeak := extractPublic pLeak
        let pubIso := extractPublic pIso

        t.expect "APL-33: observation_function_respected: public projections accurately extracted"
          (pubLeak.contains "public_flag" && !pubLeak.contains "secret_data" &&
           pubIso.contains "public_state" && !pubIso.contains "private_state")

        -- leaking_policy_found on 04-leaking-policy.zc
        let opsLeak := extractOperations pLeak
        let dLeak := operationsDomain pLeak opsLeak
        let tsModLeak := lowerNonInterferenceModule pLeak dLeak opsLeak pubLeak
        let resLeak ← checkBMC tsModLeak "public_non_interference" 2 tool 30000
        let leakFound := match resLeak.verdict with
          | .violationFound d _ => d == 1
          | _ => false
        t.expect "APL-33: leaking_policy_found: 2-safety violation detected at depth 1"
          leakFound

        -- isolated_policy_passes on 05-isolated-policy.zc
        let opsIso := extractOperations pIso
        let dIso := operationsDomain pIso opsIso
        let tsModIso := lowerNonInterferenceModule pIso dIso opsIso pubIso
        let resIso ← checkBMC tsModIso "public_non_interference" 3 tool 30000
        let isoHolds := match resIso.verdict with
          | .noViolationWithinBound _ => true
          | _ => false
        t.expect "APL-33: isolated_policy_passes: non-interference verified within bound 3"
          isoHolds

    | .missing name =>
        IO.eprintln s!"Batch4Tests: solver '{name}' not found on PATH; skipping SMT BMC tests"
    | .broken path detail =>
        IO.eprintln s!"Batch4Tests: solver '{path}' broken: {detail}; skipping SMT BMC tests"

  t.finish

end ZilLib.Test.Batch4

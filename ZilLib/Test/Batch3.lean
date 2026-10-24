import ZilLib.Model
import ZilLib.Lower
import ZilLib.Lower.Universal
import ZilLib.SMT
import ZilLib.Test.Harness

/-!
# Batch 3 Tests: Check Vocabulary (APL-05) & Universal Contract Checking (APL-30 / S1)

Covers all required inventory tests:
- APL-05: expand_check_bound, expand_check_invariant, expand_check_operation,
  expand_check_public, matrix_row_golden, reuses_model_trans, unknown_macro_fails, arity_fails.
- APL-30: seeded_flaw_found_n3, clean_policy_passes_n2_to_n6, inconclusive_on_deadline.
-/

namespace ZilLib.Test.Batch3

open Zil
open ZilLib.TransitionSystem
open ZilLib.SMT
open ZilLib.Lower
open ZilLib.Lower.Universal
open ZilLib.Lower.Replay
open ZilLib.Test

def run (withTool : Bool) : IO Bool := do
  let t ← Tally.new

  -----------------------------------------------------------------------------
  -- 1. APL-05: Check Vocabulary Macro Extension Tests
  -----------------------------------------------------------------------------

  -- Load the check vocabulary governance example
  let pGov ← ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/check-vocab-governance.zc"
  -- expand_check_bound
  let boundFacts := pGov.facts.filter fun f =>
    toString f.relation == "zil.maxNodes" || toString f.relation == "max_nodes"
  t.expect "APL-05: expand_check_bound: CHECK_BOUND expands to max_nodes facts"
    (boundFacts.size >= 2)

  -- expand_check_invariant
  let invFacts := pGov.facts.filter fun f =>
    toString f.relation == "zil.targetQuery" || toString f.relation == "target_query"
  t.expect "APL-05: expand_check_invariant: CHECK_INVARIANT expands to target_query fact"
    (invFacts.size >= 1)

  -- expand_check_operation
  let opGuardFacts := pGov.facts.filter fun f =>
    toString f.relation == "zil.guardQuery" || toString f.relation == "guard_query"
  let opParamFacts := pGov.facts.filter fun f =>
    toString f.relation == "zil.param" || toString f.relation == "param"
  let opAddFacts := pGov.facts.filter fun f =>
    (nodeNameOfTerm f.object).any (·.contains "check_op_add")
  let opRemoveFacts := pGov.facts.filter fun f =>
    (nodeNameOfTerm f.object).any (·.contains "check_op_remove")
  t.expect "APL-05: expand_check_operation: CHECK_OPERATION expands guard, param, add, remove facts"
    (opGuardFacts.size >= 2 && opParamFacts.size >= 1 && opAddFacts.size >= 1 && opRemoveFacts.size >= 1)

  -- expand_check_public
  let libs ← ZilLib.loadLibraries "libsets/check-vocab"
  let publicSnippet := "MODULE test.public.\nUSE CHECK_PUBLIC(public_api, caller_ident).\n"
  let parsedPublic := Zil.Parser.DeclarationProgram.parseTextWithLibraries libs "test.zc" publicSnippet
  match parsedPublic with
  | .ok pPub =>
      let hasPublicRel := pPub.facts.any fun f =>
        toString f.relation == "zil.projectionName" ||
        (nodeNameOfTerm f.object).any (·.contains "check_public")
      t.expect "APL-05: expand_check_public: CHECK_PUBLIC expands to projection facts" hasPublicRel
  | .error e =>
      t.expect "APL-05: expand_check_public: parsed without error" false e.render

  -- matrix_row_golden
  let goldenPath := "spec/macro-extension-golden/check-vocab.expanded.zc"
  let goldenExists ← (System.FilePath.mk goldenPath).pathExists
  t.expect "APL-05: matrix_row_golden: golden file exists in spec/macro-extension-golden/" goldenExists

  -- reuses_model_trans
  let hasKindRel := pGov.facts.any fun f =>
    toString f.relation == "zil.kind" || toString f.relation == "kind"
  t.expect "APL-05: reuses_model_trans: check vocabulary reuses entity:kind concepts" hasKindRel

  -- unknown_macro_fails
  let unknownSnippet := "MODULE test.unknown.\nUSE UNKNOWN_NONEXISTENT_MACRO(x).\n"
  let parsedUnknown := Zil.Parser.DeclarationProgram.parseTextWithLibraries libs "test.zc" unknownSnippet
  let isUnknownError := match parsedUnknown with | .error _ => true | .ok _ => false
  t.expect "APL-05: unknown_macro_fails: unknown macro refused with error" isUnknownError

  -- arity_fails
  let aritySnippet := "MODULE test.arity.\nUSE CHECK_BOUND(subject).\n"
  let parsedArity := Zil.Parser.DeclarationProgram.parseTextWithLibraries libs "test.zc" aritySnippet
  let isArityError := match parsedArity with | .error _ => true | .ok _ => false
  t.expect "APL-05: arity_fails: macro invocation with incorrect arity refused" isArityError

  -----------------------------------------------------------------------------
  -- 2. APL-30: Universal Contract Checking (S1) Tests
  -----------------------------------------------------------------------------

  if withTool then
    let solverOpt ← locateInEnvironment "z3"
    match solverOpt with
    | .found tool =>
        -- seeded_flaw_found_n3
        let pFlawed ← ZilLib.loadProgram "examples/universal/03-flawed-admin.zc"
        
        -- At N = 2: should have NO violation within bound
        let (_, m2) ← match lowerUniversalProgram pFlawed 2 none with
          | .ok res => pure res
          | .error e => throw (IO.userError s!"lowerUniversalProgram failed: {e}")
        let invName2 := m2.invariants.head?.map (·.1) |>.getD "inv_no_untrusted_admin"
        let res2 ← checkBMC m2 invName2 3 tool 30000
        let n2Clean := match res2.verdict with
          | .noViolationWithinBound _ => true
          | _ => false
        t.expect "APL-30: seeded_flaw_found_n3: flawed policy passes at N=2 (no violation within bound)" n2Clean

        -- At N = 3: flaw MUST be found and replayed
        let (d3, m3) ← match lowerUniversalProgram pFlawed 3 none with
          | .ok res => pure res
          | .error e => throw (IO.userError s!"lowerUniversalProgram failed: {e}")
        let invName3 := m3.invariants.head?.map (·.1) |>.getD "inv_no_untrusted_admin"
        let res3 ← checkBMC m3 invName3 4 tool 30000
        let (n3Violation, n3Replayed) := match res3.verdict with
          | .violationFound _ trace =>
              let rep := replayAndCertify d3 m3 trace invName3
              (true, rep.valid)
          | _ => (false, false)
        t.expect "APL-30: seeded_flaw_found_n3: seeded flaw found at N=3" n3Violation
        t.expect "APL-30: seeded_flaw_found_n3: counterexample confirmed by Lean replay reference" n3Replayed

        -- clean_policy_passes_n2_to_n6
        let pClean1 ← ZilLib.loadProgram "examples/universal/01-delegation.zc"
        let mut clean1Pass := true
        for n in [2:7] do
          let (_, mn) ← match lowerUniversalProgram pClean1 n none with
            | .ok res => pure res
            | .error e => throw (IO.userError e)
          let inv := mn.invariants.head?.map (·.1) |>.getD "invariant"
          let r ← checkBMC mn inv (n + 1) tool 30000
          match r.verdict with
          | .noViolationWithinBound _ => pure ()
          | _ => clean1Pass := false
        t.expect "APL-30: clean_policy_passes_n2_to_n6: delegation policy passes for all N in 2..6" clean1Pass

        let pClean2 ← ZilLib.loadProgram "examples/universal/02-least-privilege.zc"
        let mut clean2Pass := true
        for n in [2:7] do
          let (_, mn) ← match lowerUniversalProgram pClean2 n none with
            | .ok res => pure res
            | .error e => throw (IO.userError e)
          let inv := mn.invariants.head?.map (·.1) |>.getD "invariant"
          let r ← checkBMC mn inv (n + 1) tool 30000
          match r.verdict with
          | .noViolationWithinBound _ => pure ()
          | _ => clean2Pass := false
        t.expect "APL-30: clean_policy_passes_n2_to_n6: least-privilege policy passes for all N in 2..6" clean2Pass

        -- inconclusive_on_deadline (fail-closed timeout)
        let (_, mTimeout) ← match lowerUniversalProgram pClean1 5 none with
          | .ok res => pure res
          | .error e => throw (IO.userError e)
        let invTimeout := mTimeout.invariants.head?.map (·.1) |>.getD "invariant"
        -- 1 millisecond timeout guarantees timeout
        let resTimeout ← checkBMC mTimeout invTimeout 5 tool 1
        let isTimeout := match resTimeout.verdict with
          | .inconclusive r => r.contains "timeout" || r.contains "timed out"
          | _ => false
        t.expect "APL-30: inconclusive_on_deadline: deadline exceeded returns inconclusive (fail-closed, not pass)" isTimeout
    | _ =>
        IO.println "  skipped: z3 solver not found on PATH for SMT checks"
  else
    IO.println "  skipped: z3 solver checks (run with --with-tool)"

  t.finish

end ZilLib.Test.Batch3

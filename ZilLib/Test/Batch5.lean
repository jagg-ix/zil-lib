import Zil.Core.Program
import ZilLib.Model
import ZilLib.TransitionSystem
import ZilLib.Lower.Equivalence
import ZilLib.Repair.Hints
import ZilLib.GenTests.Generate
import ZilLib.Lower.StaleViews
import ZilLib.Lower.NumericLimits
import ZilLib.Lower.Composition
import ZilLib.SMT.Run
import ZilLib.SMT.Check

/-!
# Batch 5 Automated Test Suite

Covers:
- APL-40: Policy Equivalence Checking
- APL-46: Rule Repair Hints
- APL-42: Test Generation and Coverage
- APL-43: Stale Views & Causal Revisions
- APL-44: Numeric Limits & Quota Governance
- APL-45: Assume-Guarantee Policy Composition
-/

namespace ZilLib.Test.Batch5

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower.Equivalence
open ZilLib.Repair
open ZilLib.GenTests
open ZilLib.Lower.StaleViews
open ZilLib.Lower.NumericLimits
open ZilLib.Lower.Composition
open ZilLib.SMT

/-- Helper assertion. -/
def assert (cond : Bool) (msg : String) : IO Unit := do
  unless cond do
    throw (IO.userError s!"Assertion failed: {msg}")

/-- Test APL-40 (Equivalence) & APL-46 (Repair Hints). -/
def testEquivalenceAndRepair (tool : Tool) : IO Unit := do
  IO.println "Running testEquivalenceAndRepair..."
  let pA ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/equivalence/01-rbac-direct.zc").toBaseIO with
    | .ok p => pure p
    | .error e => throw e
  let pB_equiv ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/equivalence/02-rbac-indirect.zc").toBaseIO with
    | .ok p => pure p
    | .error e => throw e
  let pB_flawed ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/equivalence/03-rbac-flawed.zc").toBaseIO with
    | .ok p => pure p
    | .error e => throw e

  -- 1. Direct vs Indirect: Equivalent
  let (d1, m1, _) ← match lowerEquivalenceModule pA pB_equiv 3 [] with
    | .ok res => pure res
    | .error e => throw (IO.userError s!"lowering failed: {e}")
  let res1 ← checkBMC m1 m1.invariants.head!.1 5 tool 10000
  match res1.verdict with
  | .noViolationWithinBound _ => pure ()
  | other => throw (IO.userError s!"expected equivalent, got {repr other}")
  IO.println "  PASS 01-rbac-direct and 02-rbac-indirect are equivalent"

  -- 2. Direct vs Flawed: Equivalence violation detected
  let (d2, m2, targets) ← match lowerEquivalenceModule pA pB_flawed 3 [] with
    | .ok res => pure res
    | .error e => throw (IO.userError s!"lowering failed: {e}")
  let res2 ← checkBMC m2 m2.invariants.head!.1 5 tool 10000
  match res2.verdict with
  | .violationFound depth trace =>
      assert (depth <= 3) "expected violation at depth <= 3"
      let terminalState := trace.back?.getD trace.toList.head!
      let diffs := findDivergence d2 m2 terminalState targets
      assert (!diffs.isEmpty) "expected divergence in target relations"

      -- 3. APL-46: Repair hints on divergence
      let div := diffs[0]!
      let report := synthesizeRepairHints pA pB_flawed d2 m2 terminalState div
      assert report.firingInstance.isSome s!"expected firing rule instance, got none for {div.relation}"
      assert (!report.candidatePatches.isEmpty) "expected candidate repair patches"
      IO.println s!"  PASS 01-rbac-direct and 03-rbac-flawed diverge (APL-40) with repair hint (APL-46)"
  | other => throw (IO.userError s!"expected violation, got {repr other}")

/-- Test APL-42 (Test Generation). -/
def testTestGeneration (tool : Tool) : IO Unit := do
  IO.println "Running testTestGeneration..."
  let p ← match ← (ZilLib.loadProgramWith ["libsets/check-vocab"] "examples/equivalence/01-rbac-direct.zc").toBaseIO with
    | .ok program => pure program
    | .error e => throw e

  let report ← generateCoverage p tool 3 4 10000
  assert (report.totalRules == 3) s!"expected 3 rules, got {report.totalRules}"
  assert (report.coveredRules == 3) s!"expected 100% rule coverage (3/3), got {report.coveredRules}"

  let testSuiteCode := renderLeanTestSuite report "examples/equivalence/01-rbac-direct.zc"
  assert (testSuiteCode.contains "def test_rule_role_direct") "missing test_rule_role_direct"
  assert (testSuiteCode.contains "def test_rule_role_inherit") "missing test_rule_role_inherit"
  assert (testSuiteCode.contains "def test_rule_access_perm") "missing test_rule_access_perm"
  IO.println "  PASS test generation achieves 100% rule coverage and emits Lean test suite (APL-42)"

/-- Test APL-43 (Stale Views & Causal Revisions). -/
def testStaleViews (tool : Tool) : IO Unit := do
  IO.println "Running testStaleViews..."
  -- Revisions: r0 adds perm, r1 removes perm, r2 updates user context (depends on r1)
  let a := ("canAccess", "user1", "res1")
  let revs : List RevisionInfo := [
    { id := "r0", dependsOn := [], isAdd := true, atom := a },
    { id := "r1", dependsOn := ["r0"], isAdd := false, atom := a },
    { id := "r2", dependsOn := ["r1"], isAdd := true, atom := ("sessionActive", "user1", "session1") }
  ]

  -- 1. Safe causal replication: no causal reversal
  let safeCfg : StaleViewsConfig := { replicas := ["rep1", "rep2"], revisions := revs, flawedGossip := false }
  let safeMod := lowerStaleViewsModule safeCfg
  let safeRes ← checkBMC safeMod "no_causal_reversal" 4 tool 10000
  match safeRes.verdict with
  | .noViolationWithinBound _ => pure ()
  | other => throw (IO.userError s!"expected safe stale views to pass, got {repr other}")
  IO.println "  PASS safe causal replication preserves monotonicity (no causal reversal)"

  -- 2. Flawed replication (ignores tombstones during lagged gossip): flaw detected
  let flawedCfg : StaleViewsConfig := { replicas := ["rep1", "rep2"], revisions := revs, flawedGossip := true }
  let flawedMod := lowerStaleViewsModule flawedCfg
  let flawedRes ← checkBMC flawedMod "no_causal_reversal" 4 tool 10000
  match flawedRes.verdict with
  | .violationFound _ _ => pure ()
  | other => throw (IO.userError s!"expected flawed stale views to detect violation, got {repr other}")
  IO.println "  PASS flawed replication without tombstones caught by SMT (APL-43)"

/-- Test APL-44 (Numeric Limits & Quotas). -/
def testNumericLimits (tool : Tool) : IO Unit := do
  IO.println "Running testNumericLimits..."
  -- 1. Safe quota governance
  let safeCfg : QuotaConfig := { users := ["u1"], defaultMaxSessions := 2, defaultQuotaLimit := 50 }
  let safeMod := lowerQuotaModule safeCfg
  let safeRes ← checkBMC safeMod "session_within_bounds" 4 tool 10000
  match safeRes.verdict with
  | .noViolationWithinBound _ => pure ()
  | other => throw (IO.userError s!"expected safe quota to pass, got {repr other}")
  IO.println "  PASS safe quota governance preserves bounds"

  -- 2. Flawed login (omits upper bound guard): overflow detected
  let overflowCfg : QuotaConfig := { users := ["u1"], defaultMaxSessions := 2, flawedLogin := true }
  let overflowMod := lowerQuotaModule overflowCfg
  let overflowRes ← checkBMC overflowMod "session_within_bounds" 4 tool 10000
  match overflowRes.verdict with
  | .violationFound depth _ =>
      assert (depth <= 3) "expected quota overflow within depth 3"
  | other => throw (IO.userError s!"expected quota overflow detection, got {repr other}")
  IO.println "  PASS session quota overflow flaw detected (APL-44)"

  -- 3. Flawed logout (omits non-negative check): underflow detected
  let underflowCfg : QuotaConfig := { users := ["u1"], defaultMaxSessions := 2, flawedLogout := true }
  let underflowMod := lowerQuotaModule underflowCfg
  let underflowRes ← checkBMC underflowMod "session_within_bounds" 2 tool 10000
  match underflowRes.verdict with
  | .violationFound depth _ =>
      assert (depth <= 2) "expected quota underflow at depth <= 2"
  | other => throw (IO.userError s!"expected counter underflow detection, got {repr other}")
  IO.println "  PASS counter underflow flaw detected (APL-44)"

/-- Test APL-45 (Assume-Guarantee Policy Composition). -/
def testComposition (tool : Tool) : IO Unit := do
  IO.println "Running testComposition..."
  -- Component 1: AuthN
  -- Inputs: none; Outputs: authenticated; Guarantee: authenticated -> token_valid
  let comp1 : PolicyComponent := {
    interface := {
      name := "AuthN",
      inputVars := [],
      outputVars := ["authenticated"],
      assumption := .constBool true,
      guarantee := .implies (.var "authenticated" false) (.var "token_valid" false)
    },
    localVars := [{ name := "token_valid", sort := .bool }],
    init := .and (.eq (.var "authenticated" false) (.constBool false)) (.eq (.var "token_valid" false) (.constBool true)),
    next := .and
      (.eq (.var "token_valid" true) (.var "token_valid" false))
      (.or (.eq (.var "authenticated" true) (.var "token_valid" false)) (.eq (.var "authenticated" true) (.constBool false)))
  }

  -- Component 2: AuthZ (RBAC)
  -- Inputs: authenticated; Outputs: authorized; Assumption: true; Guarantee: authorized -> authenticated
  let comp2 : PolicyComponent := {
    interface := {
      name := "AuthZ",
      inputVars := ["authenticated"],
      outputVars := ["authorized"],
      assumption := .constBool true,
      guarantee := .implies (.var "authorized" false) (.var "authenticated" false)
    },
    localVars := [],
    init := .eq (.var "authorized" false) (.constBool false),
    next := .eq (.var "authorized" true) (.var "authenticated" true)
  }

  -- 1. Isolated verification of AuthN
  let r1 ← verifyIsolatedComponent comp1 tool 3 10000
  assert r1.passed s!"AuthN isolated verification failed: {r1.detail}"
  IO.println "  PASS AuthN component verified in isolation (<A1> M1 <G1>)"

  -- 2. Isolated verification of AuthZ
  let r2 ← verifyIsolatedComponent comp2 tool 3 10000
  assert r2.passed s!"AuthZ isolated verification failed: {r2.detail}"
  IO.println "  PASS AuthZ component verified in isolation (<A2> M2 <G2>)"

  -- 3. Interface compatibility check
  let compat := checkInterfaceCompatibility comp1 comp2
  assert compat.compatible s!"interfaces should be compatible: {compat.detail}"
  IO.println "  PASS AuthN and AuthZ interfaces are compatible and circular-free"

  -- 4. Composed system verification
  let compMod ← match lowerCompositeModule comp1 comp2 with
    | .ok m => pure m
    | .error e => throw (IO.userError e)
  let compRes ← checkBMC compMod compMod.invariants.head!.1 4 tool 10000
  match compRes.verdict with
  | .noViolationWithinBound _ => pure ()
  | other => throw (IO.userError s!"expected composite guarantee to hold, got {repr other}")
  IO.println "  PASS composed system M1 || M2 establishes G1 and G2 (APL-45)"

/-- Main entry point for Batch 5 tests. -/
def runAllBatch5Tests : IO Unit := do
  IO.println "========================================"
  IO.println "        RUNNING BATCH 5 TEST SUITE      "
  IO.println "========================================"
  let tool ← match ← locateInEnvironment "z3" with
    | .found t => pure t
    | .missing name => throw (IO.userError s!"z3 solver missing: {name}")
    | .broken path detail => throw (IO.userError s!"z3 solver broken at {path}: {detail}")

  testEquivalenceAndRepair tool
  testTestGeneration tool
  testStaleViews tool
  testNumericLimits tool
  testComposition tool
  IO.println "========================================"
  IO.println "    ALL BATCH 5 TESTS PASSED (100%)    "
  IO.println "========================================"

end ZilLib.Test.Batch5

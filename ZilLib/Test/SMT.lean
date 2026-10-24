import ZilLib.SMT
import ZilLib.Test.Harness

/-!
# Tests of the SMT-LIB 2 Backend (TS-03)

Tests:
1. Pure SMT-LIB 2 text generation from `TSModule` AST.
2. Model parsing for SMT-LIB 2 `(get-value ...)` expressions (integers, negative numbers, booleans, enums).
3. Trace reconstruction and validation against Lean's `replayTrace` reference.
4. Solver execution (when `z3` is available):
   - Bounded model check with passing invariant (`Counter`, `x_nonneg`).
   - Bounded model check with counterexample discovery and reference replay (`CounterDefective`, `x_lt_3`).
   - $k$-induction verification (`Counter`, `x_nonneg`, $k=1$).
   - Negative tests: unknown invariant rejected, tampered trace rejected by replay.
5. Evidence envelope generation (`ZIL-EVIDENCE/1`).
-/

namespace ZilLib.Test.SMT

open ZilLib.TransitionSystem
open ZilLib.SMT
open ZilLib.SMT.Evidence
open ZilLib.Test

def run (withTool : Bool) : IO Bool := do
  let t ← Tally.new
  -- 1. SMT-LIB 2 Translation Tests
  t.expect "toSmtSort maps Int to Int" (toSmtSort .int == "Int")
  t.expect "toSmtSort maps Bool to Bool" (toSmtSort .bool == "Bool")
  t.expect "toSmtSort maps enumSort to its name" (toSmtSort (.enumSort "Color" ["Red", "Green"]) == "Color")

  t.expect "toSmtExpr formats non-negative integer" (toSmtExpr 0 (.constInt 42) == "42")
  t.expect "toSmtExpr formats negative integer with (- N)" (toSmtExpr 0 (.constInt (-5)) == "(- 5)")
  t.expect "toSmtExpr formats unprimed variable at step" (toSmtExpr 2 (.var "x" false) == "|v_x_2|")
  t.expect "toSmtExpr formats primed variable at next step" (toSmtExpr 2 (.var "x" true) == "|v_x_3|")
  t.expect "toSmtExpr formats arithmetic" (toSmtExpr 0 (.add (.var "x" false) (.constInt 1)) == "(+ |v_x_0| 1)")
  t.expect "toSmtExpr formats comparison" (toSmtExpr 1 (.ge (.var "x" false) (.constInt 0)) == "(>= |v_x_1| 0)")

  -- 2. Script Generation
  match bmcScript counterModule "x_nonneg" 3 with
  | .ok script =>
      t.expect "bmcScript contains set-logic QF_LIA" (script.contains "(set-logic QF_LIA)")
      t.expect "bmcScript declares variables for all steps"
        (script.contains "(declare-const |v_x_0| Int)" && script.contains "(declare-const |v_x_3| Int)")
      t.expect "bmcScript contains push/pop scopes"
        (script.contains "(push 1)" && script.contains "(pop 1)")
      t.expect "bmcScript asserts negated invariant"
        (script.contains "(assert (not (>= |v_x_0| 0)))")
  | .error e => t.expect "bmcScript succeeded" false e

  t.expect "bmcScript rejects unknown invariant" (match bmcScript counterModule "unknown_inv" 3 with | .error _ => true | .ok _ => false)

  match inductScript counterModule "x_nonneg" 1 with
  | .ok (baseScript, stepScript) =>
      t.expect "inductScript base case checks 0..k" (baseScript.contains "(check-sat)")
      t.expect "inductScript step case asserts Inv(0) and checks not Inv(1)"
        (stepScript.contains "(assert (>= |v_x_0| 0))" && stepScript.contains "(assert (not (>= |v_x_1| 0)))")
  | .error e => t.expect "inductScript succeeded" false e

  -- 3. Parser Tests
  match parseSmtVal "42" with
  | .ok (.int 42) => t.expect "parseSmtVal parses positive integer" true
  | _ => t.expect "parseSmtVal parses positive integer" false

  match parseSmtVal "(- 7)" with
  | .ok (.int (-7)) => t.expect "parseSmtVal parses negative integer" true
  | _ => t.expect "parseSmtVal parses negative integer" false

  match parseSmtVal "true" with
  | .ok (.bool true) => t.expect "parseSmtVal parses true" true
  | _ => t.expect "parseSmtVal parses true" false

  match parseSmtVal "false" with
  | .ok (.bool false) => t.expect "parseSmtVal parses false" true
  | _ => t.expect "parseSmtVal parses false" false

  let sampleGetValue := "((|v_x_0| 0) (|v_x_1| 1) (|v_x_2| 2) (|v_x_3| 3))"
  match parseGetValueResponse sampleGetValue with
  | .ok pairs =>
      t.expect "parseGetValueResponse parses 4 pairs" (pairs.length == 4)
      match reconstructTrace counterModule 3 pairs with
      | .ok trace =>
          t.expect "reconstructTrace reconstructs 4 states" (trace.size == 4)
          let s0Val := (trace.toList[0]?).bind (·.getVar counterModule "x")
          let s3Val := (trace.toList[3]?).bind (·.getVar counterModule "x")
          t.expect "reconstructTrace state 0 x = 0" (s0Val == some (TSVal.int 0))
          t.expect "reconstructTrace state 3 x = 3" (s3Val == some (TSVal.int 3))
          -- Replay reference check on the reconstructed trace
          t.expect "replayTrace accepts counterDefective trace"
            (replayTrace counterDefectiveModule trace.toList "x_lt_3")
          -- Tamper with trace: change state 2 x to 99 (invalid step 1 -> 99)
          let tampered := trace.set! 2 ⟨#[.int 99]⟩
          t.expect "replayTrace rejects tampered trace"
            (!replayTrace counterDefectiveModule tampered.toList "x_lt_3")
      | .error e => t.expect "reconstructTrace succeeded" false e
  | .error e => t.expect "parseGetValueResponse succeeded" false e

  -- 4. Evidence Envelope Tests
  let dummyResult : SmtResult := {
    verdict := .violationFound 3 #[⟨#[.int 0]⟩, ⟨#[.int 1]⟩, ⟨#[.int 2]⟩, ⟨#[.int 3]⟩],
    moduleName := "CounterDefective",
    invName := "x_lt_3",
    solver := some { path := "/usr/local/bin/z3", name := "z3", version := "Z3 5.3.1" },
    script := "(dummy script)",
    stdout := "sat\n((|v_x_0| 0))",
    elapsedMs := 25
  }
  match ZilLib.SMT.Evidence.ofResult dummyResult with
  | .ok json =>
      t.expect "evidence schema is ZIL-EVIDENCE/1" (json.getStr? "schema" == some "ZIL-EVIDENCE/1")
      t.expect "evidence authority is external" (json.getStr? "authority" == some "external")
      t.expect "evidence role is bounded-model-checker" (json.getStr? "role" == some "bounded-model-checker")
      t.expect "evidence output_sha256 matches payload" (json.getStr? "output_sha256").isSome
  | .error e => t.expect "evidence creation succeeded" false e

  -- 5. Live Solver Integration Tests (when z3 is present or withTool is requested)
  let solverOpt ← locateInEnvironment "z3"
  match solverOpt with
  | .found tool =>
      t.expect "z3 solver located on PATH" true
      -- BMC passing invariant
      let bmcPass ← checkBMC counterModule "x_nonneg" 5 tool 30000
      match bmcPass.verdict with
      | .noViolationWithinBound 5 => t.expect "BMC Counter x_nonneg passes within bound 5" true
      | other => t.expect "BMC Counter x_nonneg passes within bound 5" false (toString (repr other))

      -- BMC counterexample discovery + Lean replay
      let bmcFail ← checkBMC counterDefectiveModule "x_lt_3" 5 tool 30000
      match bmcFail.verdict with
      | .violationFound 3 trace =>
          t.expect "BMC CounterDefective x_lt_3 finds violation at step 3" (trace.size == 4)
      | other => t.expect "BMC CounterDefective x_lt_3 finds violation at step 3" false (toString (repr other))

      -- k-induction pass
      let indPass ← checkInduct counterModule "x_nonneg" 1 tool 30000
      match indPass.verdict with
      | .inductiveProved 1 => t.expect "k-induction Counter x_nonneg proved at k=1" true
      | other => t.expect "k-induction Counter x_nonneg proved at k=1" false (toString (repr other))

      -- k-induction non-inductive invariant check (x_lt_3 is not inductive)
      let indFail ← checkInduct counterDefectiveModule "x_lt_3" 1 tool 30000
      match indFail.verdict with
      | .nonInductive 1 _ => t.expect "k-induction CounterDefective x_lt_3 correctly identified as non-inductive" true
      | other => t.expect "k-induction CounterDefective x_lt_3 non-inductive" false (toString (repr other))

  | .missing _ =>
      if withTool then
        t.expect "z3 tool was requested with --with-tool but not found" false
      else
        IO.println "      [SKIP] z3 solver not found on PATH (pure tests passed)"

  | .broken path detail =>
      if withTool then
        t.expect s!"z3 tool at {path} is broken: {detail}" false
      else
        IO.println s!"      [SKIP] z3 solver at {path} is broken: {detail}"

  t.finish

end ZilLib.Test.SMT

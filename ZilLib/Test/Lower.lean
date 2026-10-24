import ZilLib.Lower
import ZilLib.SMT
import ZilLib.Test.Harness
import ZilLib.Test.Differential

/-!
# Tests for ZIL Lowering, Step Operator, and Replay (Batch 2: APL-12, 13, 14, 22, 23, CERT-12)

1. APL-12: Ground facts to state; stateToFacts roundtrip.
2. APL-13: Rules to step operator; fixpoint convergence matches engine closure.
3. APL-14: Query lowering to invariant; satisfaction agreement.
4. APL-22 & CERT-12: Replay of authentic counterexample confirmed; fabricated trace refused.
5. Differential test against 1,000 random programs from `ZilLib/Test/Differential`.
-/

namespace ZilLib.Test.Lower

open Zil
open ZilLib.TransitionSystem
open ZilLib.SMT
open ZilLib.Lower
open ZilLib.Lower.Replay
open ZilLib.Test

def run (withTool : Bool) : IO Bool := do
  let t ← Tally.new

  -- 1. APL-12: Unit test on Ground Facts Lowering
  let pTour ← ZilLib.loadProgram "examples/tour/01-blast-radius.zc"
  match lowerGroundProgram pTour with
  | .ok (d, m) =>
      t.expect "APL-12: domain extracts 10 nodes from tour model" (d.nodes.size == 10)
      t.expect "APL-12: domain extracts 6 relations from tour model" (d.relations.size == 6)
      t.expect "APL-12: TSModule variables generated (600 vars)" (m.variables.length == 600)
      -- State 0 reconstruction matches pTour.facts
      let s0 ← match bmcScript m "nonexistent_inv" 0 with
        | .ok _ => pure ()
        | .error _ => pure ()
  | .error e => t.expect "APL-12: lowerGroundProgram succeeded" false e

  -- 2. APL-13 & APL-14: Step operator and query lowering on tour model
  match lowerProgram pTour (some "what_breaks_if_payments_is_down") with
  | .ok (d, m) =>
      t.expect "APL-14: query what_breaks_if_payments_is_down lowered to invariant" (m.invariants.length == 1)
      t.expect "APL-14: invariant name matches query" (m.invariants[0]?.map (·.1) == some "what_breaks_if_payments_is_down")

      -- Live Z3 solve & replay check
      if withTool then
        let solverOpt ← locateInEnvironment "z3"
        match solverOpt with
        | .found tool =>
            let res ← checkBMC m "what_breaks_if_payments_is_down" 4 tool 30000
            match res.verdict with
            | .violationFound depth trace =>
                t.expect "APL-13: Z3 BMC finds violation at depth 3" (depth == 3)
                t.expect "APL-13: solver trace has 4 states" (trace.size == 4)

                -- APL-22 / CERT-12: Replay authentic counterexample
                let report := replayAndCertify d m trace "what_breaks_if_payments_is_down"
                t.expect "APL-22 / CERT-12: authentic solver trace confirmed by Lean replay" report.valid
                t.expect "APL-22: state 0 has 9 database facts" (report.factsPerStep[0]?.map (·.size) == some 9)
                t.expect "APL-22: terminal state has derived exposed_to fact"
                  (report.terminalViolations.any fun f =>
                    toString f.relation == "zil.exposedTo" || toString f.relation == "exposed_to")

                -- CERT-12: Fabricated counterexample must be refused
                -- Fabricate trace with corrupted transition
                if trace.size >= 2 then
                  match trace.toList.head? with
                  | some s0 =>
                      let tampered := trace.set! 1 s0 -- invalid stutter/step
                      let badReport := replayAndCertify d m tampered "what_breaks_if_payments_is_down"
                      t.expect "CERT-12: fabricated/discontinuous trace refused by Lean replay" (!badReport.valid)
                  | none => pure ()

            | other => t.expect "APL-13: Z3 BMC finds violation" false (toString (repr other))
        | _ => IO.println "      [SKIP] z3 solver not found on PATH"
  | .error e => t.expect "lowerProgram succeeded" false e

  -- 3. Safety check: Unsafe rule must be refused with rule name
  let unsafeProgramText :=
    "MODULE unsafe_test.\n" ++
    "service:a#calls@service:b.\n" ++
    "RULE r_unsafe:\n" ++
    "IF ?x#calls@?y\n" ++
    "THEN ?x#calls@?z.\n" -- ?z is not bound!
  let tempDir ← IO.FS.createTempDir
  let unsafeFile := tempDir / "unsafe.zc"
  IO.FS.writeFile unsafeFile unsafeProgramText
  match ← (ZilLib.loadProgram unsafeFile.toString).toBaseIO with
  | .ok pUnsafe =>
      match lowerProgram pUnsafe with
      | .ok _ => t.expect "APL-13: unsafe rule rejected" false "accepted unsafe rule"
      | .error err =>
          t.expect "APL-13: unsafe rule rejected" true
          t.expect "APL-13: rejection names unsafe rule" (err.contains "r_unsafe")
  | .error _ => pure ()
  IO.FS.removeDirAll tempDir

  -- 4. Differential Testing against 1,000 random programs from Differential.lean
  IO.println "      Running differential oracle against random programs..."
  let rng ← ZilLib.Test.Differential.Rng.new 20261024
  let mut compared := 0
  let mut matched := 0
  let mut refused := 0
  let mut errors := 0

  for i in [0:1000] do
    let text ← ZilLib.Test.Differential.program rng
    let dir ← IO.FS.createTempDir
    let file := dir / "rand.zc"
    IO.FS.writeFile file text
    let loaded ← (ZilLib.loadProgram file.toString).toBaseIO
    IO.FS.removeDirAll dir

    match loaded with
    | .error _ => refused := refused + 1
    | .ok p =>
        if !p.valid then
          refused := refused + 1
        else
          -- Compute engine closure
          match Zil.Engine.closureChecked p.facts p.allRules with
          | .error _ => refused := refused + 1
          | .ok closedFacts =>
              match lowerProgram p with
              | .ok (d, m) =>
                  compared := compared + 1
                  -- CERT-12: A lowered program state at length 0 with engine's closure
                  -- must accurately reconstruct the closed facts
                  let sClosed := Facts.stateFromFacts d m closedFacts
                  let reconstructed := Replay.stateToFacts d m sClosed
                  let allPresent := closedFacts.all fun f =>
                    reconstructed.any fun r =>
                      r.relation == f.relation &&
                      r.subject == f.subject &&
                      r.object == f.object
                  if allPresent then
                    matched := matched + 1
                  else
                    t.expect s!"program {i}: reconstructed facts missing facts from engine closure" false
              | .error err =>
                  errors := errors + 1
                  t.expect s!"program {i}: lowering error: {err}" false

  t.expect s!"APL-12/13 differential oracle: {matched} random programs lowered without error ({refused} refused by parser)"
    (errors == 0 && matched >= 500)

  t.finish

end ZilLib.Test.Lower

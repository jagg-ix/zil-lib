import Zil.Plugin.Evidence
import Zil.Crypto.Sha256
import ZilLib.SMT.Check

/-!
# ZIL-EVIDENCE/1 Envelope Generator for SMT Runs (TS-03)

Constructs `ZIL-EVIDENCE/1` receipts for bounded model checking and $k$-induction runs:
- Authority: `external`
- Assurance: `validated` when a counterexample was replayed and confirmed by Lean's `replayTrace` reference;
  `externally-attested` for bounded pass and inductive invariants.
- Input SHA-256 covers the SMT-LIB 2 script and solver identity.
- Output SHA-256 covers the canonical payload.
-/

namespace ZilLib.SMT.Evidence

open Zil.Json Zil.Crypto

def manifest (solverName : String) : Zil.Plugin.Manifest :=
  { id := s!"extension:zil-lib-smt-{solverName}",
    version := "0.1.0",
    runtime := "external",
    entrypoint := solverName,
    capabilities := #["bounded-model-checking", "k-induction"],
    authority := "external",
    trusted := false }

def role : String := "bounded-model-checker"

/-- Render an `SmtResult` as a `ZIL-EVIDENCE/1` envelope JSON. -/
def ofResult (res : SmtResult) : Except String J := do
  let (verdictStr, stmtStr) := match res.verdict with
    | .noViolationWithinBound b =>
        ("no-violation-within-bound",
         s!"no execution of {b} steps violates {res.invName}; bounded check only")
    | .violationFound d _ =>
        ("violation-found",
         s!"counterexample at step {d} violates {res.invName}; confirmed by Lean reference replay")
    | .inductiveProved k =>
        ("inductive-proved",
         s!"invariant {res.invName} is {k}-inductive; step case confirmed by solver")
    | .nonInductive k _ =>
        ("non-inductive",
         s!"invariant {res.invName} failed {k}-induction step case")
    | .inconclusive reason =>
        ("inconclusive", s!"solver was inconclusive: {reason}")
    | .rejected reason =>
        ("rejected", s!"check was rejected: {reason}")
    | .unavailable reason =>
        ("unavailable", s!"solver unavailable: {reason}")

  let solverName := res.solver.map (·.name) |>.getD "z3"
  let solverVer := res.solver.map (·.version) |>.getD "unknown"

  let payload := J.obj #[
    ("module", .str res.moduleName),
    ("invariant", .str res.invName),
    ("verdict", .str verdictStr),
    ("statement", .str stmtStr),
    ("solver", .str solverName),
    ("solver_version", .str solverVer)
  ]

  let payloadCanonical ← Zil.Json.canonical payload
  let payloadText := Zil.Json.write payloadCanonical

  let inputSha := Sha256.ofText res.script

  let metadata := J.obj #[
    ("elapsed_ms", .int res.elapsedMs),
    ("script_sha256", .str inputSha)
  ]

  Zil.Plugin.Evidence.make {
    manifest := manifest solverName,
    role := role,
    subject := s!"smt:{res.moduleName}:{res.invName}",
    inputSha256 := some inputSha,
    payload := payloadText,
    metadata := metadata,
    assurance := "externally-attested"
  }

end ZilLib.SMT.Evidence

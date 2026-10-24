# Plan: Apalache in the toolkit

Date: 2026-10-23. The target list is `docs/targets.md`; what was measured is `docs/tool-notes.md`. This file orders the work, says
what each stage proves, and where to stop.

## What the spike changed

The first plan assumed that the value of Apalache was a lowering from ZIL. A day of running the tool says something different.

1. **The tool is usable now.** Apalache 0.62.4 runs on a current Java, `check` accepts a typed JSON IR, and a violation writes a trace in
   a documented format. Nothing about installing it, running it or reading it is a risk any more. APL-01 is largely done (the three hand-written
   IR modules it names remain).
2. **It is not a replacement for an explicit-state checker.** On a model with a small state space, an explicit-state checker gives a complete
   answer quickly; Apalache starts a JVM and a solver for every run (3 s for the smallest check).
3. **It wins in two places:** domains an explicit-state checker cannot enumerate (the tool's documentation says so; it is not measured here),
   and *induction* (measured on `LockStep.tla`). A counterexample to induction names the missing conjunct of an invariant in seconds, and
   once the invariant is inductive the proof covers every depth at that domain size.
4. **Most of the benefit needs no ZIL.** `LockStep.tla` is plain TLA+ with type comments. A toolkit that runs the tool, reads
   its traces, and records the result as evidence is useful to any TLA+ model; the ZIL lowering is a second, separate benefit.

So the plan has two tracks that share a runner.

## Tracks

| Track | Input | What it gives | Targets |
|---|---|---|---|
| **A. TLA+ models as they are** | `.tla` with type comments | bounded counterexamples, induction checks with counterexamples to induction, symbolic domains | APL-20, APL-21, APL-24, APL-41 (and the viewer of a trace) |
| **B. ZIL programs** | `.zc` after expansion | the same checks on rules, queries and administrative operations, with every counterexample replayed by the ZIL evaluator | APL-00, APL-05, APL-10 to APL-14, APL-22, APL-30 to APL-33 |

Track A starts first because it pays in days and tests the runner, the trace reader and the evidence record that Track B then reuses.

## Milestones

Each milestone has an exit that can be shown, and a stop rule.

### M0 The tool, pinned (done 2026-10-23)

- Release, checksum and commands recorded: `docs/tool-notes.md`. Trace and IR fixtures: `test/fixtures/apalache/`.
- **Stays:** the tool is found on the machine; nothing is vendored; the gate runs without it.

### M1 Runner and trace reader (APL-20, APL-21)

**Done 2026-10-23.** `ZilLib/Apalache/Run.lean` and `Itf.lean`; tests in `ZilLib/Test/Apalache.lean`; `zilLib apalache check|trace|version`. The gate passes with failing `java` and `apalache-mc` programs because its tests use a stand-in tool. The exit as written below holds, with one change: the "tool unavailable" exit is 3 and a deadline that passed is 4. Running the real tool also showed facts the plan did not have (deadlock, `ExecutionsTooShort`, the output-directory collision): `docs/tool-notes.md`.

- `ZilLib/Apalache/Run.lean`: find the tool (`APALACHE_HOME`, then `PATH`), record `version`, run `check` in a fresh `--out-dir` with a deadline,
  map exit codes (0, 12, 255, timeout, tool missing) to a result type, collect the newest `violation*.itf.json`.
- `ZilLib/Apalache/Itf.lean`: read ITF into a typed trace (sets, tuples, maps, big integers, uninterpreted strings, `params`), print it.
- **Exit:** the two fixtures in `test/fixtures/apalache/` round-trip; a fake `apalache-mc` that exits 12 with a canned trace is read
  correctly; with no tool, the command says *tool unavailable* and exits 3; the gate passes with failing `java` and `apalache-mc` programs.
- **Stop rule:** none; this is small and every later step needs it.

### M2 Evidence (APL-24)

**Done 2026-10-23** for runs on TLA+ (`ZilLib/Apalache/Evidence.lean`). The input digest covers the model and the modules it extends, because there is no IR yet. The tests change each part of the request and compare the digest of the inputs, not only the evidence id: removing the bound from the inputs was a mutation that the first version of the tests did not catch, because the payload also names the bound.

- One `ZIL-EVIDENCE/1` envelope per run: role `bounded-model-checker`, authority `external`, assurance `externally-attested`, the input hash,
  the tool version and command, the bounds (domain sizes, steps), the verdict. A *no violation* result says *within these bounds*. A
  counterexample to induction is a finding, not a failure of the model.
- **Exit:** envelopes validate against the core's evidence checks; changing any bound changes the evidence id; a run that timed out is recorded
  as inconclusive, never as a pass.

### M3 The induction workflow (APL-41), on TLA+ input

**Done 2026-10-23** (`ZilLib/Apalache/Induct.lean`, `zilLib apalache induct`), on an invented model, `test/fixtures/apalache/LockStep.tla`. The exit as written is met there: the invariant is true but not inductive on its own, the counterexample to induction shows the missing conjunct, the strengthened invariant is inductive at the constants that were set, and the injected defect is caught. **The decision point below is still open**: it needs three models other than `LockStep.tla`.

- `induct` takes a model, the invariant, and the assignment form of the type predicate (`IndInit`), runs the base case (`--length=0`) and the
  step (`--length=1`), and prints either *inductive within these bounds* or the counterexample to induction.
- **Exit:** reproduces the measured result in `docs/tool-notes.md`: `Bounded` is not inductive, the counterexample shows the missing
  conjunct, `IndInv` is inductive, and the injected defect is caught by the step check.
- **Decision point (go/no-go for Track A beyond M3):** run it on three models other than `LockStep.tla`. Continue if it finds at least one
  non-inductive invariant whose counterexample is a useful strengthening hint, or checks a domain the explicit-state checker could not finish.
  Stop and keep M1 to M3 as a tool if it does neither.

### M4 Typed IR and lowering of facts (APL-05, APL-10, APL-11, APL-12)

- The check vocabulary in `libsets/` (bounds, invariants, public projections, operations).
- IR types with Snowcat type strings on every node (the tool rejects an untyped IR), writer and reader, a printer to TLA+ text for review.
- **Exit:** twelve hand-written modules round-trip and match their bytes; each type-checks in the tool; a ground program lowers and checks at length 0.
- **Open facts to test here:** whether a hand-written IR may omit `source`; the node kinds sets, tuples, functions and quantifiers use.

### M5 Rules and queries with a differential test (APL-13, APL-14)

- Safe rules (`Zil.Rule.safe`) become one-step operators; stratified negation follows the core's strata; closure is unrolled to a derived depth.
- **Exit:** on the corpus subset and on at least 200 generated programs with domain up to 4, the relations Apalache derives equal the core's
  `Zil.Engine.closure`. Lean is the reference; any difference is a bug in the lowering.
- **Stop rule:** if the unroll depth needed for the corpus exceeds what the tool checks in a minute at domain 3, S1 is limited to the
  non-recursive fragment and the report says so.

### M6 Replay and the strategic targets (APL-22, APL-30, APL-31 to APL-33)

- Replay of a trace in the Lean evaluator (and, for operations, in the operation executor) before it is reported.
- S1, then S2 after the operation language, then S3.
- **Exit:** as in `docs/targets.md`.

## Order and parallelism

```text
M0 done
 ├─ M1 ── M2 ── M3 ── (decision) ── Track A continues: more models, evidence in the consumers' gates
 └─ APL-00 (contract) ── M4 ── M5 ── M6
```

M1 to M3 and APL-00 can run at the same time. M4 waits for APL-00 and for the libsets move to reach the point where the vocabulary has a home
(LIB-03 is done).

## What the numbers say about when to use which tool

| Situation | Use |
|---|---|
| A finite model whose state space finishes in seconds | the explicit-state checker; its answer is complete |
| The same model with a larger domain | Apalache, for a bound; Apalache's induction, for every depth at that size |
| A property that says "for every graph / every set of this size" | Apalache with a symbolic universe |
| A property over two copies of the state (non-interference) | Apalache, with the two-copy product |
| A liveness property | neither of the checks measured here; not covered |

## Risks and what to do about them

| Risk | Likelihood | Handling |
|---|---|---|
| Type annotations are a burden on models with many variables | high for large models | start with models of at most eight variables; annotations are comments, so they cannot change an existing explicit-state result |
| A model uses features the tool lacks (recursion, some library operators, liveness) | medium | the type-check step says so at once; such a model is recorded as *not supported* with the reason, not forced |
| A pass is read as a proof | medium | wording rule in `docs/targets.md`; every report prints its bounds; the evidence record carries them |
| The tool changes its output format | low per release | the version is recorded in every run; fixtures are tool-written; the reader refuses an unknown top-level shape |
| JVM start-up makes many small runs slow | certain | one run per property set, `--inv=A,B,C`; no per-property loops |
| The induction result is trusted for all domain sizes | medium | the report says *at these sizes*; the statement for all sizes needs a proof outside the tool |

## What is not planned

- Liveness checking and the temporal mode, until a model needs one and a spike shows the tool handles it.
- Running the tool in the core's build or default tests.
- A Lean command in the language. Anything the editor shows comes from this repository's own library.

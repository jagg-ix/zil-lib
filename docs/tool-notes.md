# Apalache: what was measured

Facts from running the tool on 2026-10-23, not from its documentation. This is the record that target APL-01 asks for.
Everything here was run on one machine (macOS, x86_64, OpenJDK 26.0.2.1). A claim marked *not tested* has not been.

## The tool

| | |
|---|---|
| Version | 0.62.4 (`apalache-mc version`) |
| Obtained | `apalache-0.62.4.tgz` from the project's release, SHA-256 `b781b53bba32fac14ac2e02b0332e1dc2edc64cb7b850c0608d8142cc7aa2ef4` (equal to the `sha256sum.txt` in the release) |
| Size | 188 MB unpacked (`bin/apalache-mc`, `lib/apalache.jar`) |
| Needs | a Java runtime (ran on OpenJDK 26); no other install |
| Start-up | `version` 1 s; the smallest check 3 s, most of it starting the JVM |
| Not vendored | the repository finds `apalache-mc` on `PATH` or under `APALACHE_HOME`, records its version, and says *tool unavailable* when it is absent |

## Commands used

```text
apalache-mc check     [--init=Init] [--next=Next] [--inv=A,B] [--length=N] [--cinit=ConstInit] [--out-dir=DIR] FILE
apalache-mc typecheck [--output=typed.json] FILE
apalache-mc parse     [--output=ir.json]    FILE
```

`FILE` is a `.tla` file or a **typed** JSON IR.

| Exit code | Meaning (observed) |
|---|---|
| 0 | no error within the bound (`The outcome is: NoError`) |
| 12 | an invariant is violated (`The outcome is: Error`, a trace is written) |
| 255 | the input is wrong: a missing type annotation, a constant that is not assigned |

More cases, observed on 2026-10-23 while building the runner (`ZilLib/Apalache/Run.lean`):

| Case | Exit | `The outcome is:` | Files written |
|---|---|---|---|
| a state without a successor (a deadlock) | 12 | `Deadlock` | `violation.itf.json` and `violation0.itf.json` |
| the same model with `--no-deadlock` and a bound no execution reaches | 0 | `ExecutionsTooShort` | no trace |
| a variable without a type annotation | 255 | none (`type input error: Expected a type annotation for VARIABLE n`) | none |
| an invariant name the model does not define | 255 | none (`Operator Nope not found (used as an invariant)`) | none |
| the model file is inside `--out-dir` | 255 | none | none |

* Exit 12 does not tell a violated invariant from a deadlock; the outcome line does. The deadlock check is on by default
  (`--no-deadlock`, default false). A check that starts from arbitrary states, such as one induction step, must switch it off.
* `ExecutionsTooShort` is a pass whose depth is less than the one requested; the runner reports it as such.
* The tool writes into `<out-dir>/<model file name>/<timestamp>_<id>/`, so a model that sits in the output directory collides with that
  directory name. The runner always uses a new directory that is not the model's.
* The directory names sort as text in time order (`2026-10-23T18-10-10_...`), which is how the runner picks the newest trace.
* `version` prints the bare version, `0.62.4`, on one line.

The code of a timeout of the tool itself and of an out-of-memory run were *not tested*; the runner's own deadline kills the tool and is
reported as `timedOut`.

## The JSON IR (APL-10)

- `parse --output=X.json` writes `{"name": "ApalacheIR", "version": "1.0", "modules": [{"kind": "TlaModule", ...}]}`. Every node has
  `"type": "Untyped"` and a `source` object (`filename`, `from`, `to`).
- `check` accepts a JSON file, but **only a typed one**. The untyped IR gives exit 255 with *Expected a type annotation for VARIABLE n*.
  `typecheck --output=Typed.json` writes the typed IR; `check Typed.json` then gives the same result as `check Counter.tla` (exit 12).
  An emitter must therefore put a Snowcat type string on every declaration and expression.
- Node kinds in the typed IR of a counter: `TlaModule`, `TlaVarDecl`, `TlaOperDecl`, `OperEx` (`oper`, `args`), `NameEx`, `ValEx` with
  `TlaInt`. A fixture is in `test/fixtures/apalache/counter.typed-ir.json`.
- *Not tested*: whether the `source` objects may be left out of an IR that is written by hand; which node kinds sets, tuples,
  functions, `LET` and quantifiers use.

## Traces (APL-21)

A failing run writes `<out-dir>/<spec file name>/<timestamp>_<id>/` with `violation.tla`, `violation.json`, `violation.itf.json`
and one numbered copy per violated invariant (`violation1.*`), plus `MCviolation*.out`, `log0.smt`, `detailed.log`, `run.txt`.
The trace is the Informal Trace Format (ADR-015). Seen in `*.itf.json`:

| Value | Encoding |
|---|---|
| top level | `#meta` (`format`, `varTypes`), `vars`, `states` (each with `#meta.index`), and `params` for constants |
| integer | `{"#bigint": "3"}` (also small ones) |
| boolean, string | plain JSON |
| set | `{"#set": [...]}` |
| tuple | `{"#tup": [...]}` |
| function | `{"#map": [[key, value], ...]}` |
| uninterpreted value | a string, `"a_OF_NODE"` |
| constants | listed under `params`; their values are in state 0 |

Fixtures: `test/fixtures/apalache/*.itf.json`.

## A symbolic universe (APL-30)

```tla
CONSTANT
  \* @type: Set(NODE);
  Nodes
VARIABLE
  \* @type: Set(<<NODE, NODE>>);
  edge
ConstInit == Nodes = {"a_OF_NODE", "b_OF_NODE", "c_OF_NODE"}
Init == edge \in SUBSET (Nodes \X Nodes)
```

- The constant is **assigned** in `ConstInit`; `Cardinality(Nodes) = 3` is rejected (*Nodes' is used before it is assigned*, exit 255).
- Values of an uninterpreted sort are the strings `<name>_OF_<SORT>`.
- Run with `--cinit=ConstInit --length=0`: a false invariant is found in 3 s (exit 12), a true one passes (exit 0). Apalache picks
  `edge` among all 2^9 subsets symbolically.

## An invented model: what it showed

`test/fixtures/apalache/LockStep.tla` has two counters that move together (two variables, two constants, `Max = 5`). `Bounded` (`b <= Max`)
is true in every reachable state but is not inductive; `IndInv` (`Bounded` and `a = b`) is inductive; `CInitFault` makes `b` move by 2.
Times are wall-clock for the whole command, including JVM start. `induct` runs the tool twice, the base case and the step.

| Command | Result | Time |
|---|---|---|
| `check --inv=Bounded --length=5` | no violation (exit 0) | 6 s |
| `check --inv=Bounded --length=5`, `CInitFault` | violation (exit 12) | 5 s |
| `induct`, `WeakInit`, `Bounded` | not inductive: from `a = 0, b = 5` one step reaches `b = 6` | 9 s |
| `induct`, `StrongInit`, `IndInv` | inductive at `Max = 5` | 9 s |
| `induct`, `StrongInit`, `IndInv`, `CInitFault` | the step check fails | 8 s |

Reading it:

- **A bounded check says nothing beyond its length.** Five steps pass. With `--length=8` the tool reports a deadlock (exit 12), because `Next`
  cannot be taken a sixth time.
- **The induction check names the missing conjunct.** The counterexample to induction is a state that satisfies `Bounded` and leaves it after
  one step; it is unreachable, and it shows that the counters must be equal. With that conjunct added, `Init ⇒ IndInv` and
  `IndInv ∧ Next ⇒ IndInv'` both hold, which is a proof for every depth at this value of `Max`.
- **The check can fail.** With the defect switched on, the step check fails (exit 12), as the bounded check does.
- The fixed constants are still a bound. A statement for every value of `Max` needs a proof outside the tool.

## Three invented models: decision point (APL-41, M3)

Three models of different shapes were run through `zilLib apalache induct` and `check` on 2026-10-24 with Apalache 0.62.4:

| Model | Command | Result | Time |
|---|---|---|---|
| `TwoProcLock.tla` | `check --cinit CInit --inv MutualExclusion --length 5` | no violation (exit 0) | 5 s |
| `TwoProcLock.tla` | `induct --cinit CInit --indinit WeakInit --inv MutualExclusion` | not inductive: counterexample shows critical process without lock ownership | 7 s |
| `TwoProcLock.tla` | `induct --cinit CInit --indinit StrongInit --inv IndInv` | inductive at the constants (exit 0) | 7 s |
| `TwoProcLock.tla` | `induct --cinit CInitFault --indinit StrongInit --inv IndInv` | step check fails (exit 1) | 7 s |
| `TokenArbiter.tla` | `check --cinit CInit --inv OneInUse --length 5` | no violation (exit 0) | 5 s |
| `TokenArbiter.tla` | `induct --cinit CInit --indinit WeakInit --inv OneInUse` | not inductive: counterexample shows active process while token is held elsewhere | 7 s |
| `TokenArbiter.tla` | `induct --cinit CInit --indinit StrongInit --inv IndInv` | inductive at the constants (exit 0) | 7 s |
| `TokenArbiter.tla` | `induct --cinit CInitFault --indinit StrongInit --inv IndInv` | step check fails (exit 1) | 7 s |
| `RingBuffer.tla` | `check --cinit CInit --inv EmptyMeansEqual --length 5` | no violation (exit 0) | 5 s |
| `RingBuffer.tla` | `induct --cinit CInit --indinit WeakInit --inv EmptyMeansEqual` | not inductive: counterexample shows mismatched head/tail pointers | 7 s |
| `RingBuffer.tla` | `induct --cinit CInit --indinit StrongInit --inv IndInv` | inductive at the constants (exit 0) | 7 s |
| `RingBuffer.tla` | `induct --cinit CInitFault --indinit StrongInit --inv IndInv` | step check fails (exit 1) | 7 s |

All three models found non-inductive invariants whose counterexamples to induction directly suggested the missing conjuncts needed for an inductive proof. The decision is GO.

## Not covered

- Liveness and temporal properties: not tested; the safety invariants are what this looked at.
- `simulate`, `test`, and the `--temporal` mode: not tested.
- Other Java versions and other operating systems: not tested.

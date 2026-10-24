# Files written by Apalache

Produced on 2026-10-23 by Apalache 0.62.4 (OpenJDK 26.0.2.1). They are the tool's own output, kept so that the trace reader and the IR
tests have real input; they are not edited.

| File | Command | What it is |
|---|---|---|
| `Counter.tla` | written by hand | a counter whose invariant `n < 3` fails at the fourth state |
| `counter.violation.itf.json` | `apalache-mc check --inv=Inv --length=5 Counter.tla` (exit 12) | the trace of the failure in the Informal Trace Format |
| `counter.typed-ir.json` | `apalache-mc typecheck --output=Counter.typed.json Counter.tla` | the typed JSON IR; `check` accepts it and gives the same exit 12 |
| `Sym.tla` | written by hand | all graphs over three uninterpreted nodes, with an antisymmetry invariant that does not hold |
| `sym.violation.itf.json` | `apalache-mc check --cinit=ConstInit --inv=Anti --length=0 Sym.tla` (exit 12) | a trace with a set of tuples, an uninterpreted value (`a_OF_NODE`) and a constant under `params` |
| `LockStep.tla` | written by hand | two counters that move together; `Bounded` is true but not inductive, `IndInv` (with `InStep`) is inductive, and `CInitFault` breaks it |
| `TwoProcLock.tla` | written by hand | two processes and a lock; `MutualExclusion` is true but not inductive, `IndInv` (with `HolderMatches`) is inductive, and `CInitFault` breaks it |
| `TokenArbiter.tla` | written by hand | three processes in a token ring; `OneInUse` is true but not inductive, `IndInv` (with `TokenConsistency`) is inductive, and `CInitFault` breaks it |
| `RingBuffer.tla` | written by hand | circular queue; `EmptyMeansEqual` is true but not inductive, `IndInv` (with `PointerBalance`) is inductive, and `CInitFault` breaks it |
| `Stuck.tla` | written by hand | a counter that cannot step past 2: a deadlock, or `ExecutionsTooShort` with `--no-deadlock` |
| `Untyped.tla` | written by hand | a variable without a type annotation: the tool exits with 255 |
| `fake-home/bin/apalache-mc` | written by hand | a stand-in for the tool, for tests that must not start a JVM; it reads the model's file name (`fake-models/`) and does what the real tool did in that case |
| `broken-home/bin/apalache-mc` | written by hand | an executable that does not report a version (exit 99) |

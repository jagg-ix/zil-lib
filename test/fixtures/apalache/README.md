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

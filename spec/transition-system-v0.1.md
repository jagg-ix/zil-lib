# Transition System Representation & SMT Backend Contract v0.1

This contract specifies the semantic transition-system layer in `zil-lib` (`TSModule` deep embedding and `TransitionSystem` semantic class in Lean 4), the safety fragment, front-end TLA+ ingest via snapshots, solver backends (PySMT and Apalache), the assurance contract, and the unified lowering target for ZIL programs.

It corresponds to target `TS-00` in `docs/targets.md` (Batch S) and establishes the architectural foundation for targets `TS-01` through `TS-05`.

---

## 1. Architectural Principles

1. **Lean is the Semantic Authority:**
   A specification—whether imported from TLA+ source or lowered from a ZIL program—becomes a first-class value in Lean 4. Its formal mathematical meaning is defined by Lean denotation semantics. Safety proofs conducted in Lean are verified by the Lean 4 kernel.
2. **Interchangeable Backends from One Representation:**
   External verification tools (PySMT with SMT solvers, and Apalache with SMT-based symbolic model checking) are independent backends consuming the same semantic model. Neither backend dictates the internal language of the toolkit.
3. **Dual-Layer Representation:**
   Mathematical functions (`State → State → Prop`) cannot be printed for external solvers. Therefore, the architecture cleanly separates a **deep embedding** (`TSModule` AST) read by backends from a **denotational class** (`TransitionSystem`) giving the mathematical meaning in Lean.
4. **Zero External Tools in Core Build:**
   A clean clone of `zil-lib` builds and tests using only `lake` and `git`. No Java runtime, Clojure, Python interpreter, SMT solver, or SANY binary is required by `lake build` or `scripts/test.sh`. External tools are invoked only when `--with-tool` is passed and are gracefully skipped when absent.
5. **Trace Replay Before Reporting:**
   No external solver counterexample is ever accepted on faith. Any counterexample trace returned by PySMT or Apalache must be replayed and confirmed by Lean's reference evaluator before a violation is reported.

---

## 2. Dual-Layer Architecture

```
                  ┌──────────────────────────────┐
                  │    Source Specification      │
                  │   (TLA+ File or ZIL AST)     │
                  └──────────────┬───────────────┘
                                 │
                                 ▼
                  ┌──────────────────────────────┐
                  │    Deep Embedding AST        │
                  │         TSModule             │
                  └──────┬───────────────┬───────┘
                         │               │
            denote       │               │ backends
                         ▼               ▼
      ┌──────────────────────┐   ┌─────────────────────────────┐
      │ TransitionSystem     │   │ Backends:                   │
      │   class in Lean 4    │   │ 1. PySMT (BMC, k-induction) │
      │   State : Type       │   │ 2. SMT-LIB 2 (Z3/cvc5)      │
      │   Init : State → Prop│   │ 3. Apalache (Typed JSON IR) │
      │   Next : State → ... │   └──────────────┬──────────────┘
      └──────────┬───────────┘                  │
                 │                              │ counterexample
                 │                              │ trace
                 ▼                              ▼
      ┌──────────────────────┐   ┌─────────────────────────────┐
      │ Lean Kernel Proofs   │   │ Lean Reference Replay       │
      │ (e.g. induction)     │   │ (confirms or rejects trace) │
      └──────────────────────┘   └─────────────────────────────┘
```

### 2.1 Layer 1: Deep Embedding (`TSModule`)
The deep embedding is a purely syntactic, serializable AST representing a finite or first-order transition system:

```lean
structure TSVar where
  name : String
  sort : TSSort
deriving Inhabited, BEq, Repr

inductive TSSort where
  | bool : TSSort
  | int : TSSort
  | enumSort (name : String) (elements : List String) : TSSort
deriving Inhabited, BEq, Repr

inductive TSExpr where
  | constBool (b : Bool) : TSExpr
  | constInt (i : Int) : TSExpr
  | constEnum (sortName : String) (val : String) : TSExpr
  | var (name : String) (primed : Bool) : TSExpr
  | not (e : TSExpr) : TSExpr
  | and (e1 e2 : TSExpr) : TSExpr
  | or (e1 e2 : TSExpr) : TSExpr
  | implies (e1 e2 : TSExpr) : TSExpr
  | eq (e1 e2 : TSExpr) : TSExpr
  | neq (e1 e2 : TSExpr) : TSExpr
  | lt (e1 e2 : TSExpr) : TSExpr
  | le (e1 e2 : TSExpr) : TSExpr
  | gt (e1 e2 : TSExpr) : TSExpr
  | ge (e1 e2 : TSExpr) : TSExpr
  | add (e1 e2 : TSExpr) : TSExpr
  | sub (e1 e2 : TSExpr) : TSExpr
  | mul (e1 e2 : TSExpr) : TSExpr
  | ite (cond thn els : TSExpr) : TSExpr
deriving Inhabited, BEq, Repr

structure TSModule where
  name : String
  variables : List TSVar
  init : TSExpr
  next : TSExpr
  invariants : List (String × TSExpr)
deriving Inhabited, BEq, Repr
```

Rules for `TSModule`:
- `init` must contain **no primed variables** (`primed = false` for all variable references).
- `next` may contain both unprimed variables ($x$, denoting the current state) and primed variables ($x'$, denoting the next state).
- Invariants in `invariants` must contain **no primed variables**.
- Every variable occurring in `init`, `next`, or `invariants` must be declared in `variables`.

### 2.2 Layer 2: Denotational Class (`TransitionSystem`)
The semantic meaning of a transition system in Lean is given by a type class parameterized by the state representation:

```lean
class TransitionSystem (α : Type) where
  Init : α → Prop
  Next : α → α → Prop

def Reachable [TransitionSystem α] (s : α) : Prop :=
  ∃ (trace : List α), trace ≠ [] ∧
    TransitionSystem.Init trace.head! ∧
    trace.getLast! = s ∧
    (∀ i, (h : i + 1 < trace.length) →
      TransitionSystem.Next (trace.get ⟨i, by omega⟩) (trace.get ⟨i + 1, h⟩))
```

### 2.3 Denotation and Agreement
Each `TSModule` denotes a concrete instance of `TransitionSystem`:

```lean
def TSVal : TSSort → Type
  | .bool => Bool
  | .int => Int
  | .enumSort _ elements => { s : String // s ∈ elements }

def TSState (m : TSModule) : Type :=
  (v : String) → (h : v ∈ m.variables.map (·.name)) → TSVal ...

def denote (m : TSModule) : TransitionSystem (TSState m) := {
  Init := fun s => evalExpr m s (fun _ _ => default) m.init = true
  Next := fun s s' => evalExpr m s s' m.next = true
}
```

**Agreement Theorem (TS-01):**
Evaluating `evalNext m s s'` in the deep embedding evaluates to `true` if and only if `(denote m).Next s s'` holds in Lean. Proofs of safety (`Reachable s → Invariant s`) are conducted in Lean directly against `TransitionSystem`.

---

## 3. Scope: The Safety Fragment and Refusal Policy

### 3.1 Accepted Constructs
The safety fragment consists of discrete transition systems with decidable state transitions:
1. **Sorts:** `Bool`, `Int`, and finite enumerations with listed elements.
2. **Variables:** A finite set of typed state variables.
3. **Initial State:** Predicates over unprimed variables composed of conjunctions, disjunctions, equalities, inequalities, and bounds.
4. **Transition Relation:** First-order formulas over unprimed ($x$) and primed ($x'$) variables:
   - Conjunctions ($\land$) and disjunctions ($\lor$) of individual transition actions.
   - `UNCHANGED <<x, y>>`, expanding to $x' = x \land y' = y$.
   - `[Next]_vars`, expanding to $Next \lor UNCHANGED\ vars$.
   - Deterministic conditionals (`IF c THEN t ELSE e`).
5. **Invariants:** State predicates over unprimed variables ($Inv(s)$) that must hold on all reachable states.

### 3.2 Refused Constructs (Fail-Closed with Location)
Any construct outside the safety fragment is rejected immediately with its exact file, line, and column:
- **Temporal Logic:** Temporal operators ($\Box, \Diamond, \leadsto$), leadsto properties, and LTL/CTL formulas.
- **Fairness:** Weak fairness (`WF_vars(A)`) and strong fairness (`SF_vars(A)`).
- **Unbounded Sets & Quantification:** Unbounded existential ($\exists x: P(x)$) or universal ($\forall x: P(x)$) quantification where the domain is infinite or not a finite enumeration.
- **Non-deterministic Choice:** `CHOOSE` (Hilbert's epsilon).
- **Recursion:** Recursive operator definitions in TLA+ without statically known unrolling depth.
- **Real & Floating-Point Numbers:** Real arithmetic (`Real`), float values, and unbounded sequences.

A refusal is the intended, fail-closed answer when an out-of-scope construct is supplied.

---

## 4. TLA+ Front-End: Ahead-of-Time Snapshots

### 4.1 The No-Java Build Invariant
A core constraint of `zil-lib` is that building the repository or running `scripts/test.sh` must succeed with dummy `java` and `apalache-mc` binaries that exit 99 first on `PATH`. Invoking SANY at Lean elaboration time would violate this invariant.

### 4.2 Snapshot Workflow
1. **Export Command:**
   When a new TLA+ model is added or modified, the user or CLI runs:
   ```bash
   lake exe zilLib tla export Spec.tla
   ```
   This command invokes SANY's XML/JSON exporter and produces `Spec.tla.json`.
2. **Snapshot Envelope:**
   The snapshot contains:
   ```json
   {
     "format": "ZIL-TLA-SNAPSHOT/1",
     "source_file": "Spec.tla",
     "source_sha256": "sha256:...",
     "module": { ... }
   }
   ```
3. **Elaboration Ingestion (`tla_file`):**
   The Lean macro `def mySpec := tla_file "Spec.tla"`:
   - Reads `Spec.tla.json` from the filesystem at elaboration time.
   - Computes the SHA-256 hash of `Spec.tla`.
   - If `Spec.tla.json` is missing or its recorded `source_sha256` does not match `Spec.tla`, elaboration fails with:
     ```
     error: Spec.tla.json is missing or out of date. Run 'zilLib tla export Spec.tla' to refresh.
     ```
   - Elaborates the parsed JSON AST directly into a `TSModule` value.
4. **Pure Lean Quasi-Quotation (Optional, TS-02):**
   An embedded syntax macro `tla%{ ... }` using a native Lean recursive-descent parser for the safety fragment, requiring zero JVM calls even during development.

---

## 5. Solver Backends: PySMT and Apalache

### 5.1 PySMT Backend (TS-03)
From a `TSModule`, the PySMT backend translates the model into:
1. **SMT-LIB 2 Output (`.smt2`):**
   - Declares sorts and state variables for each step $i \in \{0, \dots, k\}$.
   - Asserts initial condition at step 0: $Init(s_0)$.
   - Asserts transition relation for steps $0 \le i < k$: $Next(s_i, s_{i+1})$.
   - Asserts violation of invariant at step $k$: $\neg Inv(s_k)$.
2. **Python PySMT Script (`.py`):**
   - Uses PySMT symbols (`Symbol(f"{var}@{i}", INT)` or `BOOL`).
   - Solves via solver API (`Solver(name="z3")`).
   - Extracts concrete valuations for all state variables at steps $0 \dots k$ if satisfiable.
3. **k-Induction Mode:**
   - **Base case:** Checks reachability of a violation in $0 \dots k$ steps.
   - **Inductive step:** Asserts $Inv(s_0) \land \dots \land Inv(s_{k-1}) \land Next(s_0, s_1) \land \dots \land Next(s_{k-1}, s_k) \land \neg Inv(s_k)$.
   - A counterexample to induction is reported as *candidate invariant is not inductive at depth k*, not as a system fault.

### 5.2 Apalache Backend (TS-04 / APL-10)
From a `TSModule`, the Apalache backend emits:
- Typed JSON IR adhering to ADR-005 and ADR-002 (`ZilLib/Apalache/IR.lean`).
- TLA+ module text adhering to SANY syntax (`ZilLib/Apalache/Print.lean`).

### 5.3 Differential Oracle (TS-04)
On any model (such as `Counter`, `LockStep`, `TwoProcLock`, `TokenArbiter`, `RingBuffer`):
- PySMT and Apalache are executed independently.
- Both must agree on the verdict (no violation within bound $k$, or violation found at step $k$).
- Any discrepancy is flagged as an engine defect with both solver traces retained for review.

---

## 6. Assurance Rules & Witness Replay

1. **Replay Mandatory:**
   A violation reported by an SMT solver (PySMT/Z3) or Apalache is only a *candidate counterexample*. It is never presented to the user until verified by Lean.
2. **Lean Reference Evaluator:**
   The candidate trace $[s_0, s_1, \dots, s_k]$ is supplied to `TS.replayTrace`:
   - Checks that $evalInit(m, s_0) = true$.
   - Checks that for all $i < k$, $evalNext(m, s_i, s_{i+1}) = true$.
   - Checks that $evalInv(m, s_k) = false$.
3. **Classification:**
   - If Lean replay **confirms** the trace: Verdict is `violation-found` with assurance level `externally-attested` (or `validated`).
   - If Lean replay **rejects** the trace: Verdict is `backend-defect` with the invalid transition logged. The external solver's answer is suppressed.
4. **Evidence Envelope:**
   Results are emitted in a `ZIL-EVIDENCE/1` envelope containing the SHA-256 of the `TSModule`, the solver versions, the bounds, and the replay status.

---

## 7. Build and Python Toolchain Policy

1. **Isolation of Python Environment:**
   - PySMT and SMT solver bindings are maintained in a dedicated, isolated virtual environment:
     `$HOME/lab/zil-jade/pysmt-venv`
   - Versions of Python, PySMT, and Z3 bindings are pinned and recorded in `docs/tool-notes.md`.
   - No Python packages are vendored into the git repository.
2. **Test Gate Policy:**
   - Pure tests (AST construction, `denote`, Lean inductive proofs, trace replay on fixtures, SMT-LIB 2 string emission) run unconditionally in `scripts/test.sh`.
   - Tests that execute Python/PySMT or Apalache run only when `--with-tool` is supplied.
   - In the default gate, PATH includes failing shims for `python3`, `java`, `z3`, and `apalache-mc` that exit 99.

---

## 8. Integration with ZIL Lowering (APL-00 Revision)

Target `TS-05` unifies the ZIL lowering with the transition-system layer:
1. **Lowering Target:**
   ZIL lowering (APL-12 to APL-14) compiles a ZIL `Program` into a `TSModule`:
   - Concrete facts $\to Init$.
   - Safe rules (stratified fixpoint unrolling) $\to Next$.
   - Queries that must return empty $\to Invariant$.
2. **APL-00 Clarifications:**
   - **Attribute Records:** In ZIL, relations may have heterogeneous attribute subsets. The lowering normalizes attribute records across a relation by providing default/null values for omitted attributes.
   - **Attribute Pattern Variable Bindings:** While the ZIL core engine binds variables in attribute patterns to nodes, the verified evaluator permits any value. `TSModule` attributes are strictly typed.
   - **Verified Evaluator Specification:** References to "Lean's verified evaluator" refer specifically to `Zil.Datalog.deriveProgramChecked` in `zil-lean` (which carries Lean kernel soundness theorems), distinguishing it from the unverified fast engine (`Zil.Engine.closure`).

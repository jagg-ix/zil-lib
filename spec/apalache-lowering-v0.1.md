# ZIL to Apalache & Transition System Lowering Contract v0.1

**Status:** Drafted, awaiting maintainer acceptance (2026-10-24).

This contract specifies how ZIL (Zil Intermediate Language) programs, queries, and administrative operations are translated into the semantic transition-system layer (`TSModule`, specified in `spec/transition-system-v0.1.md`) and typed TLA+ intermediate representation (ADR-005, ADR-002) for bounded model checking and symbolic analysis with Apalache and SMT-LIB 2 / Z3.

It answers the architectural and semantic questions required before typed IR emission (APL-10), facts lowering (APL-12), and rules lowering (APL-13) are implemented.

## 1. Principles and Boundary

1. **Lean is the reference oracle:** Apalache and SMT solvers are external verification and bug-finding tools. The authoritative ground-truth reference is Lean's verified evaluator `Zil.Datalog.deriveProgramChecked` in `zil-lean` (which carries kernel-level soundness proofs), not the fast unverified engine (`Zil.Engine.closure`). If an external tool reports "no violation within bound" and `deriveProgramChecked` derives a violation on a concrete instance, the lowering or solver is defective. External solver results are classified as `externally-attested`, never `kernel-backed`.
2. **Explicit bounds on every claim:** Every check result is bounded by domain size $N$, unrolling depth $d$, and execution steps $k$. Passing within bound is recorded as *checked within bound*, never *proved*.
3. **Fail-closed execution:** An inconclusive outcome (timeout, out of memory, or tool error) is reported as `inconclusive-timeout` or `tool-error`, never as a pass.
4. **Zero language pollution:** The core ZIL syntax, parsers, and declarations are untouched. All check vocabulary (bounds, operations, invariant queries) is introduced through macro libraries (`libsets/`) expanding to standard ZIL tuples, rules, and queries.
5. **Lowering Target is `TSModule` (TS-05):** The primary target of ZIL lowering is the semantic transition system AST `TSModule` (specified in `spec/transition-system-v0.1.md`). Both Apalache (via typed JSON IR / APL-10) and SMT-LIB 2 / Z3 (TS-03) are backends consuming `TSModule`.

## 2. Sort Scheme

In ZIL, entities are represented as untyped nodes (`service:web`, `user:10`). Apalache requires every variable, constant, and expression to carry an explicit Snowcat type annotation.

### Uninterpreted Node Sort
- All ZIL entity nodes belong to a single uninterpreted sort: `NODE`.
- In Apalache TLA+, the domain of entities is declared as:
  ```tla
  CONSTANT
    \* @type: Set(NODE);
    Nodes
  ```
- Individual elements are represented symbolically as uninterpreted string values following the Apalache uninterpreted literal convention: `"n1_OF_NODE"`, `"n2_OF_NODE"`, etc.
- **Typed Signatures (APL-05 extension):** When relation signatures are declared in check macros (e.g. `USER`, `RESOURCE`), they partition the entity universe into disjoint uninterpreted sorts (`Set(USER)`, `Set(RESOURCE)`). In baseline v0.1 without signatures, the uniform sort `NODE` is used for all subject and object positions.

### Primitive and Attribute Sorts
- **Booleans:** ZIL boolean values (`value:true`, `value:false`) lower to Apalache `Bool`.
- **Integers:** Integer counts and quotas lower to Apalache `Int`.
- **Symbolic Literals & Identifiers:** Relation names, labels, and constant string attributes lower to `Str` or distinct uninterpreted sorts.

## 3. State Variables and Relation Representation

### Per-Relation Set Variables
Relations are represented as individual TLA+ state variables, not as a single heterogeneous set of triples:
- For each relation `r` declared or inferred in the program, a state variable is emitted:
  ```tla
  VARIABLE
    \* @type: Set(<<NODE, NODE>>);
    rel_r
  ```
- If relation `r` carries attributes, its type is emitted as a set of records:
  ```tla
  VARIABLE
    \* @type: Set([sub: NODE, obj: NODE, attr_k1: Int, attr_k2: Str]);
    rel_r
  ```

### Rationale
- **SMT Performance & Indexing:** Per-relation variables isolate SMT constraints per relation. Solvers (Z3 via Apalache) solve independent relation sets significantly faster than a single monolithic universe of `<<sub, rel, obj>>` triples, which requires universal quantification and SMT pattern instantiation over relation discriminators.
- **Strong Static Typing:** Apalache type checking enforces arity and attribute schemas per relation without requiring dynamic union types.

## 4. Lowering of Program Constructs

### 4.1 Ground Facts and Initialization (`Init`)
- For concrete verification, `Init` asserts the exact equality of each relation set to its ground database facts:
  ```tla
  Init ==
    /\ rel_depends_on = {<<"service_web_OF_NODE", "service_db_OF_NODE">>}
    /\ rel_operator = {<<"service_db_OF_NODE", "user_12_OF_NODE">>}
  ```
- For universal bounded checking (APL-30), `ConstInit` fixes the finite domain `Nodes = {"n1_OF_NODE", ..., "nN_OF_NODE"}`, and `Init` chooses an arbitrary initial state satisfying structural preconditions:
  ```tla
  ConstInit == Nodes = {"n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE"}
  Init ==
    /\ rel_depends_on \in SUBSET (Nodes \X Nodes)
    /\ Preconditions
  ```

### 4.2 Positive Rules to Step Operators
Every safe ZIL Datalog rule `head :- p1, p2, ...` lowers to a set comprehension operator computing newly derived tuples:
- Given rule `RULE r: IF ?a#calls@?b AND ?b#calls@?c THEN ?a#depends_on@?c`:
  ```tla
  Delta_r(calls) ==
    { <<a, c>> \in Nodes \X Nodes :
      \E b \in Nodes : <<a, b>> \in calls /\ <<b, c>> \in calls }
  ```
- For a relation `p` with multiple defining rules `r1, ..., rk`, the immediate consequence derivation is:
  ```tla
  Step_p(rel_1, ..., rel_m) ==
    rel_p \cup Delta_r1(...) \cup ... \cup Delta_rk(...)
  ```
- Rule safety (`Zil.Rule.safe`) is strictly enforced: every variable in the head must appear in at least one positive premise. Unsafe rules are rejected with exit code 2 before IR generation.

### 4.3 Stratified Negation
- Negative premises `NOT ?x#r@?y` lower to negated set membership:
  `<<x, y>> \notin rel_r`
- Stratification is verified using the core's stratification engine (`Zil.Engine.stratify`).
- Lowering groups rules by stratum $0 \le s \le S$:
  - Relations in stratum 0 (purely positive base relations) are closed first.
  - In stratum $s$, negative premises refer strictly to relations in strata $< s$, which remain constant (read-only) throughout the closure of stratum $s$.
  - Cyclic negative dependencies are rejected at compile time.

### 4.4 Usersets and Path Rewrites
- Usersets of the form `?s#r@?o#u` (e.g., `tupleToUserset` rewrites) lower to relational composition / existential joins over the intermediate object:
  ```tla
  { <<s, u>> \in Nodes \X Nodes : \E o \in Nodes : <<s, o>> \in rel_r /\ <<o, u>> \in rel_u }
  ```

### 4.5 Attributes, Heterogeneous Schemas, and Pattern Matching

#### 4.5.1 Attribute Representation: Optional Fields with Presence Flags
In ZIL:
- Relations do not enforce rigid record schemas. Different ground facts of the same relation `r` may carry different subsets of attribute keys (e.g., fact 1 has `[k1=1]`, fact 2 has `[k2="alpha"]`, and fact 3 has `[k1=2, k2="beta"]`).
- Rule premises match an arbitrary **subset** of a fact's attributes (`IF ?s#r@?o [k1=1]` matches any fact of `r` with `k1=1`, regardless of whether `k2` is present or absent).

**Chosen Representation:**
For each relation `r`, the lowering inspects the program to collect the union of all attribute keys $K(r) = \{k_1, \dots, k_m\}$ appearing across all facts and rule premises of `r`. In `TSModule` / Apalache, `r` is typed as a set of records with explicit boolean **presence flags**:
```tla
VARIABLE
  \* @type: Set([sub: NODE, obj: NODE, has_k1: Bool, val_k1: Int, has_k2: Bool, val_k2: Str]);
  rel_r
```

**Justification:**
1. **Preserves Fact Identity & Atomicity:** The alternative approach—partitioning a fact into one set per attribute key (`rel_r_sub_obj`, `rel_r_k1`, `rel_r_k2`)—destroys fact atomicity and requires synthetic tuple surrogate keys to join attributes back together. Record embedding preserves the 1-to-1 correspondence with database facts.
2. **Subset Pattern Matching:** A premise matching attribute subset `[k1=v1]` compiles directly to:
   $$\exists rec \in rel\_r : rec.sub = s \land rec.obj = o \land rec.has\_k1 = \text{TRUE} \land rec.val\_k1 = v1$$
   Attribute keys not mentioned in the pattern (e.g. `k2`) are ignored.
3. **Absence Representation:** A fact lacking key $k_i$ is emitted with `has_k_i = FALSE` and a default sentinel value for `val_k_i`.

#### 4.5.2 Variable Bindings in Attributes (`[k=?v]`) and Refusal Policy
In ZIL attribute patterns:
- The fast execution engine (`Zil.Engine`) binds variables in attribute patterns only when the value is a node identifier (`Node`).
- The verified Lean-embedded evaluator (`ZilLib/Certify/Verified.lean`, `literalBehindVariable?`) allows binding to any literal value (e.g. integers, strings).
- **Policy:** The final language design decision on whether attribute variables may bind to non-node literals remains open awaiting maintainer resolution. To guarantee that lowered programs never diverge between the fast engine and the verified reference, the lowering follows a **fail-closed refusal**: any rule or query where `[k=?v]` binds to a non-node literal is refused with an explicit diagnostic (`attribute-variable-non-node-refusal`) until the maintainer decides. Rules binding `?v` to a node (`Node`) are accepted.

## 5. Closure Depth Bound

In Datalog evaluation, recursive derivation proceeds until a fixpoint is reached. In Apalache bounded model checking, recursion is unrolled to a static step bound.

### Herbrand Base Bound
- For a stratum containing relation set $R$ over a universe of $N$ nodes, the Herbrand base size is:
  $$H(R, N) = \sum_{r \in R} N^{\text{arity}(r)}$$
- For standard binary relations, $H(R, N) = |R| \cdot N^2$.
- Because the Datalog consequence operator $T_P$ is monotonic ($T_P(I) \supseteq I$), every iteration before fixpoint must add at least one new tuple. Thus, the fixpoint is guaranteed to be reached within at most $H(R, N)$ derivation steps.
- **Specialized Bounds:**
  - For linear transitive closure over a single relation of size $N$, diameter bound $d = N$ is used.
  - In general, the function `closureDepthBound(program, domainSize)` in Lean computes the exact structural bound based on rule dependency paths.
- **No Arbitrary Constants:** The unrolling depth is derived solely from the domain size $N$ and rule dependency graph; hardcoded limits (such as 64) are prohibited.

## 6. Invariant Language

### Query as Invariant
- In ZIL, an invariant is stated as a query that must return the empty set:
  ```text
  QUERY invariant_name:
  FIND ?x ?y WHERE ?x#bad_relation@?y.
  ```
- Macro `CHECK_INVARIANT(name, query)` binds the query as an invariant to check.
- In Apalache, this lowers to the state predicate asserting that the corresponding derived set is empty:
  ```tla
  Inv_name == rel_bad_relation = {}
  ```
- If the set is non-empty, Apalache reports a violation, and the counterexample trace provides the witness tuples `<<x, y>> \in rel_bad_relation`.

## 7. Counters, Decimals, and Time

1. **Timestamps and Ordering:** Timestamps (`ingest_ts`) and sequence numbers are abstracted away unless explicitly constrained by order rules. When ordering matters, they lower to Apalache `Int` with strict inequality guards.
2. **Decimals:** Arbitrary floating-point and decimal arithmetic is out of scope for v0.1. Decimal attributes evaluated for exact equality lower to symbolic uninterpreted constants. Arithmetic operations on non-integer numeric types are rejected with an explicit diagnostic.
3. **Integer Quotas & Limits:** Integer counters lower directly to Apalache `Int` arithmetic (`+`, `-`, `<=`).

## 8. Failure Modes and Bounded Semantics

- Every Apalache execution is subject to a hard timeout (`--timeout`) managed by the toolkit runner (`ZilLib/Apalache/Run.lean`).
- When Apalache exceeds its deadline or memory budget, the outcome is recorded as:
  - Exit code: `4`
  - Result: `inconclusive-timeout`
  - Verdict: `inconclusive`
- An inconclusive result is NEVER reported as a pass.
- A pass requires exit code `0` (`NoError`) within the specified bound. The evidence envelope records the exact bound `(N, d, k)`.

## 9. Answers to Open Questions from docs/targets.md

### Question 0: Location of the toolkit
- **Decision:** The toolkit lives in the public repository `github.com/jagg-ix/zil-lib`.
- **Reason:** The toolkit is a public developer tool that consumes the pinned core `zil-lean` as a Lake package dependency without polluting the core formal verification base.

### Question 1: Sort Scheme
- **Decision:** Use a single uninterpreted sort `NODE` for all entities in v0.1, with an extension mechanism for multi-sort signatures in APL-05.
- **Reason:** Keeps baseline ZIL programs compatible without requiring upfront type declarations in the source language, while allowing SMT domain partitioning when explicit signatures are provided.

### Question 2: Relations as State and Attribute Schemas
- **Decision:** One set variable per relation (`VARIABLE rel_r`), with attribute records inside the set using boolean presence flags (`has_attr`) and values (`val_attr`).
- **Reason:** Maximizes SMT solver performance by isolating relation constraints. Presence flags allow individual facts of the same relation to have differing subsets of attributes without destroying fact atomicity or requiring synthetic tuple IDs.

### Question 3: Closure Depth Bound
- **Decision:** Computed from the Herbrand base size and rule recursion diameter via `closureDepthBound(program, domainSize)`, never a hardcoded constant.
- **Reason:** A fixed constant (like the engine's former 64-round limit) silently truncates derivations on large models. A derived bound provably attains the fixpoint.

### Question 4: Invariant Language
- **Decision:** Invariants are queries that must return an empty set (`CHECK_INVARIANT`).
- **Reason:** Introduces zero new syntax to the core language. Any query can serve as an invariant, and witness generation is directly supported by the query's answer set.

### Question 5: Counters and Time
- **Decision:** Lower integers to `Int`, treat equality-only decimals/strings as uninterpreted sorts, and ignore timestamps unless explicitly queried.
- **Reason:** Apalache SMT encoding supports integer arithmetic natively. Abstracting irrelevant temporal details prevents unnecessary state space explosion.

### Question 6: Failure Modes
- **Decision:** Enforce hard execution deadlines returning exit code 4 (`inconclusive-timeout`).
- **Reason:** Distinguishes genuine invariant satisfaction from resource exhaustion, preventing false assurances.

### Question 7: Where Lean Wins (Authoritative Reference)
- **Decision:** Lean's kernel-verified evaluator `Zil.Datalog.deriveProgramChecked` in `zil-lean` is the sole ground-truth reference, not the unverified fast engine (`Zil.Engine.closure`).
- **Reason:** External model checkers (Apalache, Z3) rely on complex translations. When an external tool claims satisfaction but `deriveProgramChecked` derives a violation on a concrete instance, the lowering or solver is defective. A `lowering-discrepancy` defect is filed with the full witness trace. External solver evidence is categorized as `externally-attested`, never `kernel-backed`.

### Question 8: Lowering Target and Interchangeable Backends (TS-05)
- **Decision:** ZIL lowering targets the semantic transition-system layer `TSModule` directly.
- **Reason:** Decouples ZIL semantics from Apalache-specific syntax. Both Apalache (via typed JSON IR / APL-10) and SMT-LIB 2 / Z3 (TS-03) consume the identical `TSModule`, enabling direct differential verification between independent backends.

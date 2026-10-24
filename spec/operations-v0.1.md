# Operations and Temporal Governance Specification (v0.1)

**Status:** Accepted for APL-31, APL-32, and APL-33  
**Date:** 2026-10-24  
**Author:** Jorge A. Garcia (`jagg-ix`)  
**Repository:** `zil-lib` (`/spec/operations-v0.1.md`)

---

## 1. Scope and Objective

This specification formalizes administrative operations, parameter binding, guard query evaluation, and trace execution over ZIL programs. It establishes the semantic foundation for:
1. **APL-31 (Operations):** Macro vocabulary extraction and Lean reference executor applying operations to ground fact sets.
2. **APL-32 (Strategic Result S2 - Temporal Governance):** Symbolic lowering of operations into transition system step operators (`Next`), reachability checking, separation of duty, lockout detection, and trace replay.
3. **APL-33 (Strategic Result S3 - Non-Interference):** 2-safety product construction, observation functions, and public projection invariance checking.

---

## 2. Operation Syntax and Macro Representation

Operations are defined in ZIL programs using the check vocabulary extension (`libsets/check-vocab/check-vocab-macros.zc`):

```zil
USE CHECK_OPERATION(op_name, guard_query).
USE CHECK_OPERATION_PARAM(op_name, param_name, param_sort).
USE CHECK_OPERATION_ADD(op_name, subject, relation, object).
USE CHECK_OPERATION_REMOVE(op_name, subject, relation, object).
```

### 2.1 Emitted Relational Tuples
When expanded by the macro compiler, operations produce canonical ZIL ground facts:

1. **Operation Declaration:**
   - `check:op_<op_name>#kind@entity:check_operation.`
   - `check:op_<op_name>#op_name@name:<op_name>.`
   - `check:op_<op_name>#guard_query@query:<guard_query>.` (or `none` if unguarded)

2. **Parameters:**
   - `check:op_param_<op_name>_<param>#kind@entity:check_op_param.`
   - `check:op_param_<op_name>_<param>#operation@name:<op_name>.`
   - `check:op_param_<op_name>_<param>#param@name:<param>.`
   - `check:op_param_<op_name>_<param>#sort@sort:<param_sort>.`

3. **Tuple Additions:**
   - `check:op_add_<...>` with `#operation@name:<op_name>`, `#subject@node:<s>`, `#relation@relation:<r>`, `#object@node:<o>`.

4. **Tuple Removals:**
   - `check:op_rem_<...>` with `#operation@name:<op_name>`, `#subject@node:<s>`, `#relation@relation:<r>`, `#object@node:<o>`.

---

## 3. Abstract Syntax and Semantic Domain

In Lean (`ZilLib.Operation.AST`), an operation is represented as:

```lean
structure Operation where
  name : String
  guardQuery : Option String
  params : List (String × String)            -- (parameter name, sort)
  adds : List (String × String × String)      -- (subject, relation, object)
  removes : List (String × String × String)   -- (subject, relation, object)
```

An invocation represents a concrete execution instance:

```lean
structure OpInvocation where
  opName : String
  bindings : List (String × String)          -- parameter name -> concrete node
```

---

## 4. Operation Execution Semantics

Let $P = \langle \mathcal{F}_0, \mathcal{R}, \mathcal{Q}, \mathcal{O} \rangle$ be a ZIL program consisting of initial base facts $\mathcal{F}_0$, derivation rules $\mathcal{R}$, queries $\mathcal{Q}$, and operations $\mathcal{O}$.

At state $s$, the base database is a finite set of ground facts $\mathcal{F}_s$.

### 4.1 Step Semantics: $\mathcal{F}_s \xrightarrow{op(\vec{v})} \mathcal{F}_{s+1}$

Given an operation $op \in \mathcal{O}$ and parameter bindings $\beta : \text{params}(op) \to \mathcal{U}$:

1. **Parameter Completeness:**
   Every parameter $p \in \text{params}(op)$ must be bound in $\beta$. If any parameter is unbound, execution halts with an error.

2. **Guard Satisfaction:**
   If $op$ specifies a guard query $G \in \mathcal{Q}$:
   - The current base database $\mathcal{F}_s$ is closed under the program rules $\mathcal{R}$:
     $$\mathcal{F}_s^* = \text{Closure}(\mathcal{F}_s, \mathcal{R})$$
   - The query $G$ is evaluated over $\mathcal{F}_s^*$:
     $$\text{Answers} = \text{Solve}(\mathcal{F}_s^*, G)$$
   - If $\text{vars}(G)$ contains variables corresponding to operation parameters, $\text{Answers}$ must contain a solution consistent with $\beta$. If $G$ is propositional or has no parameter variables, $\text{Answers}$ must be non-empty.
   - If no satisfying solution exists, execution halts with a guard violation.

3. **Relational Update:**
   Let $\beta^*(t)$ be the term substitution under bindings $\beta$ (substituting parameters and leaving constants unchanged).
   The updated base facts $\mathcal{F}_{s+1}$ are computed by removing the specified tuples and adding new ones:
   $$\mathcal{F}_{s+1} = \left( \mathcal{F}_s \setminus \{ \langle \beta^*(s), r, \beta^*(o) \rangle \mid (s, r, o) \in \text{removes}(op) \} \right) \cup \{ \langle \beta^*(s), r, \beta^*(o) \rangle \mid (s, r, o) \in \text{adds}(op) \}$$

---

## 5. Transition System Lowering (APL-32)

In the symbolic transition system layer (`TSModule`), the global step relation `Next` is the disjunction of all grounded operation instances:

$$\text{Next}(s, s') \iff \bigvee_{op \in \mathcal{O}} \bigvee_{\vec{v} \in \mathcal{U}^{|\text{params}(op)|}} T_{op, \vec{v}}(s, s')$$

Where $T_{op, \vec{v}}(s, s')$ asserts:
1. The guard formula $\phi_G(s)$ holds under assignment $\vec{v}$.
2. For each added tuple $(s_i, r_i, o_i)$, $r_i(s_i, o_i)' = \text{true}$.
3. For each removed tuple $(s_j, r_j, o_j)$, $r_j(s_j, o_j)' = \text{false}$.
4. Frame axiom: for all other tuples $\langle u, r, w \rangle$ not modified by the operation, $r(u, w)' = r(u, w)$.

---

## 6. Observation Functions and Non-Interference (APL-33)

Non-interference checks hyperproperties (2-safety) across two parallel state trajectories:
$$\mathcal{M} \times \mathcal{M}$$

1. **Public Projection ($\pi_{\text{pub}}$):**
   Defined by `CHECK_PUBLIC` declarations in the program. An observer sees only the relations and queries in $\pi_{\text{pub}}$.
2. **Initial Condition:**
   $$\pi_{\text{pub}}(s_1) = \pi_{\text{pub}}(s_2)$$
3. **Step Condition:**
   Both copies take synchronized steps under the transition relation `Next`.
4. **Invariant:**
   At all reachable steps:
   $$\pi_{\text{pub}}(s_1) = \pi_{\text{pub}}(s_2)$$
   Any divergence constitutes an unauthorized information leak from private relations into public queries.

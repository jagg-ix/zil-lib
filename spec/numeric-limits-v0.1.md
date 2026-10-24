# Numeric Limits and Quota Governance Specification (v0.1)

**Status:** Accepted for APL-44  
**Date:** 2026-10-24  
**Author:** Jorge A. Garcia (`jagg-ix`)  
**Repository:** `zil-lib` (`/spec/numeric-limits-v0.1.md`)

---

## 1. Scope and Objective

Core ZIL relational tuples operate over untyped entity nodes. In practical access governance, authorization decisions frequently depend on numeric counters, concurrency limits, and resource quotas (e.g., maximum active sessions per principal, daily rate limits, storage allocations).

This specification formalizes **APL-44 (Numeric Limits and Quotas)**:
1. **Integer Sort Lowering:** Establishes the contract mapping integer attributes and counter quantities to SMT-LIB 2 mathematical integers (`Int`) with `QF_LIA` (Quantifier-Free Linear Integer Arithmetic).
2. **Arithmetic Guarded Transitions:** Extends operational state transitions with integer linear pre-conditions (`<`, `<=`, `>`, `>=`, `=`) and linear effect assignments (`count' = count + c`, `count' = count - c`).
3. **Quota Safety and Concurrency Invariants:** Formulates and checks invariants:
   $$\forall u \in \mathcal{U}.\; 0 \le \text{active\_sessions}(u) \le \text{max\_sessions}(u)$$
   $$\forall u \in \mathcal{U}.\; 0 \le \text{consumed\_quota}(u) \le \text{allocated\_quota}(u)$$

---

## 2. Number Domain Contract

1. **Sort Scheme:**
   Counter attributes and numeric limits are typed as `Sort.int` in `TSVar`.
   Uninterpreted strings or floating-point decimals remain uninterpreted or are scaled to fixed-point integer basis points.

2. **Arithmetic Operators:**
   Supported transition expressions include:
   - Linear additions and subtractions: `TSExpr.add e1 e2`, `TSExpr.sub e1 e2`.
   - Integer constants: `TSExpr.constInt k` where $k \in \mathbb{Z}$.
   - Linear comparisons: `TSExpr.lt`, `TSExpr.le`, `TSExpr.gt`, `TSExpr.ge`, `TSExpr.eq`.

3. **Frame Axioms for Integer State:**
   Any integer counter not explicitly modified by an enabled operation step is preserved identically across the step:
   $$\text{val}' = \text{val}$$

---

## 3. Quota Governance Model

### 3.1 State Variables
For each principal $u \in \mathcal{U}$:
- `active_sessions_u : Int`
- `max_sessions_u : Int`
- `quota_used_u : Int`
- `quota_limit_u : Int`

### 3.2 Operations
1. `Login(u)`:
   - **Guard:** `active_sessions_u < max_sessions_u`
   - **Effect:** `active_sessions_u' = active_sessions_u + 1`
2. `Logout(u)`:
   - **Guard:** `active_sessions_u > 0`
   - **Effect:** `active_sessions_u' = active_sessions_u - 1`
3. `ConsumeQuota(u, k)`:
   - **Guard:** `quota_used_u + k <= quota_limit_u`
   - **Effect:** `quota_used_u' = quota_used_u + k`

### 3.3 Security Flaws Detectable by SMT
- **Quota Exceeded Flaw:** An operation omitting the bound check in its guard allows `active_sessions_u` to strictly exceed `max_sessions_u`.
- **Underflow Flaw:** An operation allowing logout without checking `active_sessions_u > 0` drives the counter negative, enabling infinite future logins.

Both conditions are verified via bounded model checking and replayed through Lean's arithmetic evaluator.

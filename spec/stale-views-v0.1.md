# Stale Views and Causal Revisions Specification (v0.1)

**Status:** Accepted for APL-43  
**Date:** 2026-10-24  
**Author:** Jorge A. Garcia (`jagg-ix`)  
**Repository:** `zil-lib` (`/spec/stale-views-v0.1.md`)

---

## 1. Scope and Objective

In distributed deployments of policy systems, fact databases are replicated across multiple edge nodes and evaluation points. As network partitions, concurrent writes, and replication lags occur, replicas may evaluate policies against temporally stale views of the relational fact store.

This specification formalizes **APL-43 (Stale Views and Causal Revisions)**:
1. **Revision-Tagged Facts and Causal DAG:** Explicit modeling of revisions $r \in \mathcal{R}$ with causal dependency ordering $\prec$ over a global immutable `RevisionStore`.
2. **Per-Replica Causal Views:** Each replica $k \in \mathcal{K}$ maintains an observed causal frontier $\mathcal{C}_k \subseteq \mathcal{R}$ tracking the versions it has incorporated.
3. **Monotonic Causal Invariant:** Proves that a removal followed by a causal successor addition/mutation is never undone by a stale read (no resurrection of deleted access privileges via lagged gossip).

---

## 2. Formal Model

### 2.1 Revisions and Causal Graph
Let $\mathcal{R} = \{r_0, r_1, r_2, \dots, r_m\}$ be a finite set of revision identifiers.
The causal graph $G = (\mathcal{R}, \prec)$ is a strict partial order (directed acyclic graph) where $r_i \prec r_j$ denotes that revision $r_j$ causally depends on revision $r_i$.

### 2.2 Global Revision Store
The `RevisionStore` is an append-only sequence of fact updates:
$$\text{Mutation} = \langle \text{relation}, \text{subject}, \text{object}, \text{rev}, \text{kind} \rangle$$
where $\text{kind} \in \{\text{Add}, \text{Remove}\}$.

For any relation atom $a = (rel, sub, obj)$, its historical timeline is a path in the causal graph. When a write occurs at revision $r$:
- If $\text{kind} = \text{Add}$, $a$ is asserted as active at $r$.
- If $\text{kind} = \text{Remove}$, a tombstone is recorded at $r$, invalidating prior revisions $r' \prec r$.

### 2.3 Replica Frontier and View Evaluation
Each replica $k \in \mathcal{K}$ has a causal cut (frontier) $\mathcal{C}_k \subseteq \mathcal{R}$.
The visible fact set for replica $k$ is given by:
$$\text{Visible}_k(rel, sub, obj) \iff \exists r \in \mathcal{C}_k.\; \langle rel, sub, obj, r, \text{Add} \rangle \in \text{Store} \land \forall r' \in \mathcal{C}_k.\; (r \prec r' \implies \langle rel, sub, obj, r', \text{Remove} \rangle \notin \text{Store})$$

---

## 3. Operations and State Transitions

The transition system for stale views models three primary discrete actions:

1. **Local Mutation ($\text{Write}$):**
   A replica $k$ executes an update on atom $(rel, sub, obj)$ generating a fresh revision $r_{new}$ with dependencies $\mathcal{C}_k \prec r_{new}$. $\mathcal{C}_k$ advances to include $r_{new}$.

2. **Replication Gossip ($\text{Gossip}_{k_1 \to k_2}$):**
   Replica $k_2$ incorporates causal updates from replica $k_1$. Its frontier becomes $\mathcal{C}_{k_2} \cup \mathcal{C}_{k_1}$.

3. **Read / Policy Evaluation ($\text{Read}_k$):**
   An authorization query evaluates against the local view $\text{Visible}_k$.

---

## 4. Invariant: Absence of Causal Reversal (No Stale Undo)

### 4.1 Specification Invariant
Let $a = (rel, sub, obj)$ be an authorization privilege.
Suppose revision $r_1$ removes privilege $a$, and revision $r_2$ ($r_1 \prec r_2$) represents subsequent policy progression.
The system invariant asserts that **no replica observing causal context $r_2$ can observe privilege $a$ as active**:
$$\forall k \in \mathcal{K}.\; r_2 \in \mathcal{C}_k \implies \neg \text{Visible}_k(a)$$

Furthermore, for any sequence of updates $r_0 \prec r_1 \prec r_2 \dots$, gossip propagation maintains monotonicity: once a replica observes a removal at $r_1$, subsequent synchronization never resurrects $a$ from a lagging gossip path originating before $r_1$.

---

## 5. Transition System Encoding (`TSModule`)

In `ZilLib.Lower.StaleViews`, the system is lowered to boolean and integer state variables:
- `store_add_r_k`: boolean indicating whether revision $r$ added fact $k$.
- `store_rem_r_k`: boolean indicating whether revision $r$ removed fact $k$.
- `replica_seen_i_r`: boolean indicating whether replica $i$ has observed revision $r$ in its frontier.
- `replica_view_i_k`: derived boolean of whether fact $k$ is active in replica $i$'s local state.

Bounded Model Checking verifies that across all interleavings of mutations and gossip steps up to bound $N$ and depth $d$, no causal reversal occurs.

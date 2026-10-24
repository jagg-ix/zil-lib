# Assume-Guarantee Policy Composition Specification (v0.1)

**Status:** Accepted for APL-45  
**Date:** 2026-10-24  
**Author:** Jorge A. Garcia (`jagg-ix`)  
**Repository:** `zil-lib` (`/spec/composition-v0.1.md`)

---

## 1. Scope and Objective

Monolithic verification of global multi-tenant policy graphs across large organizations encounters state space explosion. Modular verification decomposes large policy architectures into decoupled sub-modules verified in isolation through interface contracts.

This specification formalizes **APL-45 (Assume-Guarantee Policy Composition)**:
1. **Component Interface Definitions:** Partitioning state variables into Inputs $V_I$, Outputs $V_O$, and Local state $V_L$, equipped with Environment Assumptions $A$ and Component Guarantees $G$.
2. **Isolated Interface Verification:** Checking that each sub-module $M_i$ satisfies its guarantee $G_i$ under assumption $A_i$ without reference to other module internals ($\langle A_i \rangle M_i \langle G_i \rangle$).
3. **Circular-Free Composition Rule:** Proving that when interfaces mutually satisfy each other's assumptions ($G_1 \implies A_2$ and $G_2 \implies A_1$) without instantaneous circular dependencies, the composite system $M_1 \parallel M_2$ unconditionally establishes $G_1 \land G_2$.

---

## 2. Component Interface Architecture

A policy component interface $\mathcal{I}$ is a 4-tuple:
$$\mathcal{I} = \langle V_I, V_O, A, G \rangle$$
where:
- $V_I$: Input relations provided by the environment or upstream modules (read-only for this module).
- $V_O$: Output relations derived or controlled by this module.
- $A$: Assumption formula constraining valid environment behaviors over $V_I$.
- $G$: Guarantee formula asserted over $V_O \cup V_I$ for every reachable state.

### 2.1 Isolated Component Verification
A component implementation $M = \langle \mathcal{I}, \text{Init}, \text{Next} \rangle$ is valid if:
$$\text{Init} \land A \implies G$$
$$G(s) \land \text{Next}(s, s') \land A(s') \implies G(s')$$

In bounded model checking, this is encoded as checking that the transition system initialized with $A$ and stepping under $\text{Next}$ never violates invariant $G$.

---

## 3. Composition Theorem and Proof Rule

### 3.1 Parallel Composition $M_1 \parallel M_2$
Given components $M_1 = \langle \mathcal{I}_1, \text{Init}_1, \text{Next}_1 \rangle$ and $M_2 = \langle \mathcal{I}_2, \text{Init}_2, \text{Next}_2 \rangle$ such that $V_{O,1} \cap V_{O,2} = \emptyset$:
$$\text{Init}_{1 \parallel 2} = \text{Init}_1 \land \text{Init}_2$$
$$\text{Next}_{1 \parallel 2} = \text{Next}_1 \land \text{Next}_2$$

### 3.2 Proof Rule (Asymmetric and Symmetric)
If:
1. $\langle A_1 \rangle M_1 \langle G_1 \rangle$ holds in isolation.
2. $\langle A_2 \rangle M_2 \langle G_2 \rangle$ holds in isolation.
3. $G_1 \implies A_2$ (Module 1 guarantees fulfill Module 2 assumptions).
4. $G_2 \implies A_1$ (Module 2 guarantees fulfill Module 1 assumptions).
5. Non-circularity: The dependency relation between input and output variables across $M_1$ and $M_2$ is acyclic.

Then:
$$M_1 \parallel M_2 \models G_1 \land G_2$$

---

## 4. Implementation in `ZilLib.Lower.Composition`

The Lean toolkit provides:
- `ComponentInterface`: Data type representing input/output relations, assumptions, and guarantees.
- `verifyComponentIsolated`: Verifies $\langle A \rangle M \langle G \rangle$ using SMT bounded model checking.
- `checkInterfaceCompatibility`: Checks implication $G_1 \implies A_2$ and dependency acyclicity.
- `lowerCompositeModule`: Constructs the unified transition system $M_1 \parallel M_2$ verifying mutual safety.

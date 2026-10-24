---- MODULE LockStep ----
\* Two counters that move together, invented to show an invariant that is true but not inductive.
EXTENDS Integers
CONSTANTS
  \* @type: Int;
  Max,
  \* @type: Bool;
  Fault
VARIABLES
  \* @type: Int;
  a,
  \* @type: Int;
  b
CInit == Max = 5 /\ Fault = FALSE
CInitFault == Max = 5 /\ Fault = TRUE
Init == a = 0 /\ b = 0
Next ==
  /\ a < Max
  /\ a' = a + 1
  /\ b' = IF Fault THEN b + 2 ELSE b + 1
\* True in every reachable state, but not inductive: from a = 0 and b = Max one step reaches b = Max + 1.
Bounded == b <= Max
\* The conjunct that is missing: the counters move together.
InStep == a = b
IndInv == Bounded /\ InStep
\* The states to step from, in assignment form: each variable ranges over its type.
WeakInit == a \in 0..Max /\ b \in 0..Max /\ Bounded
StrongInit == a \in 0..Max /\ b \in 0..Max /\ IndInv
====

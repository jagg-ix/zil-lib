---- MODULE Stuck ----
\* A counter that cannot step past 2: a state without a successor.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  n
Init == n = 0
Next == n < 2 /\ n' = n + 1
Inv == n < 100
====

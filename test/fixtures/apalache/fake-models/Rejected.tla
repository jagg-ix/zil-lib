---- MODULE Rejected ----
EXTENDS Integers
VARIABLE
  \* @type: Int;
  n
Init == n = 0
Next == n' = n + 1
Inv == n < 100
====

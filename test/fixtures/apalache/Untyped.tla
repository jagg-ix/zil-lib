---- MODULE Untyped ----
\* No type annotation on the variable: the tool rejects the model with exit 255.
EXTENDS Integers
VARIABLE n
Init == n = 0
Next == n' = n + 1
Inv == n < 100
====

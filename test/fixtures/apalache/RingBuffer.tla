---- MODULE RingBuffer ----
\* A circular buffer with head, tail, and count, invented to test modular arithmetic on queues.
EXTENDS Integers
CONSTANTS
  \* @type: Int;
  Cap,
  \* @type: Bool;
  Fault
VARIABLES
  \* @type: Int;
  head,
  \* @type: Int;
  tail,
  \* @type: Int;
  count
CInit == Cap = 3 /\ Fault = FALSE
CInitFault == Cap = 3 /\ Fault = TRUE
Init == head = 0 /\ tail = 0 /\ count = 0
Put ==
  /\ count < Cap
  /\ count' = count + 1
  /\ tail' = (tail + IF Fault THEN 2 ELSE 1) % Cap
  /\ head' = head
Get ==
  /\ count > 0
  /\ count' = count - 1
  /\ head' = (head + 1) % Cap
  /\ tail' = tail
Next == Put \/ Get
\* Candidate invariant: an empty buffer implies equal pointers.
\* True in reachable states, but not inductive alone: from count = 1, head = 0, tail = 0,
\* a Get step leads to count' = 0 with head' = 1 /= tail' = 0.
EmptyMeansEqual == (count = 0) => (head = tail)
\* The missing conjunct: pointers and count satisfy modular balance.
PointerBalance ==
  /\ head \in 0..(Cap - 1)
  /\ tail \in 0..(Cap - 1)
  /\ count \in 0..Cap
  /\ (head + count) % Cap = tail
IndInv == EmptyMeansEqual /\ PointerBalance
WeakInit ==
  /\ head \in 0..(Cap - 1)
  /\ tail \in 0..(Cap - 1)
  /\ count \in 0..Cap
  /\ EmptyMeansEqual
StrongInit ==
  /\ head \in 0..(Cap - 1)
  /\ tail \in 0..(Cap - 1)
  /\ count \in 0..Cap
  /\ IndInv
====

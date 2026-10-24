---- MODULE TokenArbiter ----
\* Three processes passing a token in a ring with at most one active, invented to test functions and exclusivity.
EXTENDS Integers
CONSTANTS
  \* @type: Set(Str);
  Procs,
  \* @type: Str -> Str;
  NextProc,
  \* @type: Bool;
  Fault
VARIABLES
  \* @type: Str -> Bool;
  hasToken,
  \* @type: Str -> Bool;
  inUse
CInit ==
  /\ Procs = {"p1", "p2", "p3"}
  /\ NextProc = [p \in {"p1", "p2", "p3"} |-> IF p = "p1" THEN "p2" ELSE IF p = "p2" THEN "p3" ELSE "p1"]
  /\ Fault = FALSE
CInitFault ==
  /\ Procs = {"p1", "p2", "p3"}
  /\ NextProc = [p \in {"p1", "p2", "p3"} |-> IF p = "p1" THEN "p2" ELSE IF p = "p2" THEN "p3" ELSE "p1"]
  /\ Fault = TRUE
Init ==
  /\ hasToken = [p \in Procs |-> IF p = "p1" THEN TRUE ELSE FALSE]
  /\ inUse = [p \in Procs |-> FALSE]
Acquire(p) ==
  /\ (hasToken[p] \/ Fault)
  /\ ~inUse[p]
  /\ inUse' = [inUse EXCEPT ![p] = TRUE]
  /\ hasToken' = hasToken
Release(p) ==
  /\ inUse[p]
  /\ inUse' = [inUse EXCEPT ![p] = FALSE]
  /\ hasToken' = [hasToken EXCEPT ![p] = FALSE, ![NextProc[p]] = TRUE]
Next ==
  \E p \in Procs : Acquire(p) \/ Release(p)
\* Candidate invariant: at most one process is in use. True in all reachable states, but not inductive alone:
\* from inUse["p1"] = TRUE and hasToken["p2"] = TRUE, process p2 acquires and both become in use.
OneInUse ==
  \A p, q \in Procs : (inUse[p] /\ inUse[q]) => p = q
\* The missing conjunct: exactly one token exists, and any in-use process holds it.
TokenConsistency ==
  /\ (\E p \in Procs : hasToken[p] /\ (\A q \in Procs : hasToken[q] => q = p))
  /\ (\A p \in Procs : inUse[p] => hasToken[p])
IndInv == OneInUse /\ TokenConsistency
WeakInit ==
  /\ hasToken \in [Procs -> BOOLEAN]
  /\ inUse \in [Procs -> BOOLEAN]
  /\ OneInUse
StrongInit ==
  /\ hasToken \in [Procs -> BOOLEAN]
  /\ inUse \in [Procs -> BOOLEAN]
  /\ IndInv
====

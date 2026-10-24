---- MODULE TwoProcLock ----
\* Two processes competing for a lock, invented to test inductive invariance on process state and boolean flags.
EXTENDS Integers
CONSTANTS
  \* @type: Set(Str);
  Procs,
  \* @type: Bool;
  Fault
VARIABLES
  \* @type: Str -> Str;
  pc,
  \* @type: Str;
  holder
CInit == Procs = {"p1", "p2"} /\ Fault = FALSE
CInitFault == Procs = {"p1", "p2"} /\ Fault = TRUE
Init ==
  /\ pc = [p \in Procs |-> "idle"]
  /\ holder = "none"
Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ holder' = holder
Acquire(p) ==
  /\ pc[p] = "waiting"
  /\ (holder = "none" \/ Fault)
  /\ holder' = p
  /\ pc' = [pc EXCEPT ![p] = "critical"]
Release(p) ==
  /\ pc[p] = "critical"
  /\ holder = p
  /\ holder' = "none"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
Next ==
  \E p \in Procs : Request(p) \/ Acquire(p) \/ Release(p)
\* Candidate invariant: mutual exclusion. True in reachable states, but not inductive alone:
\* from pc["p1"] = "critical" and holder = "none", p2 can acquire and both become critical.
MutualExclusion ==
  ~ (pc["p1"] = "critical" /\ pc["p2"] = "critical")
\* The missing conjunct: a process in critical section holds the lock.
HolderMatches ==
  /\ \A p \in Procs : pc[p] = "critical" => holder = p
  /\ holder /= "none" => \E p \in Procs : pc[p] = "critical" /\ holder = p
IndInv == MutualExclusion /\ HolderMatches
WeakInit ==
  /\ pc \in [Procs -> {"idle", "waiting", "critical"}]
  /\ holder \in (Procs \cup {"none"})
  /\ MutualExclusion
StrongInit ==
  /\ pc \in [Procs -> {"idle", "waiting", "critical"}]
  /\ holder \in (Procs \cup {"none"})
  /\ IndInv
====

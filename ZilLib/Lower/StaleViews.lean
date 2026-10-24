import Zil.Core.Program
import Zil.Core.Relation
import ZilLib.TransitionSystem
import ZilLib.SMT.Run
import ZilLib.SMT.Check

/-!
# Stale Views and Causal Revisions Transition System (APL-43)

Formalizes distributed causal views and `RevisionStore` semantics where fact updates
are tagged with revisions $r \in \mathcal{R}$ in a causal DAG $G = (\mathcal{R}, \prec)$.

Models:
- Replicas $\mathcal{K}$ tracking causal frontiers $\mathcal{C}_k \subseteq \mathcal{R}$.
- Gossip synchronization advancing causal frontiers monotonically.
- Visibility condition resolving active facts based on causal dominance.
- Invariant: A removal at $r_1$ followed by causal successor $r_2 \succ r_1$ is never
  undone by a stale read on any replica that has observed $r_2$.
-/

namespace ZilLib.Lower.StaleViews

open ZilLib.TransitionSystem

/-- Causal revision record in RevisionStore. -/
structure RevisionInfo where
  id : String
  dependsOn : List String
  isAdd : Bool
  atom : String × String × String   -- (relation, subject, object)
  deriving Inhabited, Repr

/-- Model configuration for stale views verification. -/
structure StaleViewsConfig where
  replicas : List String := ["rep1", "rep2"]
  revisions : List RevisionInfo := []
  flawedGossip : Bool := false
  deriving Inhabited, Repr

/-- Helper to build conjunction of expressions. -/
def mkAndList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool true
  | [e] => e
  | e :: rest => .and e (mkAndList rest)

/-- Helper to build disjunction of expressions. -/
def mkOrList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool false
  | [e] => e
  | e :: rest => .or e (mkOrList rest)

/-- Variable naming helpers. -/
def varSeen (repId revId : String) : String := s!"seen_{repId}_{revId}"
def varVisible (repId : String) (atom : String × String × String) : String :=
  s!"vis_{repId}_{atom.1}_{atom.2.1}_{atom.2.2}"

/-- Lower a multi-replica causal revision system into a self-contained TSModule. -/
def lowerStaleViewsModule (cfg : StaleViewsConfig) : TSModule := Id.run do
  let mut vars : List TSVar := []

  -- 1. State variables: for each replica and each revision, whether replica has seen it
  for rep in cfg.replicas do
    for rev in cfg.revisions do
      vars := { name := varSeen rep rev.id, sort := .bool } :: vars

  -- 2. State variables: visibility of each atom at each replica
  let atoms := cfg.revisions.map (·.atom) |>.eraseDups
  for rep in cfg.replicas do
    for a in atoms do
      vars := { name := varVisible rep a, sort := .bool } :: vars

  -- 3. Initial state: replica 0 has seen root revisions; others start empty or at r0
  let mut initEqs : List TSExpr := []
  for (rep, rIdx) in cfg.replicas.zip (List.range cfg.replicas.length) do
    for rev in cfg.revisions do
      let vName := varSeen rep rev.id
      if rIdx == 0 && rev.dependsOn.isEmpty then
        -- Root revision seen by primary
        initEqs := .eq (.var vName false) (.constBool true) :: initEqs
      else
        initEqs := .eq (.var vName false) (.constBool false) :: initEqs

  -- Initial visibility definition
  for rep in cfg.replicas do
    for a in atoms do
      let vName := varVisible rep a
      initEqs := .eq (.var vName false) (.constBool false) :: initEqs

  let initExpr := mkAndList initEqs.reverse

  -- 4. Next step transitions:
  -- Option A: A replica incorporates a revision whose dependencies it has already seen (local advance)
  -- Option B: Replication gossip where rep2 merges frontier of rep1
  let mut stepTransitions : List TSExpr := []

  -- Local advance transitions
  for rep in cfg.replicas do
    for rev in cfg.revisions do
      -- Guard: replica has seen all dependencies, and hasn't seen rev yet
      let mut depGuards : List TSExpr := [.not (.var (varSeen rep rev.id) false)]
      for depId in rev.dependsOn do
        depGuards := .var (varSeen rep depId) false :: depGuards
      let guard := mkAndList depGuards.reverse

      -- Effect: seen_rep_rev' = true, all other seen unchanged
      let mut effects : List TSExpr := [.eq (.var (varSeen rep rev.id) true) (.constBool true)]
      for otherRep in cfg.replicas do
        for otherRev in cfg.revisions do
          if !(otherRep == rep && otherRev.id == rev.id) then
            let vName := varSeen otherRep otherRev.id
            effects := .eq (.var vName true) (.var vName false) :: effects

      -- Update visibility
      for r in cfg.replicas do
        for a in atoms do
          let visVar := varVisible r a
          -- If this is the replica advancing and affects atom a:
          if r == rep && rev.atom == a then
            if rev.isAdd then
              effects := .eq (.var visVar true) (.constBool true) :: effects
            else
              effects := .eq (.var visVar true) (.constBool false) :: effects
          else
            effects := .eq (.var visVar true) (.var visVar false) :: effects

      stepTransitions := (mkAndList (guard :: effects)) :: stepTransitions

  -- Gossip transitions between replica pairs
  for r1 in cfg.replicas do
    for r2 in cfg.replicas do
      if r1 != r2 then
        -- Gossip from r1 to r2: r2 merges r1's seen revisions
        -- In correct mode: r2 learns all revisions from r1
        -- In flawed mode: r2 might only learn Add revisions and drop tombstones
        let mut gossipEffects : List TSExpr := []
        let mut anyNew := false
        for rev in cfg.revisions do
          let v1 := varSeen r1 rev.id
          let v2 := varSeen r2 rev.id
          if cfg.flawedGossip && !rev.isAdd then
            -- Flawed: ignores tombstones during lagged gossip
            gossipEffects := .eq (.var v2 true) (.var v2 false) :: gossipEffects
          else
            gossipEffects := .eq (.var v2 true) (.or (.var v2 false) (.var v1 false)) :: gossipEffects

        -- Other replicas unchanged
        for otherRep in cfg.replicas do
          if otherRep != r2 then
            for rev in cfg.revisions do
              let v := varSeen otherRep rev.id
              gossipEffects := .eq (.var v true) (.var v false) :: gossipEffects

        -- Visibility sync
        for r in cfg.replicas do
          for a in atoms do
            let visVar := varVisible r a
            if r == r2 then
              -- Find latest seen revision for atom a
              let relRevs := cfg.revisions.filter (·.atom == a)
              if let some latestRev := relRevs.reverse.head? then
                if cfg.flawedGossip && !latestRev.isAdd then
                  -- Flaw resurrects old add
                  gossipEffects := .eq (.var visVar true) (.constBool true) :: gossipEffects
                else
                  let visCond := .and (.var (varSeen r2 latestRev.id) true) (.constBool latestRev.isAdd)
                  gossipEffects := .eq (.var visVar true) visCond :: gossipEffects
              else
                gossipEffects := .eq (.var visVar true) (.var visVar false) :: gossipEffects
            else
              gossipEffects := .eq (.var visVar true) (.var visVar false) :: gossipEffects

        stepTransitions := mkAndList gossipEffects :: stepTransitions

  let nextExpr := mkOrList stepTransitions.reverse

  -- 5. Invariant: No Stale Undo (Causal Monotonicity)
  -- For any revision r_rem removing atom a, and any causal successor r_succ (r_rem \prec r_succ):
  -- seen(rep, r_succ) -> !visible(rep, a)
  let mut invConj : List TSExpr := []
  for rev in cfg.revisions do
    if !rev.isAdd then
      let a := rev.atom
      -- Find all causal successors of rev
      let successors := cfg.revisions.filter (·.dependsOn.contains rev.id)
      for succ in successors do
        for rep in cfg.replicas do
          let seenSucc := TSExpr.var (varSeen rep succ.id) false
          let visAtom := TSExpr.var (varVisible rep a) false
          -- Invariant: seenSucc -> not visAtom
          invConj := .implies seenSucc (.not visAtom) :: invConj

  let invExpr := mkAndList invConj.reverse
  let tag := if cfg.flawedGossip then "Flawed" else "Safe"

  return {
    name := s!"StaleViews_{tag}",
    variables := vars,
    init := initExpr,
    next := nextExpr,
    invariants := [("no_causal_reversal", invExpr)]
  }

end ZilLib.Lower.StaleViews

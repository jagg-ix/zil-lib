import Zil.Core.Program
import Zil.Core.Rule
import Zil.Core.Relation
import Zil.Core.Attribute
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain
import ZilLib.Lower.Facts
import ZilLib.Lower.Rules
import ZilLib.Lower.Replay
import ZilLib.Operation.AST

/-!
# Policy Equivalence Checking Lowering (APL-40)

Lowers two ZIL programs `pA` and `pB` into a single self-contained `TSModule` with a shared
symbolic initial state over base input relations, and dual parallel step operators deriving
`a_rel` and `b_rel`.

The equivalence invariant asserts that for all target relations $R$ (by default, all shared
derived relations) and all node pairs $(u, v) \in \mathcal{U} \times \mathcal{U}$:
  `a_R(u, v) == b_R(u, v)`

If the SMT solver finds a counterexample within unrolling depth $k$, it produces the exact
base topology $F_0$ where the two policy formulations diverge, which is replayed and
confirmed through Lean's transition system reference evaluator.
-/

namespace ZilLib.Lower.Equivalence

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower
open ZilLib.Lower.Rules (allAssignments resolveTerm mkAndList mkOrList)
open ZilLib.Operation (matchRelName)

/-- A target relation pair to compare between Model A and Model B. -/
structure EquivTarget where
  name : String
  relA : String
  relB : String
  deriving Inhabited, Repr

/-- Normalize relation name by stripping identifier guillemets. -/
def cleanRel (name : Name) : String :=
  let s := toString name
  if s.startsWith "«" && s.endsWith "»" then ((s.drop 1).dropEnd 1).toString else s

/-- Prefix a relation name in a Term/Relation if it is derived. -/
def prefixRel (prefixStr : String) (derivedRels : List String) (relName : String) : String :=
  if derivedRels.contains relName then
    prefixStr ++ relName
  else
    relName

/-- Transform a rule so that its conclusion and any derived premises use the given prefix. -/
def renameRuleForEquiv (prefixStr : String) (derivedRels : List String) (r : Rule) : Rule :=
  let cRel := cleanRel r.conclusion.relation
  let newConclusionRel := (prefixStr ++ cRel).toName
  let newConclusion := { r.conclusion with relation := newConclusionRel }

  let newPremises := r.premises.map fun p =>
    let pRel := cleanRel p.relation
    let newRel := prefixRel prefixStr derivedRels pRel |>.toName
    { p with relation := newRel }

  let newNegPremises := r.negativePremises.map fun np =>
    let npRel := cleanRel np.relation
    let newRel := prefixRel prefixStr derivedRels npRel |>.toName
    { np with relation := newRel }

  { r with
    conclusion := newConclusion,
    premises := newPremises,
    negativePremises := newNegPremises }

/-- Information about an observed equivalence divergence. -/
structure EquivDivergence where
  relation : String
  subject : String
  object : String
  valA : Bool
  valB : Bool
  deriving Inhabited, Repr

/-- Lower two programs into a unified transition system checking relational equivalence. -/
def lowerEquivalenceModule
    (pA pB : Program)
    (n : Nat := 3)
    (targetRels : List String := []) :
    Except String (Domain × TSModule × List EquivTarget) := do
  -- 1. Rule safety & stratification check
  for r in pA.allRules do
    unless r.safe do throw s!"Model A contains unsafe rule '{r.name}'"
  for r in pB.allRules do
    unless r.safe do throw s!"Model B contains unsafe rule '{r.name}'"

  match ZilLib.Certify.stratify pA.allRules with
  | .ok _ => pure ()
  | .error err => throw s!"Model A rules are not stratified: {err}"
  match ZilLib.Certify.stratify pB.allRules with
  | .ok _ => pure ()
  | .error err => throw s!"Model B rules are not stratified: {err}"

  -- 2. Identify derived relations for both models
  let derivedA := pA.allRules.map (cleanRel ·.conclusion.relation) |>.toList.eraseDups
  let derivedB := pB.allRules.map (cleanRel ·.conclusion.relation) |>.toList.eraseDups

  -- Target relations to compare
  let targets : List EquivTarget ←
    if !targetRels.isEmpty then
      targetRels.mapM fun t => do
        let optA := derivedA.find? (fun a => matchRelName a t)
        let optB := derivedB.find? (fun b => matchRelName b t)
        match optA, optB with
        | some a, some b => pure { name := t, relA := a, relB := b : EquivTarget }
        | none, _ => throw s!"target relation '{t}' is not a derived relation in Model A (derived: {derivedA})"
        | _, none => throw s!"target relation '{t}' is not a derived relation in Model B (derived: {derivedB})"
    else
      let mut pairs : List EquivTarget := []
      for a in derivedA do
        if let some b := derivedB.find? (fun b => matchRelName a b) then
          pairs := { name := a, relA := a, relB := b } :: pairs
      pure pairs.reverse

  if targets.isEmpty then
    throw "no shared derived relations to compare; specify target relations with --target"

  -- 3. Rename rules
  let renamedRulesA := pA.allRules.map (renameRuleForEquiv "a_" derivedA)
  let renamedRulesB := pB.allRules.map (renameRuleForEquiv "b_" derivedB)
  let allCombinedRules := renamedRulesA ++ renamedRulesB

  -- 4. Construct unified domain
  let extraNodes := (List.range n).map (fun i => s!"node.n{i}")
  -- Collect explicit nodes from both programs
  let mut allNodes : List String := extraNodes
  let collectNodes (p : Program) : List String :=
    let fromFacts := p.facts.toList.flatMap fun f =>
      [nodeNameOfTerm f.subject, nodeNameOfTerm f.object].filterMap id
    let fromRules := p.allRules.toList.flatMap fun r =>
      [nodeNameOfTerm r.conclusion.subject, nodeNameOfTerm r.conclusion.object].filterMap id
    fromFacts ++ fromRules

  allNodes := (allNodes ++ collectNodes pA ++ collectNodes pB).eraseDups
  -- Remove macro metadata nodes if any
  allNodes := allNodes.filter fun s => !s.startsWith "check:" && !s.startsWith "pub_"
  if allNodes.isEmpty then
    allNodes := ["node.n0", "node.n1", "node.n2"]

  -- All relations in the unified system
  let baseRelsA := pA.allRules.toList.flatMap (·.premises.toList.map (cleanRel ·.relation))
    |>.filter (!derivedA.contains ·)
  let baseRelsB := pB.allRules.toList.flatMap (·.premises.toList.map (cleanRel ·.relation))
    |>.filter (!derivedB.contains ·)
  let baseRels := (baseRelsA ++ baseRelsB).eraseDups

  let allDerivedA := derivedA.map ("a_" ++ ·)
  let allDerivedB := derivedB.map ("b_" ++ ·)
  let allRels := (baseRels ++ allDerivedA ++ allDerivedB).eraseDups

  let d : Domain := {
    nodes := allNodes.toArray,
    relations := allRels.toArray,
    attrKeys := #[],
    varToAtom := (allRels.flatMap fun r =>
      allNodes.flatMap fun s =>
        allNodes.map fun o =>
          (baseVarName r s o, { relation := r, subject := s, object := o : AtomVarInfo })
    ).toArray
  }

  let vars := d.toTSVars

  -- 5. Construct shared Init
  let mut initConj : List TSExpr := []

  -- Base relations: if ground facts exist identically in both, fix them; otherwise leave symbolic
  let groundFactsA := pA.facts.filter fun f => baseRels.contains (cleanRel f.relation)
  let groundFactsB := pB.facts.filter fun f => baseRels.contains (cleanRel f.relation)

  for rel in baseRels do
    for sub in d.nodes do
      for obj in d.nodes do
        let bVar := baseVarName rel sub obj
        let inA := groundFactsA.any fun f =>
          cleanRel f.relation == rel && nodeNameOfTerm f.subject == some sub && nodeNameOfTerm f.object == some obj
        let inB := groundFactsB.any fun f =>
          cleanRel f.relation == rel && nodeNameOfTerm f.subject == some sub && nodeNameOfTerm f.object == some obj
        if inA && inB then
          initConj := .eq (.var bVar false) (.constBool true) :: initConj
        else if (!groundFactsA.isEmpty || !groundFactsB.isEmpty) && (!inA && !inB) &&
                (groundFactsA.any (cleanRel ·.relation == rel) || groundFactsB.any (cleanRel ·.relation == rel)) then
          -- Configured base relation has facts: missing facts are false
          initConj := .eq (.var bVar false) (.constBool false) :: initConj
        else
          -- Free symbolic topology
          pure ()

  -- Derived relations in both A and B start empty (false)
  for rel in allDerivedA ++ allDerivedB do
    for sub in d.nodes do
      for obj in d.nodes do
        let bVar := baseVarName rel sub obj
        initConj := .eq (.var bVar false) (.constBool false) :: initConj

  let initExpr := Facts.mkAndList initConj.reverse

  -- 6. Lower Next step operator
  let mut baseNextEqs : List TSExpr := []

  -- Base relations are unchanged
  for rel in baseRels do
    for sub in d.nodes do
      for obj in d.nodes do
        let bVar := baseVarName rel sub obj
        baseNextEqs := .eq (.var bVar true) (.var bVar false) :: baseNextEqs

  -- Derived relations step forward under combined rules
  let derivedNextExpr ← Rules.lowerNext d allCombinedRules
  let nextExpr := Facts.mkAndList (derivedNextExpr :: baseNextEqs)

  -- 7. Construct Invariants for targets
  -- For each target relation R, a_R(u, v) == b_R(u, v)
  let mut invConj : List TSExpr := []
  for target in targets do
    let relA := "a_" ++ target.relA
    let relB := "b_" ++ target.relB
    for sub in d.nodes do
      for obj in d.nodes do
        let vA := baseVarName relA sub obj
        let vB := baseVarName relB sub obj
        -- Equivalence condition: vA == vB
        invConj := .eq (.var vA false) (.var vB false) :: invConj

  let invExpr := Facts.mkAndList invConj.reverse
  let targetNames := targets.map (·.name)
  let targetsJoined := String.intercalate "_" targetNames
  let invariantName := s!"equiv_{targetsJoined}"

  let m : TSModule := {
    name := s!"Equivalence_{targetNames.head?.getD "rel"}_N{n}",
    variables := vars,
    init := initExpr,
    next := nextExpr,
    invariants := [(invariantName, invExpr)]
  }

  return (d, m, targets)

/-- Identify divergence points between Model A and Model B in a counterexample state. -/
def findDivergence (d : Domain) (m : TSModule) (state : TSState) (targets : List EquivTarget) :
    Array EquivDivergence := Id.run do
  let mut diffs : Array EquivDivergence := #[]
  for target in targets do
    let relA := "a_" ++ target.relA
    let relB := "b_" ++ target.relB
    for sub in d.nodes do
      for obj in d.nodes do
        let vA := baseVarName relA sub obj
        let vB := baseVarName relB sub obj
        let valA := TSState.getVar m state vA == some (TSVal.bool true)
        let valB := TSState.getVar m state vB == some (TSVal.bool true)
        if valA != valB then
          diffs := diffs.push {
            relation := target.name,
            subject := sub,
            object := obj,
            valA := valA,
            valB := valB
          }
  return diffs

/-- Extract base input facts present in the initial counterexample state. -/
def extractBaseFacts (d : Domain) (m : TSModule) (s0 : TSState) : Array (String × String × String) := Id.run do
  let mut facts : Array (String × String × String) := #[]
  for (vName, info) in d.varToAtom do
    if !info.relation.startsWith "a_" && !info.relation.startsWith "b_" then
      if TSState.getVar m s0 vName == some (TSVal.bool true) then
        facts := facts.push (info.relation, info.subject, info.object)
  return facts

end ZilLib.Lower.Equivalence

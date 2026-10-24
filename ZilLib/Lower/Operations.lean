import Zil.Core.Program
import Zil.Core.Relation
import Zil.Core.Query
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain
import ZilLib.Lower.Facts
import ZilLib.Lower.Rules
import ZilLib.Lower.Query
import ZilLib.Operation.AST
import ZilLib.Operation.Extract
import ZilLib.Operation.Executor

/-!
# Symbolic Lowering of Operations and Temporal Systems (APL-32, APL-33)

Translates administrative operations into symbolic `TSModule` step transitions (`Next`).
1. Grounding: Each operation is grounded across all parameter combinations in the finite domain.
2. Guard Evaluation: Query guards are lowered to boolean formulas over the current state.
3. State Transitions: Adds set variable to true, removes set variable to false, frame condition
   preserves all other variables.
4. Non-Interference: 2-copy product construction over public projections for hyperproperty checking.
-/

namespace ZilLib.Lower.Operations

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower
open ZilLib.Lower.Rules (allAssignments resolveTerm mkOrList)
open ZilLib.Operation

/-- Conjunction builder to avoid ambiguous imports. -/
def mkAndList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool true
  | [e] => e
  | e :: rest => .and e (mkAndList rest)

/-- Recursively map variable names in a TSExpr. -/
def mapExprVars (f : String → Bool → String × Bool) : TSExpr → TSExpr
  | .var x primed =>
      let (x', primed') := f x primed
      .var x' primed'
  | .not e => .not (mapExprVars f e)
  | .and e1 e2 => .and (mapExprVars f e1) (mapExprVars f e2)
  | .or e1 e2 => .or (mapExprVars f e1) (mapExprVars f e2)
  | .implies e1 e2 => .implies (mapExprVars f e1) (mapExprVars f e2)
  | .eq e1 e2 => .eq (mapExprVars f e1) (mapExprVars f e2)
  | .neq e1 e2 => .neq (mapExprVars f e1) (mapExprVars f e2)
  | .lt e1 e2 => .lt (mapExprVars f e1) (mapExprVars f e2)
  | .le e1 e2 => .le (mapExprVars f e1) (mapExprVars f e2)
  | .gt e1 e2 => .gt (mapExprVars f e1) (mapExprVars f e2)
  | .ge e1 e2 => .ge (mapExprVars f e1) (mapExprVars f e2)
  | .add e1 e2 => .add (mapExprVars f e1) (mapExprVars f e2)
  | .sub e1 e2 => .sub (mapExprVars f e1) (mapExprVars f e2)
  | .mul e1 e2 => .mul (mapExprVars f e1) (mapExprVars f e2)
  | .ite c t e => .ite (mapExprVars f c) (mapExprVars f t) (mapExprVars f e)
  | other => other

/-- Build the guard formula for an operation under a given parameter assignment. -/
def lowerGuard
    (d : Domain)
    (p : Program)
    (op : Operation)
    (assignment : List (String × String)) : TSExpr := Id.run do
  match op.guardQuery with
  | none => return .constBool true
  | some qName =>
      match p.queries.find? (fun q => cleanName (toString q.name) == cleanName qName) with
      | none => return .constBool true
      | some q =>
          -- Find free variables in query that are not in assignment
          let freeVars := q.variables.toList.filter fun v =>
            !assignment.any (fun (pName, _) => cleanName pName == cleanName (toString v))
          let freeVarNames := freeVars.map (cleanName ∘ toString)

          let mut disjuncts : List TSExpr := []
          let qAssignments := allAssignments freeVarNames d.nodes.toList

          for qSubst in qAssignments do
            let fullSubst := assignment ++ qSubst
            let mut conjuncts : List TSExpr := []
            let mut valid := true

            -- Positive premises
            for prem in q.premises do
              let pRel := toString prem.relation
              match resolveTerm prem.subject fullSubst, resolveTerm prem.object fullSubst with
              | some s, some o =>
                  let vName := baseVarName pRel s o
                  conjuncts := .var vName false :: conjuncts
              | _, _ => valid := false

            -- Negative premises
            for nprem in q.negativePremises do
              let npRel := toString nprem.relation
              match resolveTerm nprem.subject fullSubst, resolveTerm nprem.object fullSubst with
              | some s, some o =>
                  let vName := baseVarName npRel s o
                  conjuncts := .not (.var vName false) :: conjuncts
              | _, _ => valid := false

            if valid && !conjuncts.isEmpty then
              disjuncts := mkAndList conjuncts.reverse :: disjuncts

          if disjuncts.isEmpty then
            return .constBool false
          else
            return mkOrList disjuncts.reverse

/-- Lower a single grounded operation transition: Guard ∧ Effects ∧ Frame. -/
def lowerOperationTransition
    (d : Domain)
    (p : Program)
    (op : Operation)
    (assignment : List (String × String)) : TSExpr := Id.run do
  let guardExpr := lowerGuard d p op assignment

  -- Compute grounded additions and removals
  let adds := op.adds.map fun (s, r, o) =>
    (substituteParam assignment s, r, substituteParam assignment o)
  let rems := op.removes.map fun (s, r, o) =>
    (substituteParam assignment s, r, substituteParam assignment o)

  let mut conjuncts : List TSExpr := [guardExpr]

  for rel in d.relations do
    for sub in d.nodes do
      for obj in d.nodes do
        let v := baseVarName rel sub obj
        let isAdd := adds.any fun (asub, arel, aobj) =>
          cleanName asub == cleanName sub && matchRelName arel rel && cleanName aobj == cleanName obj
        let isRem := rems.any fun (rsub, rrel, robj) =>
          cleanName rsub == cleanName sub && matchRelName rrel rel && cleanName robj == cleanName obj

        if isAdd then
          -- Variable becomes true
          conjuncts := .eq (.var v true) (.constBool true) :: conjuncts
        else if isRem then
          -- Variable becomes false
          conjuncts := .eq (.var v true) (.constBool false) :: conjuncts
        else
          -- Frame condition: unchanged
          conjuncts := .eq (.var v true) (.var v false) :: conjuncts

  return mkAndList conjuncts.reverse

/-- Build stutter transition: all relation variables are unchanged. -/
def lowerStutter (d : Domain) : TSExpr := Id.run do
  let mut conjuncts : List TSExpr := []
  for rel in d.relations do
    for sub in d.nodes do
      for obj in d.nodes do
        let v := baseVarName rel sub obj
        conjuncts := .eq (.var v true) (.var v false) :: conjuncts
  return mkAndList conjuncts.reverse

/-- Find candidate ground nodes in domain matching a declared parameter sort. -/
def candidateNodesForSort (p : Program) (d : Domain) (sort : String) : List String :=
  let sortClean := (cleanName sort).toLower
  if sortClean.isEmpty || sortClean == "node" || sortClean == "entity" then
    d.nodes.toList
  else
    let matching := d.nodes.toList.filter fun n =>
      p.facts.any fun f =>
        cleanTermName f.subject == cleanName n &&
        (cleanName (toString f.relation)).toLower == "kind" &&
        (cleanTermName f.object).toLower == sortClean
    if matching.isEmpty then d.nodes.toList else matching

/-- Generate typed parameter assignments restricted to candidates matching parameter sorts. -/
def allTypedAssignments
    (params : List (String × String))
    (candidateFn : String → List String) : List (List (String × String)) :=
  match params with
  | [] => [[]]
  | (pName, pSort) :: rest =>
      let restAssigns := allTypedAssignments rest candidateFn
      let candidates := candidateFn pSort
      candidates.flatMap fun c =>
        restAssigns.map fun s => (cleanName pName, c) :: s

/-- Extract clean domain for operations transition systems, excluding check metadata facts. -/
def operationsDomain (p : Program) (ops : Array Operation) (extraNodes : Array String := #[]) : Domain := Id.run do
  let mut nodesSet : Array String := extraNodes
  let mut relsSet : Array String := #[]

  let addNode (n : String) (set : Array String) : Array String :=
    if set.contains n then set else set.push n

  let addRel (r : String) (set : Array String) : Array String :=
    if set.contains r then set else set.push r

  -- 1. Scan model facts (ignoring check macro metadata)
  for f in p.facts do
    let s := (nodeNameOfTerm f.subject).getD ""
    if !s.startsWith "check." && !s.startsWith "check:" then
      if let some sn := nodeNameOfTerm f.subject then nodesSet := addNode sn nodesSet
      if let some on := nodeNameOfTerm f.object then nodesSet := addNode on nodesSet
      relsSet := addRel (toString f.relation) relsSet

  -- 2. Scan rules
  for r in p.allRules do
    for premise in r.premises ++ r.negativePremises ++ #[r.conclusion] do
      if let some sn := nodeNameOfTerm premise.subject then nodesSet := addNode sn nodesSet
      if let some on := nodeNameOfTerm premise.object then nodesSet := addNode on nodesSet
      relsSet := addRel (toString premise.relation) relsSet

  -- 3. Scan queries
  for q in p.queries do
    for premise in q.premises ++ q.negativePremises do
      if let some sn := nodeNameOfTerm premise.subject then nodesSet := addNode sn nodesSet
      if let some on := nodeNameOfTerm premise.object then nodesSet := addNode on nodesSet
      relsSet := addRel (toString premise.relation) relsSet

  -- 4. Scan operations adds and removes
  for op in ops do
    for (_, r, _) in op.adds ++ op.removes do
      let rMatch := relsSet.find? (fun dr => matchRelName dr r)
      match rMatch with
      | some _ => pure ()
      | none => relsSet := addRel s!"zil.{(cleanName r).toLower}" relsSet

  if nodesSet.isEmpty then nodesSet := #["n:c0"]
  if relsSet.isEmpty then relsSet := #["rel0"]

  let nodes := nodesSet.qsort (· < ·)
  let relations := relsSet.qsort (· < ·)

  return {
    nodes := nodes
    relations := relations
    attrKeys := #[]
    varToAtom := #[]
  }

/-- Lower all operations into the disjunctive step relation Next. -/
def lowerOperationsToNext
    (d : Domain)
    (p : Program)
    (ops : Array Operation) : TSExpr := Id.run do
  let mut transitions : List TSExpr := []

  for op in ops do
    if op.params.isEmpty then
      transitions := lowerOperationTransition d p op [] :: transitions
    else
      let assignments := allTypedAssignments op.params (candidateNodesForSort p d)
      for a in assignments do
        let tr := lowerOperationTransition d p op a
        transitions := tr :: transitions

  -- Always include stutter transition
  transitions := lowerStutter d :: transitions
  return mkOrList transitions.reverse

/-- Lower a ZIL Program with operations into a transition system `TSModule`. -/
def lowerOperationsModule
    (p : Program)
    (extraNodes : Array String := #[])
    (invQueryName : Option String := none) : Except String (TSModule × Domain × Array Operation) := do
  let ops := extractOperations p
  let d := operationsDomain p ops extraNodes

  let modelFacts := p.facts.filter fun f =>
    let s := (nodeNameOfTerm f.subject).getD ""
    !s.startsWith "check." && !s.startsWith "check:"

  -- State variables: one boolean per relation atom
  let mut vars : List TSVar := []
  for rel in d.relations do
    for sub in d.nodes do
      for obj in d.nodes do
        vars := { name := baseVarName rel sub obj, sort := .bool } :: vars

  -- Init: initialized from initial ground model facts
  let initExpr := ZilLib.Lower.Facts.lowerInit d modelFacts

  -- Next: disjunction of grounded operations
  let nextExpr := lowerOperationsToNext d p ops

  -- Invariants:
  let mut invariants : List (String × TSExpr) := []
  if let some qName := invQueryName then
    match p.queries.find? (fun q => cleanName (toString q.name) == cleanName qName) with
    | some q =>
        let (_, invExpr) ← ZilLib.Lower.Query.lowerQuery d q
        invariants := (qName, invExpr) :: invariants
    | none =>
        -- Look for general query
        invariants := invariants

  -- If no specific invariant was supplied, check any declared CHECK_INVARIANT queries
  if invariants.isEmpty then
    let invFacts := p.facts.filter fun f =>
      let c := cleanName (toString f.relation)
      c == "target_query" || c == "targetQuery"
    for f in invFacts do
      let qName := cleanTermName f.object
      if let some q := p.queries.find? (fun q => cleanName (toString q.name) == cleanName qName) then
        let (_, invExpr) ← ZilLib.Lower.Query.lowerQuery d q
        invariants := (qName, invExpr) :: invariants

  let tsMod : TSModule := {
    name := cleanName (p.moduleName.map toString |>.getD "operations_module")
    variables := vars.reverse
    init := initExpr
    next := nextExpr
    invariants := invariants
  }

  return (tsMod, d, ops)

/-- Identify which operation and parameter assignment took state `s` to `s'`. -/
def identifyTransition
    (p : Program)
    (d : Domain)
    (m : TSModule)
    (ops : Array Operation)
    (s s' : TSState) : Option OpInvocation := Id.run do
  -- Check which operation transitions are satisfied by (s, s')
  for op in ops do
    let assignments := if op.params.isEmpty then [[]] else allTypedAssignments op.params (candidateNodesForSort p d)
    for a in assignments do
      let adds := op.adds.map fun (sub, rel, obj) =>
        (substituteParam a sub, rel, substituteParam a obj)
      let rems := op.removes.map fun (sub, rel, obj) =>
        (substituteParam a sub, rel, substituteParam a obj)

      let mut satisfies := true
      let mut changedAny := false

      for (asub, arel, aobj) in adds do
        let dRel := d.relations.find? (fun r => matchRelName r arel) |>.getD arel
        let dSub := d.nodes.find? (fun n => cleanName n == cleanName asub) |>.getD asub
        let dObj := d.nodes.find? (fun n => cleanName n == cleanName aobj) |>.getD aobj
        let v := baseVarName dRel dSub dObj
        if TSState.getVar m s' v != some (TSVal.bool true) then
          satisfies := false
        if TSState.getVar m s v == some (TSVal.bool false) && TSState.getVar m s' v == some (TSVal.bool true) then
          changedAny := true

      for (rsub, rrel, robj) in rems do
        let dRel := d.relations.find? (fun r => matchRelName r rrel) |>.getD rrel
        let dSub := d.nodes.find? (fun n => cleanName n == cleanName rsub) |>.getD rsub
        let dObj := d.nodes.find? (fun n => cleanName n == cleanName robj) |>.getD robj
        let v := baseVarName dRel dSub dObj
        if TSState.getVar m s' v != some (TSVal.bool false) then
          satisfies := false
        if TSState.getVar m s v == some (TSVal.bool true) && TSState.getVar m s' v == some (TSVal.bool false) then
          changedAny := true

      -- Guard query verification in state s
      if let some qName := op.guardQuery then
        if let some q := p.queries.find? (fun q => cleanName (toString q.name) == cleanName qName) then
          for prem in q.premises do
            let pRel := d.relations.find? (fun r => matchRelName r (toString prem.relation)) |>.getD (toString prem.relation)
            match resolveTerm prem.subject a, resolveTerm prem.object a with
            | some subNode, some objNode =>
                let dSub := d.nodes.find? (fun n => cleanName n == cleanName subNode) |>.getD subNode
                let dObj := d.nodes.find? (fun n => cleanName n == cleanName objNode) |>.getD objNode
                let v := baseVarName pRel dSub dObj
                if TSState.getVar m s v != some (TSVal.bool true) then
                  satisfies := false
            | _, _ => pure ()

      if satisfies && changedAny then
        return some { opName := op.name, bindings := a }

  return none

/-- Reconstruct a high-level operation trace from a solver state trace. -/
def reconstructOpTrace
    (p : Program)
    (d : Domain)
    (m : TSModule)
    (ops : Array Operation)
    (trace : Array TSState) : List OpInvocation := Id.run do
  let mut invocations : List OpInvocation := []
  let mut prev : Option TSState := none
  for st in trace do
    if let some prevSt := prev then
      if let some inv := identifyTransition p d m ops prevSt st then
        invocations := invocations.concat inv
    prev := some st
  return invocations

/-- Build a 2-copy self-composition transition system for Non-Interference (APL-33). -/
def lowerNonInterferenceModule
    (p : Program)
    (d : Domain)
    (ops : Array Operation)
    (publicRelations : List String) : TSModule := Id.run do
  let mut vars : List TSVar := []
  for rel in d.relations do
    for sub in d.nodes do
      for obj in d.nodes do
        let base := baseVarName rel sub obj
        vars := { name := "s1_" ++ base, sort := .bool } :: vars
        vars := { name := "s2_" ++ base, sort := .bool } :: vars

  -- Init:
  -- 1. Static model facts (kind / constants) must hold in both copies
  let mut initConjuncts : List TSExpr := []
  for f in p.facts do
    let r := toString f.relation
    let s := (nodeNameOfTerm f.subject).getD ""
    if !s.startsWith "check." && !s.startsWith "check:" then
      if let (some subN, some objN) := (nodeNameOfTerm f.subject, nodeNameOfTerm f.object) then
        let base := baseVarName r subN objN
        initConjuncts := .var ("s1_" ++ base) false :: initConjuncts
        initConjuncts := .var ("s2_" ++ base) false :: initConjuncts

  -- 2. Public relations must agree between s1 and s2
  for rel in d.relations do
    if publicRelations.any (fun pub => matchRelName pub rel) then
      for sub in d.nodes do
        for obj in d.nodes do
          let base := baseVarName rel sub obj
          initConjuncts := .eq (.var ("s1_" ++ base) false) (.var ("s2_" ++ base) false) :: initConjuncts

  let initExpr := mkAndList initConjuncts.reverse

  -- Next: synchronized operation steps across both copies:
  -- When (op, a) is attempted:
  -- In each copy i: (Guard_i ∧ Effects_i) ∨ (¬Guard_i ∧ Stutter_i)
  -- Both copies attempt the same (op, a) concurrently.
  let stutter := lowerStutter d
  let stutter1 := mapExprVars (fun name isPrimed => ("s1_" ++ name, isPrimed)) stutter
  let stutter2 := mapExprVars (fun name isPrimed => ("s2_" ++ name, isPrimed)) stutter
  let syncStutter := TSExpr.and stutter1 stutter2

  let mut syncTransitions : List TSExpr := []

  for op in ops do
    let assignments := if op.params.isEmpty then [[]] else allTypedAssignments op.params (candidateNodesForSort p d)
    for a in assignments do
      let guardExpr := lowerGuard d p op a
      let guard1 := mapExprVars (fun name isPrimed => ("s1_" ++ name, isPrimed)) guardExpr
      let guard2 := mapExprVars (fun name isPrimed => ("s2_" ++ name, isPrimed)) guardExpr

      let opTrans := lowerOperationTransition d p op a
      let trans1 := mapExprVars (fun name isPrimed => ("s1_" ++ name, isPrimed)) opTrans
      let trans2 := mapExprVars (fun name isPrimed => ("s2_" ++ name, isPrimed)) opTrans

      -- Copy 1: takes transition if guard1, else stutters
      let step1 := TSExpr.or trans1 (TSExpr.and (.not guard1) stutter1)
      -- Copy 2: takes transition if guard2, else stutters
      let step2 := TSExpr.or trans2 (TSExpr.and (.not guard2) stutter2)

      syncTransitions := TSExpr.and step1 step2 :: syncTransitions

  syncTransitions := syncStutter :: syncTransitions
  let nextExpr := mkOrList syncTransitions.reverse

  -- Invariant: at all steps, public relations must remain equal
  let mut invConjuncts : List TSExpr := []
  for rel in d.relations do
    if publicRelations.any (fun pub => matchRelName pub rel) then
      for sub in d.nodes do
        for obj in d.nodes do
          let base := baseVarName rel sub obj
          invConjuncts := .eq (.var ("s1_" ++ base) false) (.var ("s2_" ++ base) false) :: invConjuncts

  let invExpr := mkAndList invConjuncts.reverse
  let invariants := [("public_non_interference", invExpr)]

  return {
    name := cleanName (p.moduleName.map toString |>.getD "non_interference_module")
    variables := vars.reverse
    init := initExpr
    next := nextExpr
    invariants := invariants
  }

end ZilLib.Lower.Operations

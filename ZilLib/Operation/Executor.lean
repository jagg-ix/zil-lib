import Zil.Core.Program
import Zil.Core.Relation
import Zil.Core.Query
import Zil.Engine.Query
import Zil.Engine.Provenance
import Zil.Parser.Tuple
import ZilLib.Operation.AST

/-!
# Lean Reference Operation Executor (APL-31)

Executes administrative operations against ground fact databases:
1. Validates that all declared parameters have concrete bindings.
2. Evaluates the guard query against the stratified Datalog closure of the fact base.
3. Applies parameter substitutions and executes atomic tuple removals and additions.
4. Chains sequential operations into executable traces for temporal property verification.
-/

namespace ZilLib.Operation

open Zil

/-- Check whether a Datalog solution matches the given parameter bindings. -/
def solutionMatchesBindings (sol : Array (Name × Term)) (bindings : List (String × String)) : Bool :=
  sol.all fun (vName, term) =>
    let vClean := cleanName (toString vName)
    match bindings.find? (fun (bName, _) => cleanName bName == vClean) with
    | some (_, boundVal) => cleanTermName term == cleanName boundVal
    | none => true

/-- Substitute bound parameters in a tuple component. -/
def substituteParam (bindings : List (String × String)) (termStr : String) : String :=
  match bindings.find? (fun (bName, _) => cleanName bName == cleanName termStr) with
  | some (_, boundVal) => boundVal
  | none => termStr

/-- Apply an operation with concrete bindings to a set of ground facts. -/
def executeOperation
    (p : Program)
    (op : Operation)
    (inv : OpInvocation)
    (facts : Array RelExpr) : Except String (Array RelExpr) := do
  -- 1. Verify parameter completeness
  for (pName, _) in op.params do
    if !inv.bindings.any (fun (bName, _) => cleanName bName == cleanName pName) then
      throw s!"Operation '{op.name}': missing binding for parameter '{pName}'"

  -- 2. Evaluate guard query if specified
  if let some qName := op.guardQuery then
    match p.queries.find? (fun q => cleanName (toString q.name) == cleanName qName) with
    | none => throw s!"Operation '{op.name}': guard query '{qName}' not found in program"
    | some q =>
        -- Compute Datalog closure under program rules
        let closedFacts ← match Zil.Engine.closureChecked facts p.allRules with
          | .ok cf => pure cf
          | .error err => throw s!"Datalog closure failed during guard check: {err}"

        let solutions := Zil.Engine.solve closedFacts q
        if solutions.isEmpty then
          throw s!"Operation '{op.name}': guard query '{qName}' produced 0 solutions (not satisfied)"

        let anyMatch := solutions.any fun sol => solutionMatchesBindings sol inv.bindings
        if !anyMatch then
          throw s!"Operation '{op.name}': guard query '{qName}' has no solution matching bindings {repr inv.bindings}"

  -- 3. Execute removals
  let mut currentFacts := facts
  for (s, r, o) in op.removes do
    let subStr := substituteParam inv.bindings s
    let objStr := substituteParam inv.bindings o
    currentFacts := currentFacts.filter fun f =>
      !(cleanTermName f.subject == cleanName subStr &&
        matchRelName (toString f.relation) r &&
        cleanTermName f.object == cleanName objStr)

  -- 4. Execute additions
  for (s, r, o) in op.adds do
    let subStr := substituteParam inv.bindings s
    let objStr := substituteParam inv.bindings o
    let existsAlready := currentFacts.any fun f =>
      cleanTermName f.subject == cleanName subStr &&
      matchRelName (toString f.relation) r &&
      cleanTermName f.object == cleanName objStr

    if !existsAlready then
      let subTerm := match Zil.Parser.termFromToken subStr with
        | .ok t => t
        | .error _ => Term.ground (cleanName subStr).toName
      let objTerm := match Zil.Parser.termFromToken objStr with
        | .ok t => t
        | .error _ => Term.ground (cleanName objStr).toName
      let relName := match Zil.Parser.nameFromToken r with
        | .ok n => n
        | .error _ => (cleanName r).toName
      let newFact : RelExpr := {
        subject := subTerm
        relation := relName
        object := objTerm
        attrs := #[]
      }
      currentFacts := currentFacts.push newFact

  return currentFacts

/-- Execute a trace of sequential operation invocations from initial facts. -/
def executeTrace
    (p : Program)
    (ops : Array Operation)
    (initialFacts : Array RelExpr)
    (trace : List OpInvocation) : Except String (Array RelExpr) := do
  let mut state := initialFacts
  for inv in trace do
    match ops.find? (fun op => op.name == inv.opName) with
    | none => throw s!"Unknown operation '{inv.opName}' in trace"
    | some op =>
        state ← executeOperation p op inv state
  return state

end ZilLib.Operation

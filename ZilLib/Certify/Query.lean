import ZilLib.Certify.Check
import Zil.Engine.Query

/-!
# Certifying the answers to a query

A certificate says which facts the program entails. The answers to a query follow from that set by matching alone, so once the set is
certified they can be checked without the engine's query code: the rows below are computed here, from the certified facts, with the
matching functions of the checker, and compared with the rows the engine returns. Then the answers are exactly these rows, and a
binding that is not among them is not an answer: the negative answers are certified too, by completeness of the enumeration.

The enumeration extends a partial substitution one premise at a time, over the facts that can match it (the same method as the closure
check); the negative premises are then read against the whole set; a row is the values of the selected variables.
-/

namespace ZilLib.Certify.Query

open Zil

private partial def extend (model : Index) (premises : Array RelExpr) (position : Nat) (s : Subst) (found : Array Subst) :
    Array Subst :=
  if h : position < premises.size then
    let pattern := premises[position]
    (model.candidates pattern s).foldl (init := found) fun found fact =>
      match matchRelation pattern fact s with
      | some next => extend model premises (position + 1) next found
      | none => found
  else found.push s

/-- Every substitution that the positive premises of a query give over the facts of `model`, in the order of the premises. -/
def solutions (model : Index) (premises : Array RelExpr) : Array Subst := extend model premises 0 #[] #[]

/-- The rows of a query over a set of facts: the values of the selected variables for every substitution that satisfies the premises
and none of the negative premises, without repetition. `none` when the query is not safe (a selected or negated variable that no
positive premise binds), as the engine does not answer such a query either. -/
def answers (facts : Array RelExpr) (query : Query) : Option (Array (Array Term)) :=
  if !query.selectedVariablesBound || !query.safe then none
  else
    let model := Index.ofFacts facts
    let rows := (solutions model query.premises).filterMap fun s =>
      let negativesHold := query.negativePremises.all fun negative =>
        match instantiate s negative with
        | some ground => !model.hasMatch ground
        | none => false
      if !negativesHold then none
      else query.select.mapM fun name => (s.find? (·.1 == name)).map (·.2)
    some (rows.foldl (init := #[]) fun kept row => if kept.contains row then kept else kept.push row)

/-- The rows the engine returns for the query over the same facts. -/
def engineAnswers (facts : Array RelExpr) (query : Query) : Array (Array Term) :=
  let rows := (Engine.solve facts query).filterMap fun binding =>
    query.select.mapM fun name => (binding.find? (·.1 == name)).map (·.2)
  rows.foldl (init := #[]) fun kept row => if kept.contains row then kept else kept.push row

/-- A row as text: `variable=node` for each selected variable. -/
def renderRow (query : Query) (row : Array Term) : String :=
  " ".intercalate ((query.select.zip row).toList.map fun (name, term) =>
    s!"{name}=" ++ (match term with | .node node => toString node.name | .var other => "?" ++ toString other))

/-- What the comparison found. -/
structure Comparison where
  rows : Array (Array Term)
  /-- Rows only the checker found, and rows only the engine returned. -/
  onlyChecker : Array (Array Term)
  onlyEngine : Array (Array Term)

def Comparison.agree (comparison : Comparison) : Bool := comparison.onlyChecker.isEmpty && comparison.onlyEngine.isEmpty

/-- Compare the rows the checker computes from `checked` with the rows the engine returns from `engine`; these are the same facts, unless
the engine's closure is under test. `none` for a query that is not safe. -/
def compareOver (checked engine : Array RelExpr) (query : Query) : Option Comparison :=
  (answers checked query).map fun mine =>
    let theirs := engineAnswers engine query
    { rows := mine, onlyChecker := mine.filter (!theirs.contains ·), onlyEngine := theirs.filter (!mine.contains ·) }

/-- Compare the checker's rows with the engine's over the same facts. -/
def compare (facts : Array RelExpr) (query : Query) : Option Comparison := compareOver facts facts query

end ZilLib.Certify.Query

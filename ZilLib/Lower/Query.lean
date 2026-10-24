import Zil.Core.Query
import Zil.Core.Relation
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain
import ZilLib.Lower.Rules

/-!
# Lowering Queries to Invariants (APL-14)

Translates ZIL queries into `TSModule` invariant expressions.
In ZIL, a safety invariant is formulated as a query that must return no answers (empty set).
Lowering expands the query body over the finite domain, asserting that no satisfying assignment exists.
-/

namespace ZilLib.Lower.Query

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower
open ZilLib.Lower.Rules

/-- Lower a ZIL Query into an invariant predicate asserting that the query body is never satisfied. -/
def lowerQuery (d : Domain) (q : Zil.Query) : Except String (String × TSExpr) := do
  let qName := toString q.name
  let freeVars := q.variables.toList.map toString
  let assignments := allAssignments freeVars d.nodes.toList

  let mut violationDisjuncts : List TSExpr := []

  for a in assignments do
    let mut premiseConjuncts : List TSExpr := []
    let mut valid := true

    -- Positive premises
    for p in q.premises do
      let pRel := toString p.relation
      match resolveTerm p.subject a, resolveTerm p.object a with
      | some s_p, some o_p =>
          let pVar := baseVarName pRel s_p o_p
          premiseConjuncts := .var pVar false :: premiseConjuncts
      | _, _ => valid := false

    -- Negative premises
    for np in q.negativePremises do
      let npRel := toString np.relation
      match resolveTerm np.subject a, resolveTerm np.object a with
      | some s_np, some o_np =>
          let npVar := baseVarName npRel s_np o_np
          premiseConjuncts := .not (.var npVar false) :: premiseConjuncts
      | _, _ => valid := false

    if valid && !premiseConjuncts.isEmpty then
      violationDisjuncts := mkAndList premiseConjuncts.reverse :: violationDisjuncts

  -- Invariant: NOT (any violation exists)
  let anyViolation := mkOrList violationDisjuncts.reverse
  let invariantExpr := .not anyViolation
  pure (qName, invariantExpr)

/-- Create an invariant asserting that a specific relation has no facts anywhere in the domain. -/
def lowerEmptyRelationInvariant (d : Domain) (rel : String) : String × TSExpr := Id.run do
  let mut nonnegConjuncts : List TSExpr := []
  for sub in d.nodes do
    for obj in d.nodes do
      let bVar := baseVarName rel sub obj
      nonnegConjuncts := .not (.var bVar false) :: nonnegConjuncts
  (s!"no_{sanitize rel}", mkAndList nonnegConjuncts.reverse)

end ZilLib.Lower.Query

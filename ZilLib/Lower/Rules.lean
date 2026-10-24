import Zil.Core.Program
import Zil.Core.Rule
import Zil.Core.Relation
import Zil.Core.Attribute
import ZilLib.Certify.Check
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain
import ZilLib.Lower.Facts

/-!
# Lowering Rules to Step Operator (APL-13)

Compiles safe, stratified ZIL Datalog rules into a discrete `TSModule.next` transition step operator.
Unrolls existential premise variables over the finite domain via quantifier elimination,
producing exact bit-matrix propositional next-state relations.
-/

namespace ZilLib.Lower.Rules

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower
open ZilLib.Lower.Facts

/-- Conjunction and disjunction helpers. -/
def mkAndList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool true
  | [e] => e
  | e :: rest => .and e (mkAndList rest)

def mkOrList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool false
  | [e] => e
  | e :: rest => .or e (mkOrList rest)

/-- Substitution mapping rule variable names to node strings. -/
abbrev NodeSubst := List (String × String)

def lookupSubst (s : NodeSubst) (v : String) : Option String :=
  s.find? (·.1 == v) |>.map (·.2)

/-- Resolve a term to a concrete node under a substitution. -/
def resolveTerm (t : Term) (s : NodeSubst) : Option String :=
  match t with
  | .node n => some (toString n.name)
  | .var name => lookupSubst s (toString name)

/-- Generate all assignments of free variables to nodes in the domain. -/
def allAssignments (vars : List String) (nodes : List String) : List NodeSubst :=
  match vars with
  | [] => [[]]
  | v :: vs =>
      let rest := allAssignments vs nodes
      nodes.flatMap fun n =>
        rest.map fun s => (v, n) :: s

/-- Closure depth bound: maximum number of steps to guaranteed fixpoint. -/
def closureDepthBound (d : Domain) : Nat :=
  max (d.relations.size * d.nodes.size * d.nodes.size) 1

/-- Lower a set of rules into the `TSModule.next` transition relation. -/
def lowerNext (d : Domain) (rules : Array Rule) : Except String TSExpr := do
  -- 1. Safety check
  for r in rules do
    unless r.safe do
      throw s!"unsafe rule '{r.name}': head or negative variables not bound positively"

  -- 2. Stratification check
  match ZilLib.Certify.stratify rules with
  | .ok _ => pure ()
  | .error err => throw s!"rules are not stratified: {err}"

  let mut nextEqs : List TSExpr := []

  -- For each relation and node pair (sub, obj), construct the next-state condition
  for rel in d.relations do
    let rulesForRel := rules.filter (fun r => toString r.conclusion.relation == rel)

    for sub in d.nodes do
      for obj in d.nodes do
        let bVar := baseVarName rel sub obj

        -- Accumulate firing conditions across all rules for this relation
        let mut firingDisjuncts : List TSExpr := []

        for r in rulesForRel do
          -- Initial substitution from conclusion matching
          let mut initSubst : NodeSubst := []
          let mut canMatch := true

          -- Match conclusion subject
          match r.conclusion.subject with
          | .node n => if toString n.name != sub then canMatch := false
          | .var v => initSubst := (toString v, sub) :: initSubst

          -- Match conclusion object
          match r.conclusion.object with
          | .node n => if toString n.name != obj then canMatch := false
          | .var v =>
              let vName := toString v
              if let some existing := lookupSubst initSubst vName then
                if existing != obj then canMatch := false
              else
                initSubst := (vName, obj) :: initSubst

          if canMatch then
            -- Find free variables in the rule
            let boundVars := initSubst.map (·.1)
            let freeVars := r.variables.toList.map toString |>.filter (!boundVars.contains ·)

            -- Enumerate all assignments for free variables
            let assignments := allAssignments freeVars d.nodes.toList

            for a in assignments do
              let fullSubst := initSubst ++ a
              let mut premiseConjuncts : List TSExpr := []
              let mut substValid := true

              -- Positive premises
              for p in r.premises do
                let pRel := toString p.relation
                match resolveTerm p.subject fullSubst, resolveTerm p.object fullSubst with
                | some s_p, some o_p =>
                    let pVar := baseVarName pRel s_p o_p
                    premiseConjuncts := .var pVar false :: premiseConjuncts

                    -- Positive premise attribute constraints
                    for attr in p.attrs do
                      let aKey := toString attr.key
                      let hVar := hasAttrVarName pRel aKey s_p o_p
                      premiseConjuncts := .var hVar false :: premiseConjuncts
                      match attr.value with
                      | .term (.var v) =>
                          if let some vVal := lookupSubst fullSubst (toString v) then
                            if let some idx := d.nodes.findIdx? (· == vVal) then
                              let vVar := valAttrVarName pRel aKey s_p o_p
                              premiseConjuncts := .eq (.var vVar false) (.constInt idx) :: premiseConjuncts
                      | val =>
                          let enc := encodeAttrValue d val
                          let vVar := valAttrVarName pRel aKey s_p o_p
                          premiseConjuncts := .eq (.var vVar false) (.constInt enc) :: premiseConjuncts
                | _, _ => substValid := false

              -- Negative premises
              for np in r.negativePremises do
                let npRel := toString np.relation
                match resolveTerm np.subject fullSubst, resolveTerm np.object fullSubst with
                | some s_np, some o_np =>
                    let npVar := baseVarName npRel s_np o_np
                    premiseConjuncts := .not (.var npVar false) :: premiseConjuncts
                | _, _ => substValid := false

              if substValid then
                firingDisjuncts := mkAndList premiseConjuncts.reverse :: firingDisjuncts

        -- Base variable transition: r' == (r \/ fires)
        let anyFires := mkOrList firingDisjuncts.reverse
        let nextBase := .or (.var bVar false) anyFires
        nextEqs := .eq (.var bVar true) nextBase :: nextEqs

        -- Attribute variable transitions (attributes persist or are updated)
        let relAttrs := d.attrKeys.filter (·.1 == rel)
        for (_, key) in relAttrs do
          let hVar := hasAttrVarName rel key sub obj
          let vVar := valAttrVarName rel key sub obj
          -- In pure Datalog step, attributes persist once derived
          nextEqs := .eq (.var hVar true) (.var hVar false) :: nextEqs
          nextEqs := .eq (.var vVar true) (.var vVar false) :: nextEqs

  pure (mkAndList nextEqs.reverse)

end ZilLib.Lower.Rules

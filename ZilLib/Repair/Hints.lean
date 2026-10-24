import Zil.Core.Program
import Zil.Core.Rule
import Zil.Core.Relation
import Zil.Core.Attribute
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain
import ZilLib.Lower.Facts
import ZilLib.Lower.Rules
import ZilLib.Lower.Equivalence
import ZilLib.Operation.AST

/-!
# Rule Repair Hints (APL-46)

From a replayed counterexample trace produced by equivalence checking or invariant checking,
identifies the exact rule instance that fired to produce a spurious derivation or invariant
violation, and synthesizes candidate repair patches:
  1. Missing negative premise (e.g. `AND NOT ?sub#revoked@?obj`)
  2. Missing guard premise (e.g. `AND ?sub#is_active@...`)
  3. Inverted argument orientation (e.g. swapping subject and object variables in premises)

Per APL-46 specification:
"It only suggests; it never edits a file."
-/

namespace ZilLib.Repair

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower
open ZilLib.Lower.Rules (NodeSubst resolveTerm allAssignments cleanRel)
open ZilLib.Lower.Equivalence (EquivDivergence)
open ZilLib.Operation (matchRelName cleanName)

/-- Normalize relation Name. -/
def cleanRelName (n : Name) : String :=
  cleanRel (toString n)

/-- A suggested repair patch for a rule. -/
structure CandidatePatch where
  kind : String            -- "inverted_arguments", "missing_negative_premise", "missing_guard"
  ruleName : String
  description : String
  suggestedPatch : String
  deriving Inhabited, Repr

/-- Explanation of a firing rule instance that caused divergence or invariant violation. -/
structure FiringRuleInstance where
  ruleName : String
  conclusionRel : String
  subject : String
  object : String
  subst : List (String × String)
  deriving Inhabited, Repr

/-- Comprehensive repair report for an observed divergence. -/
structure RepairReport where
  targetRel : String
  subject : String
  object : String
  firingInstance : Option FiringRuleInstance
  candidatePatches : List CandidatePatch
  deriving Inhabited, Repr

/-- Check if a relation atom is true in a given transition system state. -/
def isAtomTrueInState (_d : Domain) (m : TSModule) (state : TSState) (pfx : String) (rel : String) (sub : String) (obj : String) : Bool :=
  let varNameWithPfx := baseVarName (pfx ++ rel) sub obj
  let varNameRaw := baseVarName rel sub obj
  if TSState.getVar m state varNameWithPfx == some (TSVal.bool true) then
    true
  else if TSState.getVar m state varNameRaw == some (TSVal.bool true) then
    true
  else
    false

/-- Identify which rule in a program derived a target fact in the counterexample state. -/
def findFiringRuleInstance
    (d : Domain)
    (m : TSModule)
    (p : Program)
    (state : TSState)
    (pfx : String)
    (targetRel : String)
    (sub : String)
    (obj : String) : Option FiringRuleInstance := Id.run do
  for r in p.allRules do
    let cRel := cleanRelName r.conclusion.relation
    if matchRelName cRel targetRel then
      let cSubVar := match r.conclusion.subject with
        | .var v => toString v
        | .node n => toString n.name
      let cObjVar := match r.conclusion.object with
        | .var v => toString v
        | .node n => toString n.name

      let allRuleVars := r.variables.toList.map toString |>.eraseDups
      let otherVars := allRuleVars.filter (fun v => v != cSubVar && v != cObjVar)
      let assignments := allAssignments otherVars d.nodes.toList

      for baseSubst in assignments do
        let subst : NodeSubst := (cSubVar, sub) :: (cObjVar, obj) :: baseSubst

        -- Check all positive premises
        let allPosTrue := r.premises.all fun prem =>
          match resolveTerm prem.subject subst, resolveTerm prem.object subst with
          | some pSub, some pObj =>
              isAtomTrueInState d m state pfx (cleanRelName prem.relation) pSub pObj
          | _, _ => false

        -- Check all negative premises
        let allNegFalse := r.negativePremises.all fun nprem =>
          match resolveTerm nprem.subject subst, resolveTerm nprem.object subst with
          | some nSub, some nObj =>
              !isAtomTrueInState d m state pfx (cleanRelName nprem.relation) nSub nObj
          | _, _ => true

        if allPosTrue && allNegFalse then
          return some {
            ruleName := toString r.name,
            conclusionRel := cRel,
            subject := sub,
            object := obj,
            subst := subst
          }
  return none

/-- Synthesize candidate repair hints for a divergence or spurious derivation. -/
def synthesizeRepairHints
    (pA pB : Program)
    (d : Domain)
    (m : TSModule)
    (state : TSState)
    (div : EquivDivergence) : RepairReport := Id.run do
  let (faultyProgram, pfx, _isSpuriousB) :=
    if div.valB && !div.valA then
      (pB, "b_", true)
    else
      (pA, "a_", false)

  let firingOpt := findFiringRuleInstance d m faultyProgram state pfx div.relation div.subject div.object
  let mut patches : List CandidatePatch := []

  if let some firing := firingOpt then
    let ruleOpt := faultyProgram.allRules.find? (toString ·.name == firing.ruleName)
    if let some r := ruleOpt then
      -- 1. Check for inverted arguments in premise vs conclusion or vs model A
      for prem in r.premises do
        let pSubVar := match prem.subject with | .var v => toString v | .node n => toString n.name
        let pObjVar := match prem.object with | .var v => toString v | .node n => toString n.name
        let cSubVar := match r.conclusion.subject with | .var v => toString v | .node n => toString n.name
        let cObjVar := match r.conclusion.object with | .var v => toString v | .node n => toString n.name

        -- If premise inverts conclusion variable order
        if pSubVar == cObjVar && pObjVar == cSubVar then
          patches := {
            kind := "inverted_arguments",
            ruleName := firing.ruleName,
            description := s!"Premise '{cleanRelName prem.relation}' inverts variables (?{pSubVar}, ?{pObjVar}) relative to conclusion",
            suggestedPatch := s!"Swap premise terms: IF ?{pObjVar}#{cleanRelName prem.relation}@?{pSubVar}"
          } :: patches

      -- 2. Look at reference rules in Model A (if comparing two models)
      let refRules := pA.allRules.toList.filter (fun (ra : Rule) => matchRelName (cleanRelName ra.conclusion.relation) (cleanRelName r.conclusion.relation))
      for ra in refRules do
        -- Check if Model A has a negative premise that Model B is missing
        for aNeg in ra.negativePremises do
          let aRel := cleanRelName aNeg.relation
          if !r.negativePremises.any (fun bNeg => matchRelName (cleanRelName bNeg.relation) aRel) then
            patches := {
              kind := "missing_negative_premise",
              ruleName := firing.ruleName,
              description := s!"Model A requires negative condition '{aRel}' absent in rule '{r.name}'",
              suggestedPatch := s!"Add negative premise: AND NOT ?{match aNeg.subject with | .var v => toString v | .node n => toString n.name}#{aRel}@?{match aNeg.object with | .var v => toString v | .node n => toString n.name}"
            } :: patches

        -- Check if Model A has a guard premise that Model B is missing
        for aPrem in ra.premises do
          let aRel := cleanRelName aPrem.relation
          if !r.premises.any (fun bPrem => matchRelName (cleanRelName bPrem.relation) aRel) then
            patches := {
              kind := "missing_guard",
              ruleName := firing.ruleName,
              description := s!"Model A enforces premise '{aRel}' not present in rule '{r.name}'",
              suggestedPatch := s!"Add guard premise: AND ?{match aPrem.subject with | .var v => toString v | .node n => toString n.name}#{aRel}@?{match aPrem.object with | .var v => toString v | .node n => toString n.name}"
            } :: patches

      -- 3. General security anti-pattern repairs (missing revocation / activation guard)
      if r.negativePremises.isEmpty then
        let availableRevocations := d.relations.filter fun rel =>
          rel.contains "revok" || rel.contains "den" || rel.contains "disabl" || rel.contains "block"
        for revRel in availableRevocations do
          patches := {
            kind := "missing_negative_premise",
            ruleName := firing.ruleName,
            description := s!"Rule '{r.name}' has no revocation guard; spurious derivation could be prevented with '{revRel}'",
            suggestedPatch := s!"Add negative premise: AND NOT ?{match r.conclusion.subject with | .var v => toString v | .node n => toString n.name}#{revRel}@?{match r.conclusion.object with | .var v => toString v | .node n => toString n.name}"
          } :: patches

  return {
    targetRel := div.relation,
    subject := div.subject,
    object := div.object,
    firingInstance := firingOpt,
    candidatePatches := patches.reverse
  }

/-- Render a repair report to human-readable console output. -/
def renderRepairReport (report : RepairReport) : String := Id.run do
  let mut out := ""
  out := out ++ s!"Rule repair analysis for divergent fact: {report.targetRel}({report.subject}, {report.object})\n"
  match report.firingInstance with
  | some inst =>
      out := out ++ s!"  Firing rule instance: '{inst.ruleName}'\n"
      let bindingsStr := String.intercalate ", " (inst.subst.map fun (k, v) => s!"?{k} = {v}")
      out := out ++ s!"  Variable bindings: {bindingsStr}\n"
  | none =>
      out := out ++ "  No single rule instance uniquely accounted for this derivation.\n"

  if report.candidatePatches.isEmpty then
    out := out ++ "  No immediate rule pattern patches detected.\n"
  else
    out := out ++ s!"  Candidate repair patches ({report.candidatePatches.length}):\n"
    for (p, idx) in report.candidatePatches.zip (List.range report.candidatePatches.length) do
      out := out ++ s!"    [{idx + 1}] [{p.kind}] {p.description}\n"
      out := out ++ s!"        Suggestion: {p.suggestedPatch}\n"
  return out

end ZilLib.Repair

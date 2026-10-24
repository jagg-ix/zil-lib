import Zil.Core.Program
import Zil.Core.Rule
import Zil.Core.Relation
import Zil.Core.Attribute
import ZilLib.TransitionSystem

/-!
# Entity and Relational Domain Extraction (APL-12, TS-05)

Extracts the finite universe of nodes, relations, and attribute schemas from a ZIL program,
and defines the bijective mapping between ZIL relation facts and `TSModule` boolean/QF_LIA variables.
-/

namespace ZilLib.Lower

open Zil
open ZilLib.TransitionSystem

/-- Sanitize arbitrary string (names with ':', '#', '-', etc.) into a clean SMT/Lean identifier. -/
def sanitize (s : String) : String :=
  let sanitized := s.map fun c => if c.isAlphanum then c else '_'
  if sanitized.isEmpty then "x"
  else if (sanitized.toList.head?.getD ' ').isDigit then "v_" ++ sanitized
  else sanitized

/-- Distinct variable name for a relation atom `rel(sub, obj)`. -/
def baseVarName (rel sub obj : String) : String :=
  s!"r_{sanitize rel}_{sanitize sub}_{sanitize obj}"

/-- Distinct variable name for attribute presence flag `has_attr(rel, key, sub, obj)`. -/
def hasAttrVarName (rel key sub obj : String) : String :=
  s!"has_{sanitize rel}_{sanitize key}_{sanitize sub}_{sanitize obj}"

/-- Distinct variable name for attribute value `val_attr(rel, key, sub, obj)`. -/
def valAttrVarName (rel key sub obj : String) : String :=
  s!"val_{sanitize rel}_{sanitize key}_{sanitize sub}_{sanitize obj}"

/-- Parsed atom representation from variable name. -/
structure AtomVarInfo where
  relation : String
  subject : String
  object : String
  deriving Inhabited, BEq, Repr

/-- Extract node name from a ZIL Term. -/
def nodeNameOfTerm (t : Term) : Option String :=
  match t with
  | .node n => some (toString n.name)
  | .var _ => none

/-- Finite universe specification for lowering. -/
structure Domain where
  nodes : Array String
  relations : Array String
  attrKeys : Array (String × String) -- (relation, key) pairs
  varToAtom : Array (String × AtomVarInfo)
  deriving Inhabited, Repr

namespace Domain

/-- Look up atom info for a base variable name. -/
def findAtom (d : Domain) (varName : String) : Option AtomVarInfo :=
  d.varToAtom.find? (·.1 == varName) |>.map (·.2)

/-- Extract domain from a parsed ZIL program. -/
def fromProgram (p : Program) (extraNodes : Array String := #[]) : Domain := Id.run do
  let mut nodesSet : Array String := extraNodes
  let mut relsSet : Array String := #[]
  let mut attrPairs : Array (String × String) := #[]

  let addNode (n : String) (set : Array String) : Array String :=
    if set.contains n then set else set.push n

  let addRel (r : String) (set : Array String) : Array String :=
    if set.contains r then set else set.push r

  let addAttrPair (r k : String) (set : Array (String × String)) : Array (String × String) :=
    if set.any (fun (r', k') => r' == r && k' == k) then set else set.push (r, k)

  -- 1. Scan facts
  for f in p.facts do
    if let some s := nodeNameOfTerm f.subject then nodesSet := addNode s nodesSet
    if let some o := nodeNameOfTerm f.object then nodesSet := addNode o nodesSet
    let r := toString f.relation
    relsSet := addRel r relsSet
    for attr in f.attrs do
      let k := toString attr.key
      attrPairs := addAttrPair r k attrPairs
      match attr.value with
      | .term (.node n) => nodesSet := addNode (toString n.name) nodesSet
      | _ => pure ()

  -- 2. Scan rules
  for r in p.allRules do
    for premise in r.premises ++ r.negativePremises ++ #[r.conclusion] do
      if let some s := nodeNameOfTerm premise.subject then nodesSet := addNode s nodesSet
      if let some o := nodeNameOfTerm premise.object then nodesSet := addNode o nodesSet
      let relName := toString premise.relation
      relsSet := addRel relName relsSet
      for attr in premise.attrs do
        let k := toString attr.key
        attrPairs := addAttrPair relName k attrPairs
        match attr.value with
        | .term (.node n) => nodesSet := addNode (toString n.name) nodesSet
        | _ => pure ()

  -- 3. Scan queries
  for q in p.queries do
    for premise in q.premises ++ q.negativePremises do
      if let some s := nodeNameOfTerm premise.subject then nodesSet := addNode s nodesSet
      if let some o := nodeNameOfTerm premise.object then nodesSet := addNode o nodesSet
      let relName := toString premise.relation
      relsSet := addRel relName relsSet

  -- Guarantee non-empty universe
  if nodesSet.isEmpty then nodesSet := #["n:c0"]
  if relsSet.isEmpty then relsSet := #["rel0"]

  -- Sort for determinism
  let nodes := nodesSet.qsort (· < ·)
  let relations := relsSet.qsort (· < ·)

  -- Build varToAtom map
  let mut varMap : Array (String × AtomVarInfo) := #[]
  for rel in relations do
    for sub in nodes do
      for obj in nodes do
        let vName := baseVarName rel sub obj
        varMap := varMap.push (vName, { relation := rel, subject := sub, object := obj })

  { nodes, relations, attrKeys := attrPairs, varToAtom := varMap }

/-- Generate state variables for `TSModule`. -/
def toTSVars (d : Domain) : List TSVar := Id.run do
  let mut vars : List TSVar := []
  for rel in d.relations do
    for sub in d.nodes do
      for obj in d.nodes do
        let baseName := baseVarName rel sub obj
        vars := { name := baseName, sort := .bool } :: vars

        -- Attributes for this relation
        let relAttrs := d.attrKeys.filter (·.1 == rel)
        for (_, key) in relAttrs do
          let hasName := hasAttrVarName rel key sub obj
          let valName := valAttrVarName rel key sub obj
          vars := { name := hasName, sort := .bool } :: vars
          vars := { name := valName, sort := .int } :: vars -- numeric / QF_LIA sort

  vars.reverse

end Domain

end ZilLib.Lower

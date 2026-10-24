import Zil.Core.Program
import Zil.Core.Relation
import ZilLib.Operation.AST

/-!
# Operation Extraction from ZIL Programs (APL-31)

Extracts structured `Operation` definitions from the relational tuples emitted by
`CHECK_OPERATION`, `CHECK_OPERATION_PARAM`, `CHECK_OPERATION_ADD`, and `CHECK_OPERATION_REMOVE`.
-/

namespace ZilLib.Operation

open Zil

/-- Normalize property relation name for matching (handles camelCase vs snake_case). -/
def isProp (r prop : String) : Bool :=
  let c := (cleanName r).toLower.replace "_" ""
  let p := prop.toLower.replace "_" ""
  c == p

/-- Extract all declared operations from a ZIL program. -/
def extractOperations (p : Program) : Array Operation := Id.run do
  -- Helper to lookup property of a specific entity
  let lookupProp (entity : Term) (prop : String) : Option String :=
    p.facts.findSome? fun f =>
      if f.subject == entity && isProp (toString f.relation) prop then
        some (cleanTermName f.object)
      else none

  -- Find all operation entities: ?e#kind@entity:check_operation
  let opEntities := p.facts.filterMap fun f =>
    if isProp (toString f.relation) "kind" && cleanTermName f.object == "check_operation" then
      some f.subject
    else none

  let mut ops : Array Operation := #[]

  for ent in opEntities do
    let rawOpName := (lookupProp ent "op_name").getD (cleanTermName ent)
    let opName := if rawOpName.startsWith "op_" then (rawOpName.drop 3).toString else rawOpName
    let rawGuard := lookupProp ent "guard_query"
    let guardQuery := match rawGuard with
      | some g => if g == "none" || g.isEmpty then none else some g
      | none => none

    -- Find parameters for this operation
    let paramEntities := p.facts.filterMap fun f =>
      if isProp (toString f.relation) "kind" && cleanTermName f.object == "check_op_param" then
        let opVal := lookupProp f.subject "operation"
        let opValClean := opVal.map (fun s => if s.startsWith "op_" then (s.drop 3).toString else s)
        if opVal == some opName || opValClean == some opName then
          some f.subject
        else none
      else none

    let mut params : List (String × String) := []
    for pe in paramEntities do
      if let some pName := lookupProp pe "param" then
        let pSort := (lookupProp pe "sort").getD "node"
        params := params.concat (pName, pSort)

    -- Find adds for this operation
    let addEntities := p.facts.filterMap fun f =>
      if isProp (toString f.relation) "kind" && cleanTermName f.object == "check_op_add" then
        let opVal := lookupProp f.subject "operation"
        let opValClean := opVal.map (fun s => if s.startsWith "op_" then (s.drop 3).toString else s)
        if opVal == some opName || opValClean == some opName then
          some f.subject
        else none
      else none

    let mut adds : List (String × String × String) := []
    for ae in addEntities do
      if let (some s, some r, some o) := (lookupProp ae "subject", lookupProp ae "relation", lookupProp ae "object") then
        adds := adds.concat (s, r, o)

    -- Find removes for this operation
    let remEntities := p.facts.filterMap fun f =>
      if isProp (toString f.relation) "kind" && cleanTermName f.object == "check_op_remove" then
        let opVal := lookupProp f.subject "operation"
        let opValClean := opVal.map (fun s => if s.startsWith "op_" then (s.drop 3).toString else s)
        if opVal == some opName || opValClean == some opName then
          some f.subject
        else none
      else none

    let mut removes : List (String × String × String) := []
    for re in remEntities do
      if let (some s, some r, some o) := (lookupProp re "subject", lookupProp re "relation", lookupProp re "object") then
        removes := removes.concat (s, r, o)

    ops := ops.push {
      name := opName
      guardQuery := guardQuery
      params := params
      adds := adds
      removes := removes
    }

  return ops

end ZilLib.Operation

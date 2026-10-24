import Zil.Core.Program
import Zil.Core.Relation
import Zil.Core.Attribute

/-!
# Operation AST and Invocation Representation (APL-31)

Defines data structures for administrative operations declared via `CHECK_OPERATION` macros:
guards, parameters, relational tuple additions, and relational tuple removals.
-/

namespace ZilLib.Operation

open Zil

/-- Specification of an administrative operation. -/
structure Operation where
  name : String
  guardQuery : Option String
  params : List (String × String)            -- (parameter name, sort)
  adds : List (String × String × String)      -- (subject, relation, object)
  removes : List (String × String × String)   -- (subject, relation, object)
  deriving Inhabited, Repr, BEq

/-- Concrete invocation of an operation with parameter bindings. -/
structure OpInvocation where
  opName : String
  bindings : List (String × String)          -- (parameter name, concrete node name)
  deriving Inhabited, Repr, BEq

/-- Strip namespace prefixes (e.g., "name:", "node:", "query:", "relation:") for uniform comparison. -/
def stripPrefix (pfx s : String) : String :=
  if s.startsWith pfx then (s.drop pfx.length).toString else s

def cleanName (s : String) : String :=
  let s := if s.startsWith "«" && s.endsWith "»" then ((s.drop 1).dropEnd 1).toString else s
  let s := if s.startsWith "?" then (s.drop 1).toString else s
  if s.contains ':' then
    let parts := s.splitOn ":"
    parts.getLast?.getD s
  else if s.contains '.' then
    let parts := s.splitOn "."
    parts.getLast?.getD s
  else
    s

def cleanTermName (t : Term) : String :=
  match t with
  | .node n => cleanName (toString n.name)
  | .var v => cleanName (toString v)

/-- Compare relation names ignoring camelCase vs snake_case and namespace prefixes. -/
def matchRelName (r1 r2 : String) : Bool :=
  let c1 := (cleanName r1).toLower.replace "_" ""
  let c2 := (cleanName r2).toLower.replace "_" ""
  c1 == c2

end ZilLib.Operation

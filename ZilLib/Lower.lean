import Zil.Core.Program
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain
import ZilLib.Lower.Facts
import ZilLib.Lower.Rules
import ZilLib.Lower.Query
import ZilLib.Lower.Replay

/-!
# ZIL to Transition System Lowering (APL-12, APL-13, APL-14, TS-05)

Compiles a ZIL program into a `TSModule` transition system AST:
- `APL-12`: Program facts become state variables and `Init`.
- `APL-13`: Safe rules become step operator `Next` over finite bit-matrix.
- `APL-14`: Queries become invariant expressions.
- `APL-22` & `CERT-12`: Solver traces are replayed and certified against Lean reference.
-/

namespace ZilLib.Lower

open Zil
open ZilLib.TransitionSystem

/-- Lower a ZIL program into a `TSModule` with an optional target invariant query name. -/
def lowerProgram (p : Program) (targetQuery : Option String := none) : Except String (Domain × TSModule) := do
  -- 1. Validate rule safety
  for r in p.allRules do
    unless r.safe do
      throw s!"unsafe rule '{r.name}': head or negative variables not bound by positive premises"

  -- 2. Extract domain
  let d := Domain.fromProgram p
  let vars := d.toTSVars

  -- 3. Lower Init from ground facts
  let init := Facts.lowerInit d p.facts

  -- 4. Lower Next step operator from rules
  let next ← Rules.lowerNext d p.allRules

  -- 5. Lower Invariants from queries
  let mut invariants : List (String × TSExpr) := []
  match targetQuery with
  | some qName =>
      match p.queries.find? (fun q => toString q.name == qName) with
      | some q =>
          let inv ← Query.lowerQuery d q
          invariants := [inv]
      | none =>
          throw s!"unknown query '{qName}'; available: {p.queries.map (toString ·.name)}"
  | none =>
      for q in p.queries do
        let inv ← Query.lowerQuery d q
        invariants := inv :: invariants
      invariants := invariants.reverse

  let modName := p.moduleName.map toString |>.getD "ZilModel"
  let m : TSModule := {
    name := modName,
    variables := vars,
    init := init,
    next := next,
    invariants := invariants
  }

  pure (d, m)

/-- Lower a ground program (facts only, or with rules idle) for checking at length 0 (APL-12). -/
def lowerGroundProgram (p : Program) (targetQuery : Option String := none) : Except String (Domain × TSModule) := do
  let (d, m) ← lowerProgram p targetQuery
  -- For pure length-0 check, next state can be an identity step
  let identityNext := Rules.mkAndList (m.variables.map fun v => .eq (.var v.name true) (.var v.name false))
  pure (d, { m with next := identityNext })

end ZilLib.Lower

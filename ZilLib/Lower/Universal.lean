import Zil.Core.Program
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain
import ZilLib.Lower.Facts
import ZilLib.Lower.Rules
import ZilLib.Lower.Query
import ZilLib.Lower.Replay

/-!
# Universal Contract Checking Lowering (APL-30, S1)

Lowers a ZIL policy into a `TSModule` with a symbolic initial state over a finite domain
of $N$ nodes. Base relations without defining rules are left unconstrained in `Init`,
allowing the SMT solver to search for any initial topology that can trigger an invariant violation.
-/

namespace ZilLib.Lower.Universal

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower

/-- Lower a ZIL program into a symbolic transition system over a universe of $N$ nodes. -/
def lowerUniversalProgram (p : Program) (n : Nat) (targetQuery : Option String := none) :
    Except String (Domain × TSModule) := do
  -- 1. Validate rule safety
  for r in p.allRules do
    unless r.safe do
      throw s!"unsafe rule '{r.name}': head or negative variables not bound by positive premises"

  -- 2. Build domain with N symbolic nodes
  let extraNodes := (List.range n).map (fun i => s!"node.n{i}")
  let d := Domain.fromProgram p extraNodes.toArray
  let vars := d.toTSVars

  -- 3. Determine derived relations and configured relations
  let derivedRels := p.allRules.foldl (init := #[]) fun acc r =>
    let relName := toString r.conclusion.relation
    if acc.contains relName then acc else acc.push relName

  let configuredRels := p.facts.foldl (init := #[]) fun acc f =>
    let relName := toString f.relation
    if acc.contains relName then acc else acc.push relName

  -- 4. Construct symbolic Init:
  -- - Relations with ground facts in the model are fixed (specified facts true, others false).
  -- - Derived relations start empty (false) at step 0.
  -- - Topology relations (no facts, no defining rules) are free/symbolic.
  let mut initConj : List TSExpr := []

  let hasFact (rel sub obj : String) : Option RelExpr :=
    p.facts.find? fun f =>
      toString f.relation == rel &&
      nodeNameOfTerm f.subject == some sub &&
      nodeNameOfTerm f.object == some obj

  for rel in d.relations do
    let isConfigured := configuredRels.contains rel
    let isDerived := derivedRels.contains rel
    for sub in d.nodes do
      for obj in d.nodes do
        let bVar := baseVarName rel sub obj
        let relAttrs := d.attrKeys.filter (·.1 == rel)
        match hasFact rel sub obj with
        | some fact =>
            -- Ground fact is asserted true
            initConj := .eq (.var bVar false) (.constBool true) :: initConj
            for (_, key) in relAttrs do
              let hVar := hasAttrVarName rel key sub obj
              let vVar := valAttrVarName rel key sub obj
              match fact.attrs.find? (fun a => toString a.key == key) with
              | some attr =>
                  initConj := .eq (.var hVar false) (.constBool true) :: initConj
                  initConj := .eq (.var vVar false) (.constInt (Facts.encodeAttrValue d attr.value)) :: initConj
              | none =>
                  initConj := .eq (.var hVar false) (.constBool false) :: initConj
                  initConj := .eq (.var vVar false) (.constInt 0) :: initConj
        | none =>
            if isConfigured || isDerived then
              -- Non-existent facts of configured or derived relations start false
              initConj := .eq (.var bVar false) (.constBool false) :: initConj
              for (_, key) in relAttrs do
                let hVar := hasAttrVarName rel key sub obj
                let vVar := valAttrVarName rel key sub obj
                initConj := .eq (.var hVar false) (.constBool false) :: initConj
                initConj := .eq (.var vVar false) (.constInt 0) :: initConj
            else
              -- Pure topology relations: unconstrained (symbolic)
              pure ()

  let initExpr := Facts.mkAndList initConj.reverse

  -- 5. Lower Next step operator from rules
  let next ← Rules.lowerNext d p.allRules

  -- 6. Lower Invariant from target query
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

  let modName := (p.moduleName.map toString |>.getD "UniversalModel") ++ s!"_N{n}"
  let m : TSModule := {
    name := modName,
    variables := vars,
    init := initExpr,
    next := next,
    invariants := invariants
  }

  pure (d, m)

end ZilLib.Lower.Universal

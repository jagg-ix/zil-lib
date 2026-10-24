import Zil.Core.Program
import Zil.Core.Relation
import Zil.Core.Attribute
import ZilLib.TransitionSystem
import ZilLib.Lower.Domain

/-!
# Lowering Facts to State (APL-12)

Translates ground database facts into `TSModule` variable initializations (`Init`).
At step 0, each bit-matrix variable `r_s_o` is true if and only if the ground fact
`s#r@o` is present in the database, with attribute presence flags and values initialized.
-/

namespace ZilLib.Lower.Facts

open Zil
open ZilLib.TransitionSystem
open ZilLib.Lower

/-- Encode an attribute value into an integer representation for QF_LIA. -/
def encodeAttrValue (d : Domain) (v : AttrValue) : Int :=
  match v with
  | .integer i => i
  | .boolean b => if b then 1 else 0
  | .term (.node n) =>
      let name := toString n.name
      match d.nodes.findIdx? (· == name) with
      | some idx => idx
      | none => 0
  | .text s | .decimal s =>
      match s.toInt? with
      | some i => i
      | none => (s.foldl (fun h c => (h * 31 + c.toNat) % 100000) 0 : Nat)
  | _ => 0

/-- Conjunction builder. -/
def mkAndList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool true
  | [e] => e
  | e :: rest => .and e (mkAndList rest)

/-- Build the `Init` expression for a domain and given facts. -/
def lowerInit (d : Domain) (facts : Array RelExpr) : TSExpr := Id.run do
  let mut eqList : List TSExpr := []

  -- Quick lookup index for ground facts
  let hasFact (rel sub obj : String) : Option RelExpr :=
    facts.find? fun f =>
      toString f.relation == rel &&
      nodeNameOfTerm f.subject == some sub &&
      nodeNameOfTerm f.object == some obj

  for rel in d.relations do
    for sub in d.nodes do
      for obj in d.nodes do
        let bVar := baseVarName rel sub obj
        let relAttrs := d.attrKeys.filter (·.1 == rel)

        match hasFact rel sub obj with
        | some fact =>
            -- Base relation is true
            eqList := .eq (.var bVar false) (.constBool true) :: eqList

            -- Set attribute values
            for (_, key) in relAttrs do
              let hVar := hasAttrVarName rel key sub obj
              let vVar := valAttrVarName rel key sub obj
              match fact.attrs.find? (fun a => toString a.key == key) with
              | some attr =>
                  let encodedVal := encodeAttrValue d attr.value
                  eqList := .eq (.var hVar false) (.constBool true) :: eqList
                  eqList := .eq (.var vVar false) (.constInt encodedVal) :: eqList
              | none =>
                  eqList := .eq (.var hVar false) (.constBool false) :: eqList
                  eqList := .eq (.var vVar false) (.constInt 0) :: eqList

        | none =>
            -- Base relation is false
            eqList := .eq (.var bVar false) (.constBool false) :: eqList
            for (_, key) in relAttrs do
              let hVar := hasAttrVarName rel key sub obj
              let vVar := valAttrVarName rel key sub obj
              eqList := .eq (.var hVar false) (.constBool false) :: eqList
              eqList := .eq (.var vVar false) (.constInt 0) :: eqList

  mkAndList eqList.reverse

/-- Construct an aligned `TSState` for a domain and fact set. -/
def stateFromFacts (d : Domain) (_ : TSModule) (facts : Array RelExpr) : TSState := Id.run do
  let hasFact (rel sub obj : String) : Option RelExpr :=
    facts.find? fun f =>
      toString f.relation == rel &&
      nodeNameOfTerm f.subject == some sub &&
      nodeNameOfTerm f.object == some obj

  let mut vals : List TSVal := []
  for rel in d.relations do
    for sub in d.nodes do
      for obj in d.nodes do
        let fOpt := hasFact rel sub obj
        let relPresent := fOpt.isSome
        vals := TSVal.bool relPresent :: vals

        let relAttrs := d.attrKeys.filter (·.1 == rel)
        for (_, key) in relAttrs do
          match fOpt with
          | some f =>
              match f.attrs.find? (fun a => toString a.key == key) with
              | some attr =>
                  vals := TSVal.bool true :: vals
                  vals := TSVal.int (encodeAttrValue d attr.value) :: vals
              | none =>
                  vals := TSVal.bool false :: vals
                  vals := TSVal.int 0 :: vals
          | none =>
              vals := TSVal.bool false :: vals
              vals := TSVal.int 0 :: vals
  return ⟨vals.reverse.toArray⟩

end ZilLib.Lower.Facts


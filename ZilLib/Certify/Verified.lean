import Zil.Datalog.Certify
import ZilLib.Certify.Check

/-!
# Checking an engine certificate with the checker that has a proof

`ZilLib.Certify.check` is tested but not proved. The core has a checker with a soundness theorem, `Zil.Datalog.checkCertificate`
(`checkCertificate_sound`: if it says yes, the facts of the certificate are a stable model of the program). It works on the Lean-embedded
Datalog, whose atoms and rules are a different representation from the engine's. This module translates a program and a certificate of
the engine into that representation, so that the proved checker can check them.

The translation is the part that is trusted, and it is meant to be easy to read:

* a node name, a relation, a variable or an attribute key becomes a string that determines it (`nameText`: the components with their
  lengths, so two different names never give the same text);
* the subject of a relation becomes the `object` of the atom and its object the `subject`, in every pattern and every fact alike;
* attribute values keep their kind: text and decimal numbers become strings with a prefix, so that `"1.0"` as text and as a decimal are
  different;
* attributes are sorted by key, because the engine compares them as a map and the Lean-embedded atoms compare them as a list;
* a rule has its positive premises, then its negative ones; a fact with a variable, or two attributes with one key, is refused;
* the two evaluators differ in one place, and the translation refuses it: the engine matches a variable in an attribute pattern only
  against a value that is a node (`[owner=?o]` matches `[owner=team.a]`, not `[owner="a"]` or `[owner=3]`), and the Lean-embedded
  Datalog binds it to any value. A program is refused when a fact of the certificate has a text, number or boolean value for a key that
  some rule reads with a variable.

The proved checker is a plain list implementation written for the proof, not for speed: use it on programs of some hundreds of facts.
-/

namespace ZilLib.Certify.Verified

open Zil

/-- A string that determines the name: its components, each with its kind and, for text, its length. -/
def nameText (name : Name) : String :=
  String.intercalate "." (name.components.map fun
    | .str _ text => s!"s{text.length}:{text}"
    | .num _ number => s!"n{number}"
    | .anonymous => "_")

private def termPattern : Term → Datalog.Term
  | .node node => .value (.symbol (nameText node.name))
  | .var name => .variable (nameText name)

private def attrPattern : AttrValue → Datalog.Term
  | .term term => termPattern term
  | .text text => .value (.string ("text:" ++ text))
  | .decimal text => .value (.string ("decimal:" ++ text))
  | .integer number => .value (.integer number)
  | .boolean flag => .value (.boolean flag)

private def termValue? : Term → Option Datalog.Value
  | .node node => some (.symbol (nameText node.name))
  | .var _ => none

private def attrValue? : AttrValue → Option Datalog.Value
  | .term term => termValue? term
  | .text text => some (.string ("text:" ++ text))
  | .decimal text => some (.string ("decimal:" ++ text))
  | .integer number => some (.integer number)
  | .boolean flag => some (.boolean flag)

/-- The attributes sorted by key, or the reason there is no such list. -/
private def sortedAttrs {α : Type} (describe : String) (attrs : Array (String × α)) : Except String (List (String × α)) := do
  let sorted := (attrs.qsort fun left right => left.1 < right.1).toList
  for (left, right) in sorted.zip sorted.tail do
    if left.1 == right.1 then throw s!"{describe} has two attributes with the key {right.1}"
  pure sorted

/-- A relation of a rule, as a pattern. -/
def toPattern (relation : RelExpr) : Except String Datalog.Pattern := do
  let attrs ← sortedAttrs (render relation) (relation.attrs.map fun entry => (nameText entry.key, attrPattern entry.value))
  pure { object := termPattern relation.subject, relation := nameText relation.relation,
         subject := termPattern relation.object, attrs }

/-- A ground relation, as an atom. -/
def toAtom (relation : RelExpr) : Except String Datalog.Atom := do
  let some object := termValue? relation.subject | throw s!"{render relation} has a variable"
  let some subject := termValue? relation.object | throw s!"{render relation} has a variable"
  let mut attrs : Array (String × Datalog.Value) := #[]
  for entry in relation.attrs do
    let some value := attrValue? entry.value | throw s!"{render relation} has a variable"
    attrs := attrs.push (nameText entry.key, value)
  pure { object, relation := nameText relation.relation, subject, attrs := ← sortedAttrs (render relation) attrs }

def toRule (rule : Rule) : Except String Datalog.Rule := do
  let head ← toPattern rule.conclusion
  let positive ← rule.premises.toList.mapM toPattern
  let negative ← rule.negativePremises.toList.mapM toPattern
  pure { name := rule.name.toString, head, literals := positive.map .positive ++ negative.map .negative }

def toProgram (facts : Array RelExpr) (rules : Array Rule) : Except String Datalog.Program := do
  pure { facts := ← facts.toList.mapM toAtom, rules := ← rules.toList.mapM toRule }

def toCertificate (certificate : Certificate) : Except String Datalog.Certificate :=
  certificate.toList.mapM fun node => do
    pure { atom := ← toAtom node.fact, origin := node.rule.map fun name => (name, node.premises.toList) }

/-- The attribute keys that some rule reads with a variable. -/
private def variableKeys (rules : Array Rule) : Array Name :=
  rules.foldl (init := #[]) fun keys rule =>
    (rule.premises ++ rule.negativePremises).foldl (init := keys) fun keys relation =>
      relation.attrs.foldl (init := keys) fun keys entry =>
        match entry.value with
        | .term (.var _) => if keys.contains entry.key then keys else keys.push entry.key
        | _ => keys

/-- A fact whose value for a key that a rule reads with a variable is not a node: the engine does not bind the variable to it and the
Lean-embedded Datalog does, so the proved checker would be judging another program. -/
def literalBehindVariable? (facts : Array RelExpr) (rules : Array Rule) : Option String :=
  let keys := variableKeys rules
  facts.findSome? fun fact =>
    fact.attrs.findSome? fun entry =>
      match entry.value with
      | .term _ => none
      | _ => if keys.contains entry.key then
          some s!"{render fact} has a text, number or boolean value for {entry.key}, which a rule reads with a variable; the engine does not bind a variable to such a value, and the proved checker would"
        else none

/-- Check the engine's certificate with the proved checker. `Except.error` means the program or the certificate could not be
translated; `ok false` means the proved checker refused. -/
def check (facts : Array RelExpr) (rules : Array Rule) (certificate : Certificate) : Except String Bool := do
  if let some problem := literalBehindVariable? (certificate.map (·.fact)) rules then throw problem
  let program ← toProgram facts rules
  let cert ← toCertificate certificate
  pure (Datalog.checkCertificate program cert)

end ZilLib.Certify.Verified

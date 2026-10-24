import ZilLib.Certify.Check
import Zil.Codec.Canonical
import Zil.Json.Ordered

/-!
# JSON encoding of derivation certificates (ZIL-CERTIFICATE/1)

This module provides serialization and deserialization between `Certificate` and the tool-independent
`ZIL-CERTIFICATE/1` JSON format specified in `spec/certificate-json-v1.md`.
-/

namespace ZilLib.Certify

open Zil.Json Zil Zil.Codec

def attrValueToJson : AttrValue → J
  | .text s => J.str s
  | .integer i => J.int i
  | .boolean b => J.bool b
  | .decimal d => J.obj #[("decimal", J.str d)]
  | .term (.node node) => J.obj #[("node", J.str (toString node.name))]
  | .term (.var name) => J.obj #[("var", J.str (toString name))]

def parseAttrValue : J → Except String AttrValue
  | .int i => pure (.integer i)
  | .str s => pure (.text s)
  | .bool b => pure (.boolean b)
  | .obj fields => do
      if let some (J.str d) := fields.find? (·.1 == "decimal") |>.map (·.2) then
        pure (.decimal d)
      else if let some (J.str n) := fields.find? (·.1 == "node") |>.map (·.2) then
        pure (.term (.ground (canonicalNameFromString n)))
      else if let some (J.str v) := fields.find? (·.1 == "var") |>.map (·.2) then
        pure (.term (.variable (canonicalNameFromString v)))
      else
        throw "invalid attribute value object"
  | _ => throw "invalid attribute value"

def attributeToJson (attr : Attribute) : J :=
  J.obj #[
    ("key", J.str (toString attr.key)),
    ("value", attrValueToJson attr.value)
  ]

def parseAttribute (j : J) : Except String Attribute := do
  let keyStr ← j.getStr? "key" |>.toExcept "attribute missing 'key'"
  let valJ ← j.get? "value" |>.toExcept "attribute missing 'value'"
  let value ← parseAttrValue valJ
  pure { key := canonicalNameFromString keyStr, value }

def factToJson (fact : RelExpr) : J :=
  let termToStr : Term → String
    | .node node => toString node.name
    | .var name => "?" ++ toString name
  let baseFields : Array (String × J) := #[
    ("subject", J.str (termToStr fact.subject)),
    ("relation", J.str (toString fact.relation)),
    ("object", J.str (termToStr fact.object))
  ]
  let fields :=
    if fact.attrs.isEmpty then
      baseFields
    else
      let sortedAttrs := fact.attrs.qsort (fun a b => toString a.key < toString b.key)
      baseFields.push ("attrs", J.arr (sortedAttrs.map attributeToJson))
  J.obj fields

def parseFact (j : J) : Except String RelExpr := do
  let subjectStr ← j.getStr? "subject" |>.toExcept "fact missing 'subject'"
  let relationStr ← j.getStr? "relation" |>.toExcept "fact missing 'relation'"
  let objectStr ← j.getStr? "object" |>.toExcept "fact missing 'object'"
  let subject :=
    if subjectStr.startsWith "?" then Term.var (canonicalNameFromString (subjectStr.drop 1).toString)
    else Term.ground (canonicalNameFromString subjectStr)
  let relation := canonicalNameFromString relationStr
  let object :=
    if objectStr.startsWith "?" then Term.var (canonicalNameFromString (objectStr.drop 1).toString)
    else Term.ground (canonicalNameFromString objectStr)
  let attrs ← match j.get? "attrs" with
    | some (J.arr items) => items.mapM parseAttribute
    | some (J.obj fields) =>
        fields.mapM fun (k, v) => do
          pure { key := canonicalNameFromString k, value := ← parseAttrValue v }
    | some J.null | none => pure #[]
    | some _ => throw "attrs must be an array or object"
  pure { subject, relation, object, attrs }

def nodeToJson (index : Nat) (node : Node) : J :=
  let ruleJ := match node.rule with
    | some r => J.str r
    | none => J.null
  let premisesJ := J.arr (node.premises.map (fun p => J.int (Int.ofNat p)))
  J.obj #[
    ("index", J.int (Int.ofNat index)),
    ("fact", factToJson node.fact),
    ("rule", ruleJ),
    ("premises", premisesJ)
  ]

def parseNode (expectedIndex : Nat) (j : J) : Except String Node := do
  let indexInt ← j.getInt? "index" |>.toExcept s!"node {expectedIndex} missing 'index'"
  let index := indexInt.toNat
  unless index == expectedIndex do
    throw s!"expected node index {expectedIndex}, found {index}"
  let factJ ← j.get? "fact" |>.toExcept s!"node {expectedIndex} missing 'fact'"
  let fact ← parseFact factJ
  let rule := match j.get? "rule" with
    | some (J.str r) => some r
    | some J.null | none => none
    | some _ => none
  let premises ← match j.get? "premises" with
    | some (J.arr items) =>
        items.mapM fun item => do
          match item with
          | J.int p => pure p.toNat
          | _ => throw s!"node {expectedIndex}: premise is not an integer"
    | some J.null | none => pure #[]
    | some _ => throw s!"node {expectedIndex}: premises must be an array"
  pure { fact, rule, premises }

def certificateToJson (cert : Certificate) : J :=
  let nodesJ := J.arr (cert.mapIdx fun idx node => nodeToJson idx node)
  J.obj #[
    ("format", J.str "ZIL-CERTIFICATE/1"),
    ("version", J.str "1.0"),
    ("nodes", nodesJ)
  ]

def renderCertificateJson (cert : Certificate) : String :=
  Zil.Json.write (certificateToJson cert) ++ "\n"

def parseCertificateJson (text : String) : Except String Certificate := do
  let j ← Zil.Json.parse text
  let format ← j.getStr? "format" |>.toExcept "certificate missing 'format'"
  unless format == "ZIL-CERTIFICATE/1" do
    throw s!"unsupported certificate format: {format}"
  let nodesJ ← match j.get? "nodes" with
    | some (J.arr items) => pure items
    | _ => throw "certificate missing 'nodes' array"
  let mut nodes : Certificate := #[]
  for i in [:nodesJ.size] do
    nodes := nodes.push (← parseNode i nodesJ[i]!)
  pure nodes

end ZilLib.Certify

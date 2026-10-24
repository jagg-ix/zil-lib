import ZilLib.Certify.Check
import Zil.Codec.Canonical
import Zil.Json.Ordered

/-!
# JSON encoding of derivation certificates (ZIL-CERTIFICATE/1)

This module provides serialization and deserialization between `Certificate` and the tool-independent
`ZIL-CERTIFICATE/1` JSON format specified in `spec/certificate-json-v1.md`.

## Injective Name Encoding
Lean `Name` values can have both string and numeric components, and string components may contain
special characters (such as double quotes or dots, e.g. in config values or URLs).
To guarantee bijective roundtrips:
- String components escape `\` as `\\`, `.` as `\.`, and leading `#` as `\#`.
- Numeric components are encoded as `#{n}`.
- Components are joined with `.` (dot).
-/

namespace ZilLib.Certify

open Lean (Name)
open Zil.Json Zil Zil.Codec

inductive NameComponent where
  | str (s : String)
  | num (n : Nat)
deriving Inhabited, BEq, Repr

def nameToComponents (name : Name) : List NameComponent :=
  let rec loop (n : Name) (acc : List NameComponent) : List NameComponent :=
    match n with
    | .anonymous => acc
    | .str p s => loop p (.str s :: acc)
    | .num p k => loop p (.num k :: acc)
  loop name []

def componentsToName (comps : List NameComponent) : Name :=
  comps.foldl (init := Name.anonymous) fun acc c =>
    match c with
    | .str s => Name.str acc s
    | .num k => Name.num acc k

def encodeComponent : NameComponent → String
  | .num n => s!"#{n}"
  | .str s => Id.run do
      let mut out := ""
      let mut first := true
      for c in s.toList do
        if c == '\\' then
          out := out ++ "\\\\"
        else if c == '.' then
          out := out ++ "\\."
        else if c == '#' && first then
          out := out ++ "\\#"
        else
          out := out.push c
        first := false
      out

def encodeName (name : Name) : String :=
  let comps := nameToComponents name
  String.intercalate "." (comps.map encodeComponent)

def decodeName (text : String) : Name := Id.run do
  if text.isEmpty then return Name.anonymous
  let mut comps : List NameComponent := []
  let mut cur : String := ""
  let mut escaped := false
  let mut isNum := false
  let mut isStart := true
  for c in text.toList do
    if escaped then
      cur := cur.push c
      escaped := false
      isStart := false
    else if c == '\\' then
      escaped := true
      isStart := false
    else if c == '.' then
      if isNum then
        match cur.toNat? with
        | some n => comps := .num n :: comps
        | none => comps := .str cur :: comps
      else
        comps := .str cur :: comps
      cur := ""
      isNum := false
      isStart := true
    else if c == '#' && isStart then
      isNum := true
      isStart := false
    else
      cur := cur.push c
      isStart := false
  if isNum then
    match cur.toNat? with
    | some n => comps := .num n :: comps
    | none => comps := .str cur :: comps
  else
    comps := .str cur :: comps
  return componentsToName comps.reverse

def attrValueToJson : AttrValue → J
  | .text s => J.str s
  | .integer i => J.int i
  | .boolean b => J.bool b
  | .decimal d => J.obj #[("decimal", J.str d)]
  | .term (.node node) => J.obj #[("node", J.str (encodeName node.name))]
  | .term (.var name) => J.obj #[("var", J.str (encodeName name))]

def parseAttrValue : J → Except String AttrValue
  | .int i => pure (.integer i)
  | .str s => pure (.text s)
  | .bool b => pure (.boolean b)
  | .obj fields => do
      if let some (J.str d) := fields.find? (·.1 == "decimal") |>.map (·.2) then
        pure (.decimal d)
      else if let some (J.str n) := fields.find? (·.1 == "node") |>.map (·.2) then
        pure (.term (.ground (decodeName n)))
      else if let some (J.str v) := fields.find? (·.1 == "var") |>.map (·.2) then
        pure (.term (.variable (decodeName v)))
      else
        throw "invalid attribute value object"
  | _ => throw "invalid attribute value"

def attributeToJson (attr : Attribute) : J :=
  J.obj #[
    ("key", J.str (encodeName attr.key)),
    ("value", attrValueToJson attr.value)
  ]

def parseAttribute (j : J) : Except String Attribute := do
  let keyStr ← j.getStr? "key" |>.toExcept "attribute missing 'key'"
  let valJ ← j.get? "value" |>.toExcept "attribute missing 'value'"
  let value ← parseAttrValue valJ
  pure { key := decodeName keyStr, value }

def factToJson (fact : RelExpr) : J :=
  let termToStr : Term → String
    | .node node => encodeName node.name
    | .var name => "?" ++ encodeName name
  let baseFields : Array (String × J) := #[
    ("subject", J.str (termToStr fact.subject)),
    ("relation", J.str (encodeName fact.relation)),
    ("object", J.str (termToStr fact.object))
  ]
  let fields :=
    if fact.attrs.isEmpty then
      baseFields
    else
      let sortedAttrs := fact.attrs.qsort (fun a b => encodeName a.key < encodeName b.key)
      baseFields.push ("attrs", J.arr (sortedAttrs.map attributeToJson))
  J.obj fields

def parseFact (j : J) : Except String RelExpr := do
  let subjectStr ← j.getStr? "subject" |>.toExcept "fact missing 'subject'"
  let relationStr ← j.getStr? "relation" |>.toExcept "fact missing 'relation'"
  let objectStr ← j.getStr? "object" |>.toExcept "fact missing 'object'"
  let subject :=
    if subjectStr.startsWith "?" then Term.var (decodeName (subjectStr.drop 1).toString)
    else Term.ground (decodeName subjectStr)
  let relation := decodeName relationStr
  let object :=
    if objectStr.startsWith "?" then Term.var (decodeName (objectStr.drop 1).toString)
    else Term.ground (decodeName objectStr)
  let attrs ← match j.get? "attrs" with
    | some (J.arr items) => items.mapM parseAttribute
    | some (J.obj fields) =>
        fields.mapM fun (k, v) => do
          pure { key := decodeName k, value := ← parseAttrValue v }
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

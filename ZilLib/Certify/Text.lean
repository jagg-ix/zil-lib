import ZilLib.Certify.Check
import Zil.Codec.Canonical

/-!
# Reading a certificate from text

The core prints its provenance as `ZIL-PROVENANCE/1` (`bin/zil trace`, and after `-- provenance --` in the output of
`bin/zil explain-query`): for every fact one `fact` row, with its number, its stratum and the relation, and one `origin` row, with
`base`, or `rule`, the rule name and the numbers of the facts that the positive premises matched. This module reads those rows as a
certificate. Everything else on a row (the strata, the negative checks, the variable binding) is ignored, because the checker works
those out itself.

A certificate that comes from text is untrusted, so a row that cannot be read is an error, and the numbers must be 0, 1, 2, ... in
order.
-/

namespace ZilLib.Certify

private def premiseNumbers (text : String) : Except String (Array Nat) :=
  if text.isEmpty then pure #[]
  else
    (text.splitOn ",").toArray.mapM fun item =>
      match item.toNat? with
      | some number => pure number
      | none => throw s!"{item} is not a fact number"

/-- Read the rows of a provenance report as a certificate. -/
def parseProvenance (text : String) : Except String Certificate := do
  let mut nodes : Certificate := #[]
  let mut pending : Option (Nat × Zil.RelExpr) := none
  for line in text.splitOn "\n" do
    match line.splitOn "\t" with
    | "fact" :: number :: _ :: relation =>
        if pending.isSome then throw s!"the fact row {nodes.size} has no origin row"
        unless number.toNat? == some nodes.size do throw s!"expected fact {nodes.size}, found {number}"
        pending := some (nodes.size, ← Zil.Codec.decodeRelation (String.intercalate "\t" relation))
    | "origin" :: number :: kind :: rest =>
        let some (expected, fact) := pending | throw s!"an origin row for {number} has no fact row"
        unless number.toNat? == some expected do throw s!"the origin row {number} does not follow fact {expected}"
        match kind, rest with
        | "base", _ => nodes := nodes.push { fact }
        | "rule", name :: premises :: _ => nodes := nodes.push { fact, rule := some name, premises := ← premiseNumbers premises }
        | _, _ => throw s!"the origin row of fact {expected} is not understood"
        pending := none
    | _ => pure ()
  if let some (number, _) := pending then throw s!"the fact row {number} has no origin row"
  pure nodes

end ZilLib.Certify

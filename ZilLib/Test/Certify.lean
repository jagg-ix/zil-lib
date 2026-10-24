import ZilLib.Certify
import ZilLib.Model
import ZilLib.Test.Harness

/-!
# Tests of the certificate checker

Run from the repository root. The positive tests check what the core's engine computes for real models (the tour, and the expanded
macro libraries of `spec/macro-extension-golden/`) and for the programs of the paper. The others change a certificate in one way and
expect the checker to name that way, and show that the engine's fixpoint loop stops early on a long chain.
-/

namespace ZilLib.Test.Certify

open ZilLib.Certify ZilLib.Test Zil

/-- Make a program from model text, through a temporary file and the core's parser. -/
private def program (text : String) : IO Zil.Program := do
  let directory ← IO.FS.createTempDir
  let file := directory / "model.zc"
  IO.FS.writeFile file text
  let loaded ← ZilLib.loadProgram file.toString
  IO.FS.removeDirAll directory
  pure loaded

private def trace (program : Zil.Program) (fuel : Nat := 64) : IO Engine.Provenance.Trace := do
  match Engine.Provenance.traceProgram program fuel with
  | .ok trace => pure trace
  | .error problem => throw (IO.userError problem)

private def certificate (program : Zil.Program) (fuel : Nat := 64) : IO Certificate :=
  Certificate.ofTrace <$> trace program fuel

private def kinds (report : Report) : List String := (report.problems.map (·.kind)).toList

private def chain (n : Nat) : String :=
  String.intercalate "\n" <|
    ["MODULE chain."] ++ (List.range n).map (fun i => s!"n:n{i}#next@n:n{i + 1}.") ++
    ["RULE base:", "IF ?a#next@?b", "THEN ?a#reaches@?b.", "RULE step:", "IF ?a#reaches@?b AND ?b#next@?c", "THEN ?a#reaches@?c.", ""]

/-- The rules of the paper's example 3, whose proof trees are exponentially large, over a chain of `n` edges. -/
private def exponential (n : Nat) : String :=
  String.intercalate "\n" <|
    ["MODULE paper.example3."] ++ (List.range n).map (fun i => s!"n:n{i}#edge@n:n{i + 1}.") ++
    ["RULE r3:", "IF ?x#edge@?y", "THEN ?x#trans@?y.",
     "RULE r4:", "IF ?x#t@?y AND ?x#u@?y AND ?y#edge@?z", "THEN ?x#trans@?z.",
     "RULE r5:", "IF ?x#trans@?y", "THEN ?x#t@?y.",
     "RULE r6:", "IF ?x#trans@?y", "THEN ?x#u@?y.", ""]

private def fact (s r o : String) : RelExpr := .mk' (.ground s.toName) r.toName (.ground o.toName)

private def positiveTests (t : Tally) : IO Unit := do
  let blast ← ZilLib.loadProgram "examples/tour/01-blast-radius.zc"
  let blastCertificate ← certificate blast
  let report := check blast.facts blast.allRules blastCertificate
  t.expect "the tour model: the engine's trace is certified" report.certified (String.intercalate "; " (report.problems.map (·.detail)).toList)
  t.expect "the tour model: 9 facts from the database, 22 derived" (report.database == 9 && report.derived == 22)
  -- a model with negation: single_points uses NOT; the closure check must have looked at instances that the negation removed
  t.expect "the tour model: the closure check examined the rule instances" (report.instances > 0)
  let goldens := (← System.FilePath.readDir "spec/macro-extension-golden").filter (·.fileName.endsWith ".expanded.zc")
  let mut totalFacts := 0
  for entry in goldens.qsort (·.fileName < ·.fileName) do
    let model ← ZilLib.loadProgram entry.path.toString
    let cert ← certificate model
    let result := check model.facts model.allRules cert
    totalFacts := totalFacts + result.facts
    t.expect s!"{entry.fileName}: certified ({result.facts} facts)" result.certified
      (String.intercalate "; " (result.problems.map (·.detail)).toList)
  t.expect "all expanded macro libraries were checked" (goldens.size == 18) s!"{goldens.size} files"
  IO.println s!"      {totalFacts} facts in {goldens.size} expanded libraries"
  -- the paper's example 3: the proof tree of trans(0,20) is exponential, the graph is not
  let paper ← program (exponential 20)
  let paperCertificate ← certificate paper
  let paperReport := check paper.facts paper.allRules paperCertificate
  t.expect "paper example 3 over a chain of 20: certified" paperReport.certified
  t.expect "paper example 3: the certificate has one node for each fact, 650 of them, where a proof tree has more than a million"
    (paperCertificate.size == 650)
  -- the certificate of an engine run is the text it prints
  let text := Engine.Provenance.renderTrace (← trace blast)
  match parseProvenance text with
  | .ok parsed =>
      let direct := blastCertificate
      t.expect "the printed provenance reads back as the same certificate"
        (parsed.size == direct.size && (List.range parsed.size).all fun i =>
          parsed[i]!.fact.semanticallyEqual direct[i]!.fact && parsed[i]!.rule == direct[i]!.rule && parsed[i]!.premises == direct[i]!.premises)
      t.expect "the certificate read from text is certified" (check blast.facts blast.allRules parsed).certified
  | .error problem => t.expect "the printed provenance can be read" false problem

private def matchingTests (t : Tally) : IO Unit := do
  let link := fact "a" "link" "b"
  let weighted : RelExpr := { link with attrs := #[{ key := `weight, value := .integer 3 }, { key := `kind, value := .text "x" }] }
  let wanting (value : AttrValue) : RelExpr := { link with attrs := #[{ key := `weight, value }] }
  t.expect "a pattern attribute is met by a fact that has it and more" ((matchRelation (wanting (.integer 3)) weighted #[]).isSome)
  t.expect "a pattern attribute with another value does not match" ((matchRelation (wanting (.integer 4)) weighted #[]).isNone)
  t.expect "a pattern attribute the fact lacks does not match"
    ((matchRelation { link with attrs := #[{ key := `colour, value := .text "x" }] } weighted #[]).isNone)
  let binding : RelExpr := { link with attrs := #[{ key := `weight, value := .term (.var `w) }] }
  t.expect "an attribute whose value is a variable binds it"
    ((matchRelation binding { weighted with attrs := #[{ key := `weight, value := .term (.node ⟨`five⟩) }] } #[]).map (·.size) == some 1)
  t.expect "a variable that is already bound must meet the same node"
    ((matchRelation (.mk' (.variable `x) `r (.variable `x)) (fact "a" "r" "b") #[]).isNone)
  t.expect "a variable that is already bound is met by the same node"
    ((matchRelation (.mk' (.variable `x) `r (.variable `x)) (fact "a" "r" "a") #[]).isSome)
  t.expect "a pattern for another relation does not match" ((matchRelation (fact "a" "r" "b") (fact "a" "s" "b") #[]).isNone)

private def faultTests (t : Tally) : IO Unit := do
  let blast ← ZilLib.loadProgram "examples/tour/01-blast-radius.zc"
  let good ← certificate blast
  let judge (nodes : Certificate) : Report := check blast.facts blast.allRules nodes
  let derived := (List.range good.size).filter fun i => good[i]!.rule.isSome
  let some firstDerived := derived.head? | t.expect "the tour certificate has derived facts" false; return
  let lastIndex := good.size - 1
  -- 1. a premise that does not come before its node: a cycle, or a forward reference
  let selfPremise := good.set! firstDerived { good[firstDerived]! with premises := #[firstDerived] }
  t.expect "a node that uses itself is refused as out of order" ((kinds (judge selfPremise)).contains "order")
  -- 2. a derived fact the rule does not give
  let wrongFact := good.set! firstDerived { good[firstDerived]! with fact := good[0]!.fact }
  t.expect "a derived fact that is not the head of the rule instance is refused" ((kinds (judge wrongFact)).contains "unjustified")
  -- 3. a rule the program does not have
  let wrongRule := good.set! firstDerived { good[firstDerived]! with rule := some "nonexistent_rule" }
  t.expect "a rule the program does not have is refused" ((kinds (judge wrongRule)).contains "no-rule")
  -- 4. a fact from nowhere
  let invented := good.push { fact := fact "service:ghost" "calls" "service:web" }
  t.expect "a database fact that is not in the database is refused" ((kinds (judge invented)).contains "unsupported")
  -- 5. a negative premise that is false: the fact a NOT forbids is in the set
  let forbidden := good.push { fact := fact "service.payments" "zil.hasFallback" "value.true" }
  let forbiddenReport := judge forbidden
  t.expect "a fact that a negative premise forbids, put in the set, is refused"
    (forbiddenReport.problems.any fun p => p.kind == "unjustified" && contains p.detail "negative premise")
  -- 6. a derived fact is missing (nothing uses the last one)
  let missingLast := good.pop
  let missingReport := judge missingLast
  t.expect "a derived fact that is left out is found by the closure check" ((kinds missingReport).contains "not-closed")
  t.expect "the closure check names the missing fact" (missingReport.problems.any fun p => contains p.detail (render good[lastIndex]!.fact))
  -- 7. a database fact is missing from the certificate
  let extraFact := fact "service:extra" "calls" "service:web"
  t.expect "a database fact that the certificate lacks is found"
    ((kinds (check (blast.facts.push extraFact) blast.allRules good)).contains "database-missing")
  -- 8. the premises of a node in the wrong order
  let twoPremises := (List.range good.size).filter fun i => good[i]!.premises.size == 2 && good[i]!.premises[0]! != good[i]!.premises[1]!
  match twoPremises.head? with
  | some i =>
      let swapped := good.set! i { good[i]! with premises := #[good[i]!.premises[1]!, good[i]!.premises[0]!] }
      t.expect "the premises of a node in another order than the rule's are refused" ((kinds (judge swapped)).contains "unjustified")
  | none => t.expect "the tour certificate has a node with two premises" false
  -- 9. a fact twice
  t.expect "a fact that appears twice is refused" ((kinds (judge (good.push good[0]!))).contains "duplicate")
  -- 10. a node that is not ground
  let notGround := good.push { fact := .mk' (.variable `x) `calls (.ground `a) }
  t.expect "a fact with a variable is refused" ((kinds (judge notGround)).contains "not-ground")
  -- a database fact with premises
  let malformed := good.set! 0 { good[0]! with premises := #[1] }
  t.expect "a database fact that names premises is refused" ((kinds (judge malformed)).contains "malformed")
  t.expect "the certificate itself is still certified after all that" (judge good).certified

private def stratificationTests (t : Tally) : IO Unit := do
  let rule (name : String) (premise negative : String) (head : String) : Rule :=
    { name := name.toName, variables := #[`x], premises := #[.mk' (.variable `x) premise.toName (.ground `v)],
      negativePremises := #[.mk' (.variable `x) negative.toName (.ground `v)], conclusion := .mk' (.variable `x) head.toName (.ground `v) }
  let cyclic := #[rule "p_not_q" "base" "q" "p", rule "q_not_p" "base" "p" "q"]
  t.expect "two rules that negate each other are not stratified" (match stratify cyclic with | .error _ => true | .ok _ => false)
  let report := check #[] cyclic #[]
  t.expect "the check reports a program that is not stratified" ((kinds report).contains "not-stratified")
  let layered := #[rule "p_not_q" "base" "q" "p"]
  t.expect "a rule with a negation over another relation is stratified, with the negated relation lower"
    (match stratify layered with
      | .ok strata => (strata.find? (·.1 == `p)).map (·.2) == some 1 && (strata.find? (·.1 == `q)).map (·.2) == some 0
      | .error _ => false)

private def engineTests (t : Tally) : IO Unit := do
  -- the engine stops after 64 rounds without saying so; the closure check sees it. With 70 edges the facts at distance 66 to 70
  -- (15 of them) are missing, and only those at distance 66 (5) have a rule instance whose premises are in the trace.
  let long ← program (chain 70)
  let truncated ← certificate long
  let report := check long.facts long.allRules truncated
  t.expect "a chain of 70 edges: the engine's default run is not closed" (!report.certified)
  t.expect "the 5 rule instances whose heads were never derived are found" (report.problemCount == 5)
  t.expect "the first missing fact is the one at distance 66"
    (report.problems.any fun p => p.kind == "not-closed" && contains p.detail "n.n0#zil.reaches@n.n66")
  t.expect "the engine's trace has 2540 facts where the closure has 2555" (truncated.size == 2540)
  let complete ← certificate long (fuel := 200)
  let full := check long.facts long.allRules complete
  t.expect "with enough rounds the same chain is certified, with 2555 facts" (full.certified && complete.size == 2555)
  let short ← program (chain 30)
  t.expect "a chain of 30 edges is certified with the default run" (check short.facts short.allRules (← certificate short)).certified

private def textTests (t : Tally) : IO Unit := do
  let blast ← ZilLib.loadProgram "examples/tour/01-blast-radius.zc"
  let text := Engine.Provenance.renderTrace (← trace blast)
  let rows := text.splitOn "\n"
  let ruleRow := rows.find? fun row => contains row "\trule\t"
  match ruleRow with
  | none => t.expect "the provenance has a rule row" false
  | some row =>
      let fields := row.splitOn "\t"
      -- the premises field is the fifth: replace it by an empty one
      let emptied := String.intercalate "\t" (fields.set 4 "")
      let tampered := String.intercalate "\n" (rows.map fun r => if r == row then emptied else r)
      match parseProvenance tampered with
      | .ok nodes => t.expect "a rule row stripped of its premises is refused" (!(check blast.facts blast.allRules nodes).certified)
      | .error problem => t.expect "a stripped rule row can be read" false problem
      let forward := String.intercalate "\t" (fields.set 4 "999")
      match parseProvenance (String.intercalate "\n" (rows.map fun r => if r == row then forward else r)) with
      | .ok nodes => t.expect "a premise number that is not a fact is refused" ((kinds (check blast.facts blast.allRules nodes)).contains "order")
      | .error problem => t.expect "a premise number out of range can be read" false problem
  let refuses (name text expected : String) : IO Unit :=
    match parseProvenance text with
    | .ok _ => t.expect name false "it was accepted"
    | .error problem => t.expect name (contains problem expected) problem
  refuses "a fact row without its origin row is refused" "ZIL-PROVENANCE\t1\nfacts\t1\nfact\t0\t0\trel\tnode:a\tr\tnode:b\t\n" "no origin row"
  refuses "numbers out of order are refused" "fact\t5\t0\trel\tnode:a\tr\tnode:b\t\norigin\t5\tbase\n" "expected fact 0"
  refuses "an origin row that is not understood is refused" "fact\t0\t0\trel\tnode:a\tr\tnode:b\t\norigin\t0\tmagic\n" "not understood"
  refuses "a premise that is not a number is refused" "fact\t0\t0\trel\tnode:a\tr\tnode:b\t\norigin\t0\trule\tx\ta\t\t\n" "not a fact number"

/-- Run the tests. -/
def run : IO Bool := do
  let t ← Tally.new
  matchingTests t
  stratificationTests t
  positiveTests t
  faultTests t
  engineTests t
  textTests t
  t.finish

end ZilLib.Test.Certify

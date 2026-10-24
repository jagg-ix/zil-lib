import ZilLib.Certify
import ZilLib.LeanFacts
import ZilLib.Certify.Verified
import ZilLib.Certify.Query
import ZilLib.Test.Differential
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

private def trace (program : Zil.Program) (fuel : Nat := Zil.Engine.defaultFuel) : IO Engine.Provenance.Trace := do
  match Engine.Provenance.traceProgram program fuel with
  | .ok trace => pure trace
  | .error problem => throw (IO.userError problem)

private def certificate (program : Zil.Program) (fuel : Nat := Zil.Engine.defaultFuel) : IO Certificate :=
  Certificate.ofTrace <$> trace program fuel

private def kinds (report : Report) : List String := (report.problems.map (·.kind)).toList

/-- The rules of the paper's example 3, whose proof trees are exponentially large, over a chain of `n` edges. -/
private def exponential (n : Nat) : String :=
  String.intercalate "\n" <|
    ["MODULE paper.example3."] ++ (List.range n).map (fun i => s!"n:n{i}#edge@n:n{i + 1}.") ++
    ["RULE r3:", "IF ?x#edge@?y", "THEN ?x#trans@?y.",
     "RULE r4:", "IF ?x#t@?y AND ?x#u@?y AND ?y#edge@?z", "THEN ?x#trans@?z.",
     "RULE r5:", "IF ?x#trans@?y", "THEN ?x#t@?y.",
     "RULE r6:", "IF ?x#trans@?y", "THEN ?x#u@?y.", ""]

private def fact (s r o : String) : RelExpr := .mk' (.ground s.toName) r.toName (.ground o.toName)

/-- Does the checker with a soundness theorem (`Zil.Datalog.checkCertificate`) accept the certificate, after translation? -/
private def accepted (program : Zil.Program) (cert : Certificate) : Bool :=
  match Verified.check program.facts program.allRules cert with | .ok answer => answer | .error _ => false

private def positiveTests (t : Tally) : IO Unit := do
  let blast ← ZilLib.loadProgram "examples/tour/01-blast-radius.zc"
  let blastCertificate ← certificate blast
  let report := check blast.facts blast.allRules blastCertificate
  t.expect "the tour model: the engine's trace is certified" report.certified (String.intercalate "; " (report.problems.map (·.detail)).toList)
  t.expect "the tour model: 9 facts from the database, 22 derived" (report.database == 9 && report.derived == 22)
  t.expect "the tour model: accepted by the proved checker" (accepted blast blastCertificate)
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
    t.expect s!"{entry.fileName}: accepted by the proved checker" (accepted model cert)
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
  -- the checker with a soundness theorem refuses every one of these, and accepts the original
  t.expect "proved checker: the original is accepted" (accepted blast good)
  let derivedWithTwo := twoPremises.headD 0
  let mutants : List (String × Certificate) :=
    [("a node that uses itself", selfPremise), ("a derived fact the rule does not give", wrongFact),
     ("a rule the program does not have", wrongRule), ("a database fact from nowhere", invented),
     ("a fact a negative premise forbids", forbidden), ("a derived fact left out", missingLast),
     ("a derived fact whose premises are in another order", good.set! derivedWithTwo { good[derivedWithTwo]! with
        premises := #[good[derivedWithTwo]!.premises[1]!, good[derivedWithTwo]!.premises[0]!] })]
  for (name, mutant) in mutants do
    t.expect s!"proved checker: refuses {name}" (!accepted blast mutant)
  -- two things the main checker refuses and the proved checker has no reason to: a fact that appears twice, and a database fact that
  -- names premises. The set of facts is still a stable model in both cases, and a stable model is all that the proved checker says.
  t.expect "proved checker: a fact twice is the same set, and is accepted" (accepted blast (good.push good[0]!))
  t.expect "proved checker: the premises of a database fact carry no claim, and are ignored" (accepted blast malformed)
  t.expect "proved checker: refuses a database fact that the certificate lacks"
    (match Verified.check (blast.facts.push extraFact) blast.allRules good with | .ok answer => !answer | .error _ => false)

/-- The answers to a query, computed by the checker from the certified facts, are the engine's. -/
private def queryTests (t : Tally) : IO Unit := do
  let blast ← ZilLib.loadProgram "examples/tour/01-blast-radius.zc"
  let good ← certificate blast
  let facts := good.map (·.fact)
  let find (name : String) := blast.queries.find? (toString ·.name == name)
  match find "single_points", find "what_breaks_if_payments_is_down" with
  | some singlePoints, some whatBreaks =>
      match Query.compare facts singlePoints, Query.compare facts whatBreaks with
      | some single, some breaks =>
          t.expect "query single_points: the checker and the engine return the same rows" single.agree
          t.expect "query single_points: four answers" (single.rows.size == 4)
          t.expect "query what_breaks_if_payments_is_down: the same rows" breaks.agree
          t.expect "query what_breaks_if_payments_is_down: one answer, with a negative premise in the program" (breaks.rows.size == 1)
          -- the checker's rows are computed from the set it is given: take a fact away and they change, and the comparison says so
          let derivedFact := (facts.find? (·.relation == `zil.singlePointOfFailure)).getD facts[0]!
          let without := facts.filter (!·.semanticallyEqual derivedFact)
          t.expect "removing a derived fact from the set changes the rows"
            (match Query.answers without singlePoints, Query.answers facts singlePoints with
              | some a, some b => a.size != b.size
              | _, _ => false)
          t.expect "an engine that returns other rows than the checker is reported"
            (match Query.compareOver without facts singlePoints with | some c => !c.agree && !c.onlyEngine.isEmpty | none => false)
      | _, _ => t.expect "the tour queries are safe" false
  | _, _ => t.expect "the tour model has the queries single_points and what_breaks_if_payments_is_down" false
  -- a query that no positive premise binds a selected variable of is not answered, as in the engine
  let unbound : Query := { name := `unbound, variables := #[`x], select := #[`x], premises := #[] }
  t.expect "a query with an unbound selected variable is not answered" ((Query.answers facts unbound).isNone)
  -- a negative premise removes rows: services that nothing depends on
  let callsAB : RelExpr := .mk' (.variable `a) `calls (.variable `b)
  let callsBA : RelExpr := .mk' (.variable `b) `calls (.variable `a)
  let negated : Query := { name := `negated, variables := #[`a, `b], select := #[`a], premises := #[callsAB], negativePremises := #[callsBA] }
  t.expect "a negative premise is read against the whole set"
    (match Query.answers #[fact "a" "calls" "b", fact "b" "calls" "a", fact "c" "calls" "a"] negated with
      | some rows => rows.size == 1
      | none => false)

/-- What the translation to the Lean-embedded Datalog keeps apart, and what it refuses. -/
private def translationTests (t : Tally) : IO Unit := do
  t.expect "two names that print alike are different strings" (Verified.nameText (Lean.Name.mkSimple "a.b") != Verified.nameText `a.b)
  t.expect "a numeric component and a text one are different" (Verified.nameText (Lean.Name.mkNum `a 1) != Verified.nameText (Lean.Name.mkStr `a "1"))
  let attr (key : Lean.Name) (value : AttrValue) : Attribute := { key, value }
  let relation (attrs : Array Attribute) : RelExpr := { subject := .ground `a, relation := `r, object := .ground `b, attrs }
  let atom (attrs : Array Attribute) := Verified.toAtom (relation attrs)
  t.expect "attributes in another order give the same atom"
    (match atom #[attr `x (.integer 1), attr `y (.boolean true)], atom #[attr `y (.boolean true), attr `x (.integer 1)] with
      | .ok left, .ok right => left == right
      | _, _ => false)
  t.expect "text and a decimal number with the same characters give different atoms"
    (match atom #[attr `x (.text "1.0")], atom #[attr `x (.decimal "1.0")] with
      | .ok left, .ok right => left != right
      | _, _ => false)
  t.expect "a node and text with the same characters give different atoms"
    (match atom #[attr `x (.term (.ground `v))], atom #[attr `x (.text "v")] with
      | .ok left, .ok right => left != right
      | _, _ => false)
  t.expect "two attributes with one key are refused" (match atom #[attr `x (.integer 1), attr `x (.integer 2)] with | .error _ => true | .ok _ => false)
  t.expect "a fact with a variable is refused" (match Verified.toAtom (.mk' (.variable `x) `r (.ground `b)) with | .error _ => true | .ok _ => false)

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
  -- the engine used to stop after 64 rounds without saying so (zil-lean before cdec3f2); it now reaches the fixpoint or fails
  let long ← ZilLib.loadProgram "examples/certify/chain.zc"
  let current ← certificate long
  let report := check long.facts long.allRules current
  t.expect "a chain of 70 steps: the engine's trace is certified, with 140 facts" (report.certified && current.size == 140)
  t.expect "a bound of 64 rounds is an error and not a shorter trace"
    (match Engine.Provenance.traceProgram long 64 with
      | .error message => contains message "did not reach its fixpoint"
      | .ok _ => false)
  -- the report that the engine before the fix printed for the same model, kept as a fixture: 135 facts, the 66th step missing
  match parseProvenance (← IO.FS.readFile "test/fixtures/certify/chain.old-engine-trace.txt") with
  | .ok old =>
      let oldReport := check long.facts long.allRules old
      t.expect "the old engine's report has 135 facts where 140 follow" (old.size == 135)
      t.expect "the old engine's report is not certified" (!oldReport.certified)
      t.expect "the one rule instance whose head is missing is found, at distance 66" (oldReport.problemCount == 1 &&
        oldReport.problems.any fun p => p.kind == "not-closed" && contains p.detail "n.n0#zil.reaches@n.n66")
  | .error problem => t.expect "the old engine's report can be read" false problem
  let short ← program "MODULE short.\nn:a#next@n:b.\nn:b#next@n:c.\nRULE base:\nIF ?x#next@?y\nTHEN ?x#reaches@?y.\nRULE step:\nIF ?x#reaches@?y AND ?y#next@?z\nTHEN ?x#reaches@?z.\n"
  t.expect "a short chain is certified with the engine's defaults" (check short.facts short.allRules (← certificate short)).certified

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

private def jsonTests (t : Tally) : IO Unit := do
  let blast ← ZilLib.loadProgram "examples/tour/01-blast-radius.zc"
  let good ← certificate blast
  let json := renderCertificateJson good
  -- 1. Deterministic byte emission
  let json2 := renderCertificateJson good
  t.expect "JSON certificate emission is byte-deterministic" (json == json2)
  -- 2. Round-trip through JSON reader
  match parseCertificateJson json with
  | .error problem => t.expect "JSON certificate reads back" false problem
  | .ok parsed =>
      t.expect "read-back JSON certificate has the same node count" (parsed.size == good.size)
      let identical := (List.range good.size).all fun i =>
        parsed[i]!.fact.semanticallyEqual good[i]!.fact &&
        parsed[i]!.rule == good[i]!.rule &&
        parsed[i]!.premises == good[i]!.premises
      t.expect "read-back JSON certificate preserves facts, rules and premises" identical
      let report := check blast.facts blast.allRules parsed
      t.expect "read-back JSON certificate is certified" report.certified
      t.expect "re-serialized JSON certificate matches original bytes" (renderCertificateJson parsed == json)
  -- 3. Refusal of eleven faults by name on JSON certificates
  let derived := (List.range good.size).filter fun i => good[i]!.rule.isSome
  let some firstDerived := derived.head? | t.expect "the tour certificate has derived facts" false; return
  let lastIndex := good.size - 1
  let judgeJson (cert : Certificate) : Report :=
    match parseCertificateJson (renderCertificateJson cert) with
    | .ok parsed => check blast.facts blast.allRules parsed
    | .error problem => { facts := 0, database := 0, derived := 0, instances := 0, problems := #[{ kind := "parse-error", detail := problem }], problemCount := 1 }
  -- Fault 1: order
  let selfPremise := good.set! firstDerived { good[firstDerived]! with premises := #[firstDerived] }
  t.expect "JSON: a node that uses itself is refused as out of order" ((kinds (judgeJson selfPremise)).contains "order")
  -- Fault 2: unjustified
  let wrongFact := good.set! firstDerived { good[firstDerived]! with fact := good[0]!.fact }
  t.expect "JSON: a derived fact that is not the head of the rule instance is refused" ((kinds (judgeJson wrongFact)).contains "unjustified")
  -- Fault 3: no-rule
  let wrongRule := good.set! firstDerived { good[firstDerived]! with rule := some "nonexistent_rule" }
  t.expect "JSON: a rule the program does not have is refused" ((kinds (judgeJson wrongRule)).contains "no-rule")
  -- Fault 4: unsupported
  let invented := good.push { fact := fact "service:ghost" "calls" "service:web" }
  t.expect "JSON: a database fact that is not in the database is refused" ((kinds (judgeJson invented)).contains "unsupported")
  -- Fault 5: unjustified (negative premise)
  let forbidden := good.push { fact := fact "service.payments" "zil.hasFallback" "value.true" }
  let forbiddenReport := judgeJson forbidden
  t.expect "JSON: a fact that a negative premise forbids, put in the set, is refused"
    (forbiddenReport.problems.any fun p => p.kind == "unjustified" && contains p.detail "negative premise")
  -- Fault 6: not-closed
  let missingLast := good.pop
  let missingReport := judgeJson missingLast
  t.expect "JSON: a derived fact that is left out is found by the closure check" ((kinds missingReport).contains "not-closed")
  t.expect "JSON: the closure check names the missing fact" (missingReport.problems.any fun p => contains p.detail (render good[lastIndex]!.fact))
  -- Fault 7: database-missing
  let extraFact := fact "service:extra" "calls" "service:web"
  let parsedGood := match parseCertificateJson json with | .ok c => c | .error _ => good
  t.expect "JSON: a database fact that the certificate lacks is found"
    ((kinds (check (blast.facts.push extraFact) blast.allRules parsedGood)).contains "database-missing")
  -- Fault 8: unjustified (premise order)
  let twoPremises := (List.range good.size).filter fun i => good[i]!.premises.size == 2 && good[i]!.premises[0]! != good[i]!.premises[1]!
  match twoPremises.head? with
  | some i =>
      let swapped := good.set! i { good[i]! with premises := #[good[i]!.premises[1]!, good[i]!.premises[0]!] }
      t.expect "JSON: premises in reversed order are refused" ((kinds (judgeJson swapped)).contains "unjustified")
  | none => pure ()
  -- Fault 9: duplicate
  t.expect "JSON: a fact that appears twice is refused" ((kinds (judgeJson (good.push good[0]!))).contains "duplicate")
  -- Fault 10: not-ground
  let notGround := good.push { fact := .mk' (.variable `x) `calls (.ground `a) }
  t.expect "JSON: a fact with a variable is refused" ((kinds (judgeJson notGround)).contains "not-ground")
  -- Fault 11: malformed
  let malformed := good.set! 0 { good[0]! with premises := #[1] }
  t.expect "JSON: a database fact that names premises is refused" ((kinds (judgeJson malformed)).contains "malformed")
  -- 4. Syntax and structural refusals of JSON reader
  let refusesJson (name text expected : String) : IO Unit :=
    match parseCertificateJson text with
    | .ok _ => t.expect name false "it was accepted"
    | .error problem => t.expect name (contains problem expected) problem
  refusesJson "JSON missing format is refused" "{\"version\": \"1.0\", \"nodes\": []}" "missing 'format'"
  refusesJson "JSON unsupported format is refused" "{\"format\": \"OTHER/1\", \"version\": \"1.0\", \"nodes\": []}" "unsupported certificate format"
  refusesJson "JSON missing nodes is refused" "{\"format\": \"ZIL-CERTIFICATE/1\", \"version\": \"1.0\"}" "missing 'nodes'"
  refusesJson "JSON node index mismatch is refused" "{\"format\": \"ZIL-CERTIFICATE/1\", \"version\": \"1.0\", \"nodes\": [{\"index\": 3, \"fact\": {\"subject\": \"a\", \"relation\": \"r\", \"object\": \"b\"}}]}" "expected node index 0"

/-- The lines of the Lean command `zil_fact` are read as the `.zc` facts they mean, and nothing else is read as one. -/
private def leanFactTests (t : Tally) : IO Unit := do
  let line (text : String) : Option String := match ZilLib.LeanFacts.line? text with | .ok fact => fact | .error _ => some "error"
  t.expect "zil_fact: two nodes" (line "zil_fact node(function.detect) ⟶[kind] node(framework.function)" ==
    some "function.detect#kind@framework.function.")
  t.expect "zil_fact: a string, with the spacing of the generated files" (line "  zil_fact node(tier.Tier1)   ⟶[name]  \"Tier 1: Partial\"  " ==
    some "tier.Tier1#name@\"Tier 1: Partial\".")
  t.expect "zil_fact: a hyphen in a name" (line "zil_fact node(threat.TID-301) ⟶[kind] node(threat)" == some "threat.TID-301#kind@threat.")
  t.expect "zil_fact: a trailing comment" (line "zil_fact node(a) ⟶[r] node(b) // why" == some "a#r@b.")
  t.expect "a comment, a fact and a header are not zil_fact lines" (["// zil_fact node(a)", "a#r@b.", "MODULE m.", "", "zil_factory x"].all (line · == none))
  let refused (text : String) : Bool := match ZilLib.LeanFacts.line? text with | .error _ => true | .ok _ => false
  t.expect "zil_fact: no arrow" (refused "zil_fact node(a) node(b)")
  t.expect "zil_fact: a subject that is not a node" (refused "zil_fact a ⟶[r] node(b)")
  t.expect "zil_fact: a relation that is not closed" (refused "zil_fact node(a) ⟶[r node(b)")
  t.expect "zil_fact: an object that is neither a node nor a string" (refused "zil_fact node(a) ⟶[r] 42")
  t.expect "zil_fact: a string that is not closed" (refused "zil_fact node(a) ⟶[r] \"open")
  t.expect "zil_fact: a string with an escape" (refused "zil_fact node(a) ⟶[r] \"a\\\"b\"")
  t.expect "zil_fact: text after the object" (refused "zil_fact node(a) ⟶[r] node(b) node(c)")
  t.expect "zil_fact: a fact on several lines" (refused "zil_fact")
  -- the lines of a file keep their numbers, and the error says which line
  let text := "MODULE m.\n\nzil_fact node(a) ⟶[r] node(b)\nzil_fact node(c) ⟶[r]\n"
  t.expect "a translated file has the lines it had" (match ZilLib.LeanFacts.translate "MODULE m.\n\nzil_fact node(a) ⟶[r] node(b)\n" with
    | .ok out => out == "MODULE m.\n\na#r@b.\n" | .error _ => false)
  t.expect "the error names the line" (match ZilLib.LeanFacts.translate text with
    | .error problem => contains problem "line 4:" | .ok _ => false)
  -- facts and rules together: the fact lines and a .zc rule give the closure, which the checker certifies
  let loaded ← program "MODULE m.\nzil_fact node(n.a) ⟶[next] node(n.b)\nzil_fact node(n.b) ⟶[next] node(n.c)\nn.b#next@n.d.\nRULE r:\nIF ?x#next@?y\nTHEN ?y#prev@?x.\n"
  t.expect "zil_fact lines and .zc lines make one program" (loaded.facts.size == 3 && loaded.rules.size == 1)
  let cert ← certificate loaded
  t.expect "that program is certified" (check loaded.facts loaded.allRules cert).certified

/-- Run the tests. With `differential count seed`, only the comparison of the engine with the evaluator that has a proof, on that many
random programs from that seed. -/
def run (differential : Option (Nat × Nat) := none) : IO Bool := do
  let t ← Tally.new
  if let some (count, seed) := differential then
    Differential.run t count seed
    return ← t.finish
  leanFactTests t
  translationTests t
  queryTests t
  Differential.run t 300 20261024
  matchingTests t
  stratificationTests t
  positiveTests t
  faultTests t
  engineTests t
  textTests t
  jsonTests t
  t.finish

end ZilLib.Test.Certify


import Zil.Engine.Provenance
import Std.Data.HashMap

/-!
# Checking a derivation certificate

A certificate is the set of facts a program is said to entail, with a reason for each: the fact is in the database, or a rule
derived it from facts that come earlier. The core's provenance (`Zil.Engine.Provenance.Trace`) has exactly this form, so the engine's
own output is the certificate, and this module checks it without trusting the engine. It follows Tantow, Gerlach, Mennicke and
Krötzsch, "Verifying Datalog Reasoning with Lean" (ITP 2025, LIPIcs 36), and `docs/certifying-datalog.md` says where it differs.

Two checks, which together say that the facts of the certificate are exactly the facts the program entails:

* **Soundness (ordered proof graph, paper section 4.4).** Every fact is justified by the facts before it: a database fact, or the
  head of an instance of a rule whose positive premises are the facts named, in order, and whose negative premises are absent. The
  premises of node `i` have numbers below `i`, so the graph has no cycle and one pass in order suffices.
* **Closure (model check, paper section 5).** No rule instance whose positive premises are in the set and whose negative premises
  are not has a head outside the set, and the database is in the set. The paper's `checkPGR` does this for positive rules, by
  extending a partial substitution one premise at a time and stopping as soon as a premise has no match.

Negation is not in the paper (its section 8 lists it as future work and says that certificate checkers for stratified Datalog do not
exist). For a stratified program, a set of facts that passes both checks, with negative premises read against the set itself, is a
stable model of the program (the set is the least model of its reduct), and a stratified program has one stable model, the perfect
model, which is what the engine computes. The checker also checks that the program is stratified. This argument is on paper only; the
checker is not verified in Lean (target CERT-10).

What is trusted: this code, the core's parser, which says what the program and its database are, and the reader of the certificate.
The checker matches terms with its own functions, not the engine's.
-/

namespace ZilLib.Certify

open Zil

/-! ## Matching -/

/-- The nodes that variables stand for. -/
abbrev Subst := Array (Name × Term)

private def Subst.lookup (s : Subst) (name : Name) : Option Term :=
  (s.find? (·.1 == name)).map (·.2)

/-- Match a pattern term against a value, extending `s`; a variable already bound must meet the same value. -/
private def matchTerm (pattern value : Term) (s : Subst) : Option Subst :=
  match pattern with
  | .node node => if value == .node node then some s else none
  | .var name =>
      match s.lookup name with
      | some bound => if bound == value then some s else none
      | none => some (s.push (name, value))

private def matchAttrValue (pattern value : AttrValue) (s : Subst) : Option Subst :=
  match pattern, value with
  | .term p, .term v => matchTerm p v s
  | _, _ => if pattern == value then some s else none

/-- Every attribute of the pattern is on the fact, with a value that matches. The fact may have more attributes. -/
private def matchAttrs (patterns facts : Array Attribute) (s : Subst) : Option Subst :=
  patterns.foldl (init := some s) fun state pattern =>
    state.bind fun current =>
      (facts.find? (·.key == pattern.key)).bind fun fact => matchAttrValue pattern.value fact.value current

/-- Match a relation pattern against a fact. -/
def matchRelation (pattern fact : RelExpr) (s : Subst) : Option Subst :=
  if pattern.relation != fact.relation then none
  else
    (matchTerm pattern.subject fact.subject s).bind fun withSubject =>
      (matchTerm pattern.object fact.object withSubject).bind fun withObject =>
        matchAttrs pattern.attrs fact.attrs withObject

private def instantiateTerm (s : Subst) : Term → Option Term
  | .node node => some (.node node)
  | .var name => s.lookup name

private def instantiateAttrValue (s : Subst) : AttrValue → Option AttrValue
  | .term term => (instantiateTerm s term).map .term
  | value => some value

/-- Replace the variables of a pattern; `none` when one is not bound. -/
def instantiate (s : Subst) (relation : RelExpr) : Option RelExpr := do
  let subject ← instantiateTerm s relation.subject
  let object ← instantiateTerm s relation.object
  let attrs ← relation.attrs.mapM fun entry => do pure { entry with value := ← instantiateAttrValue s entry.value }
  pure { relation with subject, object, attrs }

/-- A fact as text: `subject#relation@object`. -/
def render (relation : RelExpr) : String :=
  let term : Term → String
    | .node node => toString node.name
    | .var name => "?" ++ toString name
  let attrs := if relation.attrs.isEmpty then "" else s!" [{relation.attrs.size} attribute(s)]"
  s!"{term relation.subject}#{relation.relation}@{term relation.object}{attrs}"

/-! ## Facts, indexed -/

/-- Facts by relation, by relation and subject, by relation and object, and by all three, for lookups that do not scan. -/
structure Index where
  byRelation : Std.HashMap Name (Array RelExpr) := {}
  bySubject : Std.HashMap (Name × Term) (Array RelExpr) := {}
  byObject : Std.HashMap (Name × Term) (Array RelExpr) := {}
  byTriple : Std.HashMap (Name × Term × Term) (Array RelExpr) := {}

namespace Index

private def add {κ : Type} [BEq κ] [Hashable κ] (map : Std.HashMap κ (Array RelExpr)) (key : κ) (fact : RelExpr) :=
  map.insert key ((map.getD key #[]).push fact)

def insert (index : Index) (fact : RelExpr) : Index :=
  { byRelation := add index.byRelation fact.relation fact
    bySubject := add index.bySubject (fact.relation, fact.subject) fact
    byObject := add index.byObject (fact.relation, fact.object) fact
    byTriple := add index.byTriple (fact.relation, fact.subject, fact.object) fact }

def ofFacts (facts : Array RelExpr) : Index := facts.foldl insert {}

/-- Is there a fact equal to `fact`? Attributes are compared as a map. -/
def contains (index : Index) (fact : RelExpr) : Bool :=
  (index.byTriple.getD (fact.relation, fact.subject, fact.object) #[]).any (·.semanticallyEqual fact)

/-- Is there a fact that the ground pattern matches, that is, with at least the attributes of the pattern? -/
def hasMatch (index : Index) (pattern : RelExpr) : Bool :=
  (index.byTriple.getD (pattern.relation, pattern.subject, pattern.object) #[]).any fun fact =>
    (matchRelation pattern fact #[]).isSome

/-- The facts a pattern can match under `s`, narrowed by whichever of its endpoints is already known. -/
def candidates (index : Index) (pattern : RelExpr) (s : Subst) : Array RelExpr :=
  match instantiateTerm s pattern.subject, instantiateTerm s pattern.object with
  | some subject, some object => index.byTriple.getD (pattern.relation, subject, object) #[]
  | some subject, none => index.bySubject.getD (pattern.relation, subject) #[]
  | none, some object => index.byObject.getD (pattern.relation, object) #[]
  | none, none => index.byRelation.getD pattern.relation #[]

end Index

/-! ## The certificate -/

/-- One fact of a certificate and the reason for it. -/
structure Node where
  fact : RelExpr
  /-- `none` for a fact of the database; otherwise the name of the rule that derives it, as the engine prints it. -/
  rule : Option String := none
  /-- The nodes that the positive premises of the rule matched, in the order of the premises. -/
  premises : Array Nat := #[]
  deriving Inhabited

abbrev Certificate := Array Node

/-- The certificate that a provenance trace of the core is. -/
def Certificate.ofTrace (trace : Engine.Provenance.Trace) : Certificate :=
  trace.facts.map fun node =>
    match node.origin with
    | .base => { fact := node.fact }
    | .rule name premises _ _ => { fact := node.fact, rule := some name.toString, premises }

/-- What a check found wrong. `kind` is stable text for tests and tools. -/
structure Problem where
  kind : String
  node : Option Nat := none
  detail : String
  deriving Inhabited

/-- What the check came to. -/
structure Report where
  /-- Facts in the certificate, from the database, and derived. -/
  facts : Nat
  database : Nat
  derived : Nat
  /-- Rule instances looked at by the closure check. -/
  instances : Nat
  /-- Some of the problems found: at most `limit` of them. -/
  problems : Array Problem
  /-- All of them. -/
  problemCount : Nat
  deriving Inhabited

namespace Report

/-- The facts of the certificate are exactly the facts the program entails. -/
def certified (report : Report) : Bool := report.problemCount == 0

end Report

/-! ## Stratification -/

/-- A stratum for every relation of the rules, or the reason there is none: a negative premise must be in a lower stratum than the
head, a positive one in the same or a lower stratum. -/
def stratify (rules : Array Rule) : Except String (Array (Name × Nat)) := do
  let mut names : Array Name := #[]
  for rule in rules do
    for relation in (rule.premises ++ rule.negativePremises).map (·.relation) ++ #[rule.conclusion.relation] do
      unless names.contains relation do names := names.push relation
  let mut strata : Std.HashMap Name Nat := {}
  for name in names do strata := strata.insert name 0
  for _ in [0:names.size + 1] do
    for rule in rules do
      let mut level := strata.getD rule.conclusion.relation 0
      for premise in rule.premises do level := max level (strata.getD premise.relation 0)
      for premise in rule.negativePremises do level := max level (strata.getD premise.relation 0 + 1)
      strata := strata.insert rule.conclusion.relation level
  -- one more round must change nothing; if it does, some level grows without end: a cycle through negation
  for rule in rules do
    let mut level := strata.getD rule.conclusion.relation 0
    for premise in rule.premises do level := max level (strata.getD premise.relation 0)
    for premise in rule.negativePremises do level := max level (strata.getD premise.relation 0 + 1)
    if level != strata.getD rule.conclusion.relation 0 then
      throw s!"not stratified: relation {rule.conclusion.relation} depends on itself through negation (rule {rule.name})"
  pure (names.map fun name => (name, strata.getD name 0))

/-! ## Soundness -/

/-- Why a rule does not justify a node, or `none` when it does. -/
private def unjustified (rule : Rule) (nodes : Certificate) (model : Index) (node : Node) : Option String := do
  if rule.premises.size != node.premises.size then
    return s!"rule {rule.name} has {rule.premises.size} premises, the node names {node.premises.size}"
  let mut s : Subst := #[]
  for (pattern, id) in rule.premises.zip node.premises do
    let premise := nodes[id]!
    match matchRelation pattern premise.fact s with
    | some next => s := next
    | none => return s!"premise {render pattern} does not match node {id}, {render premise.fact}"
  match instantiate s rule.conclusion with
  | none => return s!"rule {rule.name} leaves a variable of its head unbound"
  | some head =>
      unless head.semanticallyEqual node.fact do
        return s!"the head of rule {rule.name} under these premises is {render head}, not {render node.fact}"
  for negative in rule.negativePremises do
    match instantiate s negative with
    | none => return s!"rule {rule.name} leaves a variable of a negative premise unbound"
    | some ground =>
        if model.hasMatch ground then return s!"the negative premise {render ground} of rule {rule.name} is in the certificate"
  none

private def soundness (rules : Array Rule) (database : Index) (nodes : Certificate) (model : Index) : Array Problem := Id.run do
  let mut problems : Array Problem := #[]
  for h : i in [0:nodes.size] do
    let node := nodes[i]
    if !node.fact.isGround then
      problems := problems.push { kind := "not-ground", node := some i, detail := s!"{render node.fact} has a variable" }
      continue
    match node.rule with
    | none =>
        if !node.premises.isEmpty then
          problems := problems.push { kind := "malformed", node := some i, detail := "a database fact has premises" }
        else if !database.contains node.fact then
          let detail := s!"{render node.fact} is not a fact of the database and no rule derives it"
          problems := problems.push { kind := "unsupported", node := some i, detail }
    | some name =>
        if let some late := node.premises.find? (· ≥ i) then
          let detail := s!"node {i} uses node {late}, which does not come before it"
          problems := problems.push { kind := "order", node := some i, detail }
        else
          let candidates := rules.filter (toString ·.name == name)
          if candidates.isEmpty then
            problems := problems.push { kind := "no-rule", node := some i, detail := s!"the program has no rule named {name}" }
          else
            let reasons := candidates.map fun rule => unjustified rule nodes model node
            if !reasons.any (·.isNone) then
              let detail := (reasons.findSome? id).getD "no rule justifies the node"
              problems := problems.push { kind := "unjustified", node := some i, detail }
  return problems

/-! ## Closure -/

/-- The rule instances whose positive premises are in the set and whose negative premises are not: their heads must be in the set. -/
private def closureOfRule (model : Index) (rule : Rule) (limit : Nat) : Array Problem × Nat × Nat :=
  let rec go (remaining : Nat) (s : Subst) (state : Array Problem × Nat × Nat) : Array Problem × Nat × Nat :=
    match remaining with
    | 0 =>
        let (problems, count, instances) := state
        let negativesHold := rule.negativePremises.all fun negative =>
          match instantiate s negative with
          | some ground => !model.hasMatch ground
          | none => true
        if !negativesHold then (problems, count, instances)
        else
          match instantiate s rule.conclusion with
          | none =>
              let problem : Problem := { kind := "unsafe-rule", detail := s!"rule {rule.name} leaves a variable of its head unbound" }
              ((if count < limit then problems.push problem else problems), count + 1, instances + 1)
          | some head =>
              if model.contains head then (problems, count, instances + 1)
              else
                let problem : Problem :=
                  { kind := "not-closed", detail := s!"rule {rule.name} derives {render head}, which is not in the certificate" }
                ((if count < limit then problems.push problem else problems), count + 1, instances + 1)
    | remaining + 1 =>
        let pattern := rule.premises[rule.premises.size - (remaining + 1)]!
        (model.candidates pattern s).foldl (init := state) fun state fact =>
          match matchRelation pattern fact s with
          | some next => go remaining next state
          | none => state
  go rule.premises.size #[] (#[], 0, 0)

/-! ## The check -/

/-- Check a certificate against a program, given as its database and its rules. At most `limit` problems are kept; all are counted. -/
def check (facts : Array RelExpr) (rules : Array Rule) (nodes : Certificate) (limit : Nat := 20) : Report := Id.run do
  let database := Index.ofFacts facts
  let model := Index.ofFacts (nodes.map (·.fact))
  let record (state : Array Problem × Nat) (problem : Problem) : Array Problem × Nat :=
    ((if state.1.size < limit then state.1.push problem else state.1), state.2 + 1)
  let mut state : Array Problem × Nat := (#[], 0)
  match stratify rules with
  | .ok _ => pure ()
  | .error reason => state := record state { kind := "not-stratified", detail := reason }
  for problem in soundness rules database nodes model do state := record state problem
  -- a vertex of the graph is a fact: no fact twice
  let mut seen := Index.ofFacts #[]
  for h : i in [0:nodes.size] do
    let fact := nodes[i].fact
    if seen.contains fact then
      state := record state { kind := "duplicate", node := some i, detail := s!"{render fact} appears twice" }
    seen := seen.insert fact
  -- the database is in the set
  for fact in facts do
    if !model.contains fact then
      state := record state { kind := "database-missing", detail := s!"the database fact {render fact} is not in the certificate" }
  -- the set is closed under the rules
  let mut instances := 0
  for rule in rules do
    let (closureProblems, closureCount, closureInstances) := closureOfRule model rule limit
    for problem in closureProblems do
      state := ((if state.1.size < limit then state.1.push problem else state.1), state.2)
    state := (state.1, state.2 + closureCount)
    instances := instances + closureInstances
  let fromDatabase := (nodes.filter (·.rule.isNone)).size
  return { facts := nodes.size, database := fromDatabase, derived := nodes.size - fromDatabase, instances,
           problems := state.1, problemCount := state.2 }

end ZilLib.Certify

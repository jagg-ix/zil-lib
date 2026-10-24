# Certifying the engine's answers

Date: 2026-10-23. This page does three things: it says what the paper "Verifying Datalog Reasoning with Lean" establishes, checks a design
note that builds on it against the text of the paper, and lists the targets (`CERT-xx`) with what is done. The Apalache targets are in
`docs/targets.md`; the two lists meet at the replay of counterexamples (APL-22).

The paper is Johannes Tantow, Lukas Gerlach, Stephan Mennicke and Markus Krötzsch, *Verifying Datalog Reasoning with Lean*, ITP 2025,
article 36, pages 36:1 to 36:19, DOI 10.4230/LIPIcs.ITP.2025.36. Its Lean formalization is at `github.com/knowsys/CertifyingDatalog`
(version 0.2.0). Page numbers below are the paper's own.

## What the paper establishes

* **Two semantics, proved equal** (section 2, p. 36:3 to 36:4). The least model of a Datalog program and the facts that have a proof tree
  are the same set. Lemma 1 says the proof-theoretic semantics is a model; Lemma 2 says it is contained in every model.
* **A verified checker for proof trees** (section 3, p. 36:4 to 36:6). `checkValidity` agrees with the definition of a valid tree. It finds
  the rule for each step by matching, indexing rules by the sequence of relation symbols (`SymbolSequenceMap`).
* **Proof graphs** (section 4, p. 36:6 to 36:12). A graph can be exponentially smaller than a tree. The *unordered* form is checked by a
  depth-first search that also rules out cycles (Listing 4, Theorem 5, Lemma 8). The *ordered* form (`OrderedProofGraph`, section 4.4,
  p. 36:12) requires every premise of node `i` to have a number below `i`. The check is then one pass over the array, which the paper
  describes as LogSpace; acyclicity in the unordered case is NLogSpace-complete.
* **A model check** (section 5, p. 36:12 to 36:13). `checkPGR` (Listing 5) checks that a set of facts is closed under the rules, by
  extending a partial substitution one premise at a time and stopping as soon as a premise has no match in the set
  (`satisfied_of_not_active`). The paper calls it "only a first version" without the optimizations large models need.
* **Evaluation** (section 6, p. 36:13 to 36:15, Table 1). Certificates from the reasoner Nemo, converted by scripts. On a chain of 20 with
  the paper's example 3, trees take 313 MB and graphs 16 KB (unordered) or 12 KB (ordered).
* **What is left open** (section 8, p. 36:16 to 36:17). Negation, existential rules, aggregates and function terms. The text says that
  stratified negation has been integrated in certified reasoners, "but certificate checkers for stratified Datalog do not yet exist".

## The design note, checked against the paper

The note (`multi.md`) re-centers the Apalache lowering and a certificate checker on ZIL as a general relational language, with access control
as one use among others. That framing is right, and `docs/targets.md` already follows it: usersets and attributes are language features, and
the lowering is over the sorts of the model. The note's citations are mostly accurate. These are the ones that are not:

| The note says | The paper says | What to do |
|---|---|---|
| Lemma 1 is "reachability" and Lemma 2 "invariance" (p. 36:4); Lemma 1 is the soundness of positive derivations and Lemma 2 the completeness of lower-stratum models | Lemmas 1 and 2 are the two inclusions between the model-theoretic and the proof-theoretic semantics (p. 36:4). The paper has no strata | Cite the checkers (`checkValidity`, `checkPGR`), not the lemmas. Soundness of a proof is Lemma 2; the use of a model to show a fact is *not* derived is the definition of the least model |
| "Stratified Datalog certificate checker" from pairing `OrderedProofGraph` with `checkPGR` (target 4, `C_strat`) | The paper does not do it and says no such checker exists (p. 36:17) | It is new work, done here by our own argument (below). Do not cite the paper for it |
| "Certify in NLogSpace that module graphs are acyclic" with the DFS of section 4.2 | NLogSpace-completeness is the complexity of acyclicity as a problem (p. 36:12). The checker keeps a hash set and walks, so its space is linear | Say: a verified acyclicity check. For an ordered graph no search is needed |
| "LogSpace" for the ordered graph | The paper says so, as an observation, and adds that it is unclear whether it shows in practice (p. 36:12). Neither the claim nor the time is proved in Lean | Quote it as the paper's observation |
| "Hallucination-free provenance": a derived fact is accepted only with an ordered certificate | The prototype treats a node without predecessors as a database fact. "A full validation might also have to encompass that facts and rules are correctly read" (p. 36:14), and an explicit list of assumed facts "would be preferable" | The database has to be checked separately. `zilLib certify` does: a leaf that is not a fact of the model is refused |
| Apalache and Z3 outside the trusted base: certify "every external model-checking output" (target 3) | The checkers validate Datalog derivations and models of a Datalog program | Only *witnesses* can be replayed: a counterexample, or a model the tool proposes. A run that reports no violation has no certificate. The lowering and the reader of the trace stay trusted. This is APL-22 and the rule that nothing is `kernel-backed` |
| "Lemma 8 (`notReachableFromCycle`)", Listing 4, Listing 5, Table 1, section 4.4, section 5, p. 36:9 to 36:15 | Lemma 8 is `notReachableFromCycleIffPredecessorsNotReachableFromCycle` (p. 36:10); Listing 4 is `verify_via_dfs_step` (p. 36:9); Listing 5 is `checkPGR` (p. 36:13); Table 1 is p. 36:15 | Correct |
| "LIPIcs Vol. 36" | 36 is the number of the article. The PDF does not give the volume | Cite the DOI |
| `repository_scanner`, module closure and surface regression checks, `:tuple-frontend`, `:attribute-frontend` | None of them is found in `zil-lean` today (searched at 4f35b41) | Do not build on them without finding where they are |
| `QueryGovernance.lean`, `operations.zc`, `#zil_horn_grounding` | They exist (`Zil/QueryGovernance.lean`, `examples/query-governance/operations.zc`, `#zil_horn_grounding`) | Correct |
| The command names `#zil_apalache_universal`, `#zil_apalache_trace`, `#zil_commute`, `#zil_certify_witness`, `#zil_stratified_cert`, `#zil_equiv`, `#zil_repair_rules` | None exists. They are proposals | The toolkit uses `zilLib` subcommands, not Lean commands, so that nothing changes in the core |

## How ZIL fits

The engine already builds what the paper asks a reasoner to emit. `Zil.Engine.Provenance.Trace` is an array of facts; each has a number
and an origin, `base` or a rule with the numbers of the facts its positive premises matched, in order. A fact is added only after its
premises, so the numbers below it are exactly the ordered proof graph of section 4.4. The trace also records the negated instances and the
stratum, which the checker does not need and does not trust.

The checker (`ZilLib/Certify/Check.lean`) takes the model's database and rules from the core's parser and a certificate from anywhere, and
does the paper's two checks with its own matching functions, not the engine's:

1. For every node: premises have lower numbers; a database node is a fact of the model; a derived node is the head of an instance of a
   rule of that name, whose premises are the named nodes in the rule's order, and whose negated conditions have no match in the set.
2. The database is in the set; no fact is in it twice; and for every rule and every way its positive premises match facts of the set, if
   the negated conditions have no match then the head is in the set.
3. The rules are stratified (a negated relation lower than the head, a positive one not higher).

**Why this is enough for negation.** Let *M* be the set of facts in the certificate. Check 1 says that every fact of *M* is derived from the
database by the rules with the negated conditions read against *M*; that is, *M* is contained in the least model of the *reduct* of the
program by *M*. Check 2 says that *M* is closed under that reduct and contains the database, so it contains the least model. Hence *M* is
the least model of its own reduct, which is the definition of a *stable model* of the program. A stratified program has exactly one stable
model, the perfect model, and the perfect model is what the engine's stratified loop is meant to compute. So a certificate that passes
states: *M* is the perfect model of this program. The argument is not in the paper. Its first half, that *M* is a stable model, is proved
in Lean for the Lean-embedded Datalog (zil-lean `Zil.Datalog.checkCertificate_sound`, `spec/datalog-semantics-v1.md` in the core), and
`zilLib certify --verified` applies that checker to a translation of an engine program. The second half, that a stratified program has
exactly one stable model and the engine computes it, is on paper (CERT-10).

What the checker does not establish: that the parser reads the file as the author meant; that the checker's own matching has no bug (it is
tested on 18 expanded libraries (5270 facts), on the paper's example 3 and on eleven kinds of faulty certificate; five faults injected by hand into the
checker were each caught by the tests); that attributes behave as intended. Attributes follow the engine's rule, that a premise matches a fact that has at least its attributes; the
checker restates that rule, so a change of the rule in the engine shows up as a disagreement.

## A defect the closure check found, and its fix

`Zil.Engine` used to close each stratum in at most 64 rounds (`fuel := 64`) and return what it had when the rounds ran out, without saying
so. A recursive rule that extends a path by one step each round, which is the usual way to write reachability, dependency or access
propagation along a chain, then missed everything past the 65th step. (Groups nested with the `#member` userset syntax are not affected:
the generated rule doubles the reach each round, so a depth of 70 takes about ten rounds.)

Measured before the fix, on a chain of 100 `next` edges with a base rule and a transitive rule:

* the closure had 4520 facts where 5150 follow; the 630 missing facts are all the `reaches` pairs more than 65 steps apart;
* `zil query-ci` reported `status pass`, and returned 65 nodes where 100 are reachable for "everything reachable from `n0`";
* `zilLib certify` reported `NOT certified` with the first rule instance whose head was missing.

The formal core spec (section 6.5) defines the result of a stratum as the least fixpoint, so the code did not compute what the spec says. With
negation the damage can go the other way: a lower stratum cut short leaves facts out, and a `NOT` over one of them then succeeds.

**Fixed in zil-lean `cdec3f2` (CERT-08).** The loops report whether they reached the fixpoint. `closureChecked`, `traceChecked` and what calls
them (provenance, `query-ci`, authorization, impact, query governance, agent context) fail with `closure did not reach its fixpoint in
stratum N within F rounds` instead of returning a partial closure. The default bound is `Zil.Engine.defaultFuel`, one million rounds; a
round that adds nothing still ends the loop, so a large bound costs nothing. `Zil.Engine.closure`, which cannot return an error, still
returns the facts so far when a caller's own bound runs out, and its comment says so. `Zil/Test/Fixpoint.lean` in zil-lean holds the
regression guards (a chain of 70 steps, an access rule over 70 services); they fail on the previous engine.

The report that the previous engine printed for `examples/certify/chain.zc` is kept in `test/fixtures/certify/`, and the checker still
refuses it. That is the test that the checker would have caught the defect, and it keeps meaning something after the engine is fixed.

**A second finding, also fixed (CERT-13, zil-lean `1614a4e`).** Building the trace took 12.8 s for 4520 facts, because the provenance builder
looked up every fact it added, and matched every premise, by scanning all the nodes. The checker needed 0.4 s for the same facts. The
builder now indexes its nodes by relation, subject and object, with the buckets in node-number order, so that it visits the candidates in the
order a scan did. It was checked by running `zil trace` before and after on every model of this repository and on its libraries expanded: the traces are
byte-identical, and the models that are refused are refused in the same way. A chain of 100 edges with transitive rules (5150 facts) takes
1.0 s where it took 44.3 s, and generated models of tens of thousands of facts that did not finish in 40 s now do.

## Targets

| Target | What | Status |
|---|---|---|
| CERT-01 | Soundness check of an ordered derivation graph, with negated conditions and the database | done 2026-10-23, `ZilLib/Certify/Check.lean` |
| CERT-02 | Closure check (the model check of the paper's section 5), including the database and no duplicate facts | done 2026-10-23; the chain of 70 edges, the 18 expanded libraries and the shop model |
| CERT-03 | Stratified negation: stratification checked independently of the engine; negation read against the set | done 2026-10-23 by the stable-model argument above; unproved |
| CERT-04 | A certificate read from text (`ZIL-PROVENANCE/1`), untrusted | done 2026-10-23, `ZilLib/Certify/Text.lean`, `zilLib certify MODEL TRACE` |
| CERT-05 | The proof graph stays small on the paper's example 3 (650 facts for a chain of 20; a tree has more than a million nodes) | done as a test |
| CERT-06 | Fault injection: eleven kinds of faulty certificate are refused by name; five faults injected by hand into the checker were each caught by the tests (not repeated by the gate) | done 2026-10-23 |
| CERT-07 | `zilLib certify` over the macro libraries as a test of the engine | done 2026-10-23 for the 18 rows of the matrix, each model read with its library (`--lib`); the libraries outside the matrix (`model-substrate`, `diff-patch`) are not covered |
| CERT-08 | The engine reaches the fixpoint or fails; no silent truncation (a change in `zil-lean`) | done 2026-10-23, zil-lean `cdec3f2`; the pin of this repository is there |
| CERT-09 | Certify one query's answers, including a negative answer ("this fact is not entailed"), from the closure | not started |
| CERT-10 | The semantics in Lean (ground programs, stable and perfect models) and a theorem that a passing check means the perfect model. Read `CertifyingDatalog` and its license before reusing any of it | partly done 2026-10-24, zil-lean `022896d`: models, derivations, least and stable models, the equivalence of the two semantics for a program without negation, and `checkCertificate_sound` and `checkCertificate_leastModel` for the Lean-embedded Datalog. Not done: that a stratified program has one stable model; that `unify` agrees with declarative matching; a proof about this repository's own checker |
| CERT-11 | A JSON encoding of certificates like the paper's, so that a trace from Nemo or Soufflé can be checked against a ZIL model; relations are ternary here (`subject#relation@object`) with attributes | not started |
| CERT-12 | Replay of an Apalache counterexample: the trace is mapped to a set of facts and checked with the same matching and closure functions (APL-22) | not started |
| CERT-13 | The provenance builder of the core is quadratic; an index brings it near the checker's cost | done 2026-10-23, zil-lean `1614a4e`; the traces of every model here are byte-identical before and after |
| CERT-14 | Read fact bases written as `zil_fact` lines (the line form of the Lean command) in `.zc` files, which the core's parser refuses | done 2026-10-23, `ZilLib/LeanFacts.lean`; a fact over several lines or a string with an escape is an error |
| CERT-15 | Run the proved checker on the engine's programs | done 2026-10-24, `ZilLib/Certify/Verified.lean` and `zilLib certify --verified`: the program and the certificate are translated to the Lean-embedded Datalog; the 18 expanded libraries and the tour model are accepted, and every fault the tests inject is refused |

## The note's targets, and ours

| The note | Where it stands |
|---|---|
| Target 1, universal check of file contracts over all structures up to a size | APL-30 (S1); `#zil_horn_grounding` is the concrete check it generalizes |
| Target 2, temporal governance and commutativity of operations | APL-31 and APL-32 (S2); commutativity is a new check on the operation semantics, to add after APL-31 |
| Target 3, zero-trust certification of solver output | APL-22 and CERT-12; only witnesses, as above |
| Target 4, stratified relational algebra with certificates | CERT-03, done in the form above; the relational-algebra operators (union, intersection, difference) are rules, so nothing more is needed |
| Target 5, equivalence of rule sets, non-interference | APL-33 for non-interference; equivalence of two programs over all databases up to a size is a new check on the same lowering (to add after APL-13) |
| Middle targets 1 and 2 | CERT-01 to CERT-04 here; the faster grounding of `#zil_horn_grounding` is a change in the core, not started |
| Middle targets 3 and 4 | APL-10 to APL-14 and APL-20 to APL-22 |
| Middle target 5, one-step induction | APL-41, done for TLA+ models (`zilLib apalache induct`) |
| Middle target 6, repair of rules from counterexamples, cardinality constraints | not started; cardinality needs the lowering to count |

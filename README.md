# zil-lib

[ZIL](https://github.com/jagg-ix/zil-lean) is a small declarative language for describing a system as facts, rules and queries. ZIL can
explain every derived fact: it records the rule and the facts that produced it, which is the fact's provenance. **zil-lib** is a
collection of reusable macro libraries for ZIL, plus a toolkit for checking ZIL models. This repository is separate from ZIL: it depends
on the ZIL core at a pinned commit, and the core has no dependency on it.

Licensed under the [Apache License 2.0](LICENSE).

- **`libsets/`**: opt-in macro libraries (model substrate, process algebra, proof evidence, discovery API, AWS, Souffle compatibility and
  more). Each is tested against reviewed golden files by `scripts/matrix.sh`. A library is loaded with the core's `--lib` flag.
- **The toolkit** (`ZilLib/`, in progress): model checking of ZIL models with [Apalache](https://apalache-mc.org), a symbolic model
  checker for TLA+. It checks rules, queries and administrative operations over all fact sets up to a bounded size and all operation
  sequences up to a bounded length, and replays every counterexample in the ZIL evaluator before reporting it. `docs/targets.md` is the
  work list, `docs/apalache-plan.md` the plan and `docs/tool-notes.md` the record of what was measured.

## Getting started

The prerequisites are `git` and [`elan`](https://github.com/leanprover/elan), which installs the Lean toolchain version that this
repository specifies. There are no other dependencies: no Java, Clojure or database.

```sh
git clone https://github.com/jagg-ix/zil-lib
cd zil-lib
lake build ZilLib zilLib zil-lean/zil zil-lean/zilTheoremAudit zil-lean/Zil
. examples/tour/helpers.sh
```

The first build compiles the ZIL core; it took about a minute on a laptop. While it builds, Lean prints deprecation warnings for the
core's source code. They do not affect the result.

The last command loads a few shell helper functions, which are all the tooling the tour needs:

```sh
zil()   { lake env zil "$@"; }
audit() { lake env zilTheoremAudit "$@"; }
zillib() { lake env zilLib "$@"; }

# query FILE NAME: print the result bindings of a query, one per line
query() { zil explain-query "$1" "$2" | awk -F'\t' '$1 == "witness" {print $3}'; }

# queries FILE NAME...: print the results of each query on one line, or (none)
queries() { local file="$1" name results; shift; for name in "$@"; do results="$(query "$file" "$name" | paste -sd' ' -)"; echo "$name: ${results:-(none)}"; done; }

# explain FILE NAME TEXT: print the derivation (provenance) of the first result whose binding contains TEXT:
# each rule that was applied, with the IDs of the facts it used
explain() { zil explain-query "$1" "$2" | awk -F'\t' -v pat="$3" '
  $1 == "witness" && goal == "" && index($3, pat) { goal = $4 }
  $1 == "origin" && $3 == "rule" { rule[$2] = $4; from[$2] = $5; args[$2] = $NF }
  function walk(id,  n, p, k) { if ((id in rule) && !(id in seen)) { seen[id] = 1; n = split(from[id], p, ","); for (k = 1; k <= n; k++) walk(p[k]) } }
  END { walk(goal); for (id = 0; id <= goal; id++) if (id in seen) printf "%2s  %-16s from %-4s %s\n", id, rule[id], from[id], args[id] }'; }

# audit_summary MODEL: print one line per theorem from the audit: status, name, and its proof or the failure reason
# (the audit exits with status 1 when a theorem fails, so that exit status is ignored here)
audit_summary() { { audit "$1" - || true; } | awk -F'\t' '$1 == "theorem" {printf "%s  %s  %s\n", $3, $2, ($NF == "" ? $(NF - 1) : "reason: " $NF)}'; }
```

## A tour of ZIL: one small shop, four questions

All files are in [`examples/tour/`](examples/tour). The shop is a synthetic example, and each question exercises a different feature of
ZIL. The outputs on this page are real: `scripts/test-tour.sh` runs every command shown here and fails if its output differs from what
the page shows.

### 1. Which user journeys are affected when a service fails?

This question needs only the ZIL core, with no library. A fact is a relation tuple of the form `subject#relation@object`. The facts below
describe a service call graph, the entry point of each user journey, and which service has a fallback:

```zil
// Who calls whom.
service:web#calls@service:checkout.
service:checkout#calls@service:payments.
service:checkout#calls@service:inventory.
service:payments#calls@service:card_gateway.
service:inventory#calls@service:warehouse_db.
service:reports#calls@service:warehouse_db.

// What a customer does starts at one service. Only one dependency has a fallback.
journey:buy#starts_at@service:web.
journey:browse_reports#starts_at@service:reports.
service:warehouse_db#has_fallback@value:true.
```

Rules derive new facts from existing ones. A rule has an `IF` part (the premises) and a `THEN` part (the conclusion), and `?x` denotes a
variable:

```zil
RULE depends_directly:
IF ?a#calls@?b
THEN ?a#depends_on@?b.

RULE depends_through:
IF ?a#depends_on@?b AND ?b#calls@?c
THEN ?a#depends_on@?c.

// A journey is exposed to everything its first service depends on.
RULE journey_exposed:
IF ?j#starts_at@?s AND ?s#depends_on@?x
THEN ?j#exposed_to@?x.

// Exposed to a service that has no fallback: a single point of failure.
RULE single_point:
IF ?j#exposed_to@?x AND NOT ?x#has_fallback@value:true
THEN ?j#single_point_of_failure@?x.
```

Two features are worth noting. `depends_through` is recursive: its conclusion (`depends_on`) is also one of its premises, so the engine
computes the transitive closure of the call graph by applying the rules until no new facts are derived. `single_point` uses negation
(`NOT`): its last premise holds only when `has_fallback` cannot be derived for that service (negation as failure).

Run the queries:

```sh
query examples/tour/01-blast-radius.zc what_breaks_if_payments_is_down
```

```text
j=journey.buy
```

```sh
query examples/tour/01-blast-radius.zc single_points
```

```text
j=journey.buy,x=service.checkout
j=journey.buy,x=service.payments
j=journey.buy,x=service.inventory
j=journey.buy,x=service.card_gateway
```

`service.warehouse_db` is not in the result: the `buy` journey depends on it transitively (through `inventory`), but it has a fallback.

To see why the card gateway is reported as a single point of failure, print its derivation. Every derived fact records the rule that
produced it and the facts that rule used (its provenance):

```sh
explain examples/tour/01-blast-radius.zc single_points x=service.card_gateway
```

```text
 9  depends_directly from 0    a=service.web,b=service.checkout
15  depends_through  from 9,1  a=service.web,b=service.checkout,c=service.payments
23  depends_through  from 15,3 a=service.web,b=service.payments,c=service.card_gateway
25  journey_exposed  from 6,23 j=journey.buy,s=service.web,x=service.card_gateway
30  single_point     from 25   j=journey.buy,x=service.card_gateway
```

Reading the derivation from top to bottom: `web` calls `checkout` (input fact 0), so `web` depends on `checkout` (derived fact 9).
Through `payments` (15) that extends to `card_gateway` (23). The `buy` journey starts at `web`, so it is exposed to the gateway (25), and
because the gateway has no fallback, it is a single point of failure (30). The numbers are fact IDs; IDs that are not listed (0, 1, 3
and 6) are input facts that you wrote.

The same program can be compiled to a Lean source file:

```sh
zil compile examples/tour/01-blast-radius.zc /tmp/Blast.lean Tour.Blast
lake env lean /tmp/Blast.lean
grep 'def sourceProgram' /tmp/Blast.lean
```

```text
def sourceProgram : Zil.Program := {
```

Lean type-checks the file without errors. The file defines the program as a Lean value (`Zil.Program`), so Lean theorems can refer to
it. Question 4 uses Lean to check a proof.

### 2. Is the design consistent across its specifications?

A system design is usually spread over several artifacts: a state machine describes its structure and behavior, use cases describe its
requirements, and test scenarios describe its verification. Nothing forces them to stay consistent. The `model-substrate` library puts all
three in one vocabulary, so that inconsistencies can be found with queries.

A library is a set of macros, and a macro invocation expands to a set of facts and rules. For example, `USE MODEL_STATE(paid, order)` is
a macro invocation. The checkout model below has three parts: structure (a state machine), intent (actors and use cases) and scenarios
(tests):

```zil
// Structure: an order moves through three states.
USE MODEL_ENTITY(order).
USE MODEL_OP(order_place, order).
USE MODEL_OP(order_pay, order).
USE MODEL_OP(order_ship, order).
USE MODEL_STATE(cart, order).
USE MODEL_STATE(placed, order).
USE MODEL_STATE(paid, order).
USE MODEL_STATE(shipped, order).
USE MODEL_INITIAL(cart).
USE MODEL_TRANS(place, cart, submit, placed).
USE MODEL_TRANS(pay, placed, charge, paid).
USE MODEL_TRANS(ship, paid, dispatch, shipped).
```

```zil
// Intent: who wants what.
USE MODEL_ACTOR(shopper).
USE MODEL_ACTOR(warehouse).
USE MODEL_USECASE(place_order).
USE MODEL_USECASE(pay_for_order).
USE MODEL_USECASE(ship_order).
USE MODEL_PARTICIPATES(shopper, place_order).
USE MODEL_PARTICIPATES(shopper, pay_for_order).
USE MODEL_PARTICIPATES(warehouse, ship_order).
```

```zil
// Scenarios: how it is tested. Three steps, in order.
USE SCENARIO_FEATURE(f_checkout, place_order).
USE SCENARIO_CASE(s_happy_path, f_checkout).
USE SCENARIO_GIVEN(g1, s_happy_path, 1, cart_has_items).
USE SCENARIO_WHEN(w1, s_happy_path, 2, shopper_submits).
USE SCENARIO_THEN(t1, s_happy_path, 3, order_is_placed).
USE SCENARIO_THEN(t2, s_happy_path, 4, confirmation_email_is_sent).

// Links between them.
USE MODEL_COVERED_BY(place_order, s_happy_path).
USE MODEL_COVERED_BY(pay_for_order, s_happy_path).
USE SCENARIO_REALIZES(w1, order_place).
USE SCENARIO_REALIZES(t1, place).
```

Expand the macros with the library on the library path. (`explain-query` has no `--lib` option, so the file is expanded first.) The 31
`USE` directives expand to 98 lines of facts and rules:

```sh
grep -c '^USE' examples/tour/02-design-coherence.zc
zil expand examples/tour/02-design-coherence.zc /tmp/design.zc --lib libsets/model-substrate
awk 'END {print NR}' /tmp/design.zc
```

```text
31
98
```

The library defines three consistency queries: use cases that no test covers, test scenarios that are not linked to the model, and
`Then` steps that realize no operation or transition of the model:

```sh
queries /tmp/design.zc c_uncovered_usecases c_orphan_scenarios c_unrealized_then_steps
```

```text
c_uncovered_usecases: uc=ship_order
c_orphan_scenarios: (none)
c_unrealized_then_steps: st=t2
```

The queries report two defects, found by static analysis without running any code. No test covers the `ship_order` use case, and the
step "confirmation email is sent" does not correspond to any operation in the model. `02-design-coherence-fixed.zc` fixes both by adding
a shipping test and a `send_confirmation` operation. The `diff` between the two files:

```sh
diff examples/tour/02-design-coherence.zc examples/tour/02-design-coherence-fixed.zc || true
```

```text
1c1
< MODULE tour.design.coherence.
---
> MODULE tour.design.coherence.fixed.
9a10
> USE MODEL_OP(send_confirmation, order).
36a38,43
> USE SCENARIO_FEATURE(f_fulfilment, ship_order).
> USE SCENARIO_CASE(s_ship_it, f_fulfilment).
> USE SCENARIO_GIVEN(g2, s_ship_it, 1, order_is_paid).
> USE SCENARIO_WHEN(w2, s_ship_it, 2, warehouse_dispatches).
> USE SCENARIO_THEN(t3, s_ship_it, 3, order_is_shipped).
> 
41a49,52
> USE SCENARIO_REALIZES(t2, send_confirmation).
> USE MODEL_COVERED_BY(ship_order, s_ship_it).
> USE SCENARIO_REALIZES(w2, order_ship).
> USE SCENARIO_REALIZES(t3, ship).
```

```sh
zil expand examples/tour/02-design-coherence-fixed.zc /tmp/design-fixed.zc --lib libsets/model-substrate
queries /tmp/design-fixed.zc c_uncovered_usecases c_orphan_scenarios c_unrealized_then_steps
```

```text
c_uncovered_usecases: (none)
c_orphan_scenarios: (none)
c_unrealized_then_steps: (none)
```

### 3. Were events recorded in the required order?

Services that do not share a clock cannot always tell which of two events happened first. The `process-algebra` library models vector
clocks and derives the happened-before order from them. Each service counts its own events (`c1` < `c2` < `c3`), and each event carries a
vector clock: the counter value of every service whose clock it includes:

```zil
USE VC_COMPONENT(order_placed, shop, c1).
USE VC_COMPONENT(payment_captured, shop, c2).
USE VC_COMPONENT(shipment_dispatched, shop, c3).
USE VC_COMPONENT(shipment_dispatched, carrier, c1).
USE VC_COMPONENT(delivered, carrier, c2).
USE VC_COMPONENT(refund_issued, shop, c1).      // logged before the capture: the clocks disagree
USE VC_COMPONENT(invoice_sent, accounting, c1).  // never saw the shop's clock: nothing links it
```

Next, the required ordering constraints (the first event must happen before the second):

```zil
// What the business requires.
USE VC_REQUIRE_BEFORE(order_placed, payment_captured).
USE VC_REQUIRE_BEFORE(payment_captured, shipment_dispatched).
USE VC_REQUIRE_BEFORE(shipment_dispatched, delivered).
USE VC_REQUIRE_BEFORE(payment_captured, refund_issued).
USE VC_REQUIRE_BEFORE(payment_captured, invoice_sent).
```

The library reports which constraints are satisfied (`order_kept`) and which are broken (`order_broken`). The two rules below split the
broken constraints into two classes that need different follow-up: *contradicted*, where the vector clocks show the opposite order, and
*unproven*, where the clocks are concurrent or incomplete, so neither order can be established:

```zil
// Two ways to fail: the clocks contradict the order, or nothing proves it.
RULE order_contradicted:
IF ?a#must_precede@?b AND ?a#violation@?b
THEN ?a#order_contradicted@?b.

RULE order_unproven:
IF ?a#order_broken@?b AND NOT ?a#order_contradicted@?b
THEN ?a#order_unproven@?b.
```

```sh
zil expand examples/tour/03-event-order.zc /tmp/order.zc --lib libsets/process-algebra
for q in orders_kept orders_contradicted orders_unproven; do echo "$q:"; query /tmp/order.zc $q | sed 's/^/  /'; done
```

```text
orders_kept:
  a=vc.event.order_placed,b=vc.event.payment_captured
  a=vc.event.payment_captured,b=vc.event.shipment_dispatched
  a=vc.event.shipment_dispatched,b=vc.event.delivered
orders_contradicted:
  a=vc.event.payment_captured,b=vc.event.refund_issued
orders_unproven:
  a=vc.event.payment_captured,b=vc.event.invoice_sent
```

The refund's vector clock says it happened before the payment it refunds, which contradicts the constraint. The invoice's vector clock is
concurrent with the payment's, because the accounting service never observed the shop's clock, so the data neither confirms nor contradicts
the constraint. Reporting both as a generic ordering violation would send the investigation in the wrong direction.

### 4. Requiring a proof for a critical claim

ZIL can represent a claim as data: a theorem with its assumptions, its guarantee and its criticality.

```zil
// A claim about the checkout, written as data.
assumption:percentIsAtMost100#kind@entity:assumption.
lemma:subtractionNeverGrows#kind@entity:lemma.

theorem:discountNeverExceedsPrice#kind@entity:theorem.
theorem:discountNeverExceedsPrice#requires_assumption@assumption:percentIsAtMost100.
theorem:discountNeverExceedsPrice#requires_lemma@lemma:subtractionNeverGrows.
theorem:discountNeverExceedsPrice#ensures@guarantee:totalIsNeverAbovePrice.
theorem:discountNeverExceedsPrice#criticality@value:high.
```

The `proof-evidence` library provides a macro that links a theorem to the Lean theorem that proves it:

```zil
MACRO LEAN_PROOF(theorem, lean_name):
EMIT theorem:{{theorem}}#proof_token@proof:{{lean_name}}.
EMIT proof:{{lean_name}}#kind@entity:proof.
EMIT proof:{{lean_name}}#engine@engine:lean4.
ENDMACRO.
```

The last two lines of `examples/tour/04-claims-need-proofs.zc` use this macro to name the Lean theorem that proves the claim. The ZIL core
includes a theorem audit that fails a high-criticality theorem when it has no proof evidence. The `audit_summary` helper prints one line
per theorem (`audit` prints the full report). Run the audit on the file with and without those two lines:

```sh
zil expand examples/tour/04-claims-need-proofs.zc /tmp/claims.zc --lib libsets/proof-evidence
audit_summary /tmp/claims.zc
```

```text
pass  theorem.discountNeverExceedsPrice  proof.ZilLib.Tour.discounted_le
```

```sh
grep -v '^USE LEAN_' examples/tour/04-claims-need-proofs.zc > /tmp/claims-bare.zc
zil expand /tmp/claims-bare.zc /tmp/claims-bare.expanded.zc --lib libsets/proof-evidence
audit_summary /tmp/claims-bare.expanded.zc
```

```text
fail  theorem.discountNeverExceedsPrice  reason: proof-evidence-missing
```

The audit only checks that a proof is *referenced*. Whether the referenced theorem actually proves the claim is checked by Lean. The
theorem is in this repository ([`ZilLib/Tour.lean`](ZilLib/Tour.lean)) and is compiled with the library:

```lean
/-- Taking a percentage off a price never gives more than the price. -/
theorem discounted_le (price pct : Nat) (_h : pct ≤ 100) : price * (100 - pct) / 100 ≤ price := by
  apply Nat.div_le_of_le_mul
  calc price * (100 - pct) ≤ price * 100 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 100 * price := Nat.mul_comm _ _
```

To see which axioms the proof depends on, ask Lean:

```sh
printf 'import ZilLib.Tour\n#print axioms ZilLib.Tour.discounted_le\n' | lake env lean --stdin
```

```text
'ZilLib.Tour.discounted_le' depends on axioms: [propext]
```

The proof depends only on `propext` (propositional extensionality), one of Lean's standard axioms. In summary: the claim is data, the
proof is checked by the Lean kernel, and the audit rejects a high-criticality claim that references no proof. One link is not verified by
any of these tools: that the name referenced in the ZIL file is the name of an existing Lean theorem. Enforce that in your own CI, for
example with a `#check` command for each referenced proof name.

### Summary of the features used

| ZIL feature | Seen in |
|---|---|
| facts, rules, queries, and recursive rules | 1 |
| negation (`NOT`) | 1, 2, 3 |
| provenance (the derivation of each result) | 1 |
| macros and libraries (`USE`, `--lib`) | 2, 3, 4 |
| compilation to Lean source | 1 |
| theorem claims, proof evidence and the theorem audit | 4 |

## Writing your own library

A library is a directory of `.zc` files that contain `MACRO` definitions; `--lib DIR` makes them available. A macro consists of a name, a
parameter list and a template of facts to emit (the `LEAN_PROOF` macro in question 4 is a complete example). To write your own, copy one
of the small libraries in `libsets/` (`proof-evidence` is 21 lines) into a new directory, edit it, and run
`zil expand FILE - --lib YOUR_DIR`.

## Checking TLA+ models with Apalache

[Apalache](https://apalache-mc.org) is a symbolic model checker for TLA+. The toolkit runs it, reads the counterexamples it writes, records
each run as evidence, and checks whether an invariant is inductive. The tool is not part of this repository and is never downloaded. It is
looked up in `$APALACHE_HOME/bin` and then on `PATH`, and it needs a Java runtime. When the tool is missing, the commands say so and exit
with status 3. The test suite never starts it unless you pass `--with-tool`.

```bash
export APALACHE_HOME=/path/to/apalache-0.62.4    # or put apalache-mc on PATH
```

The example is an invented model of two counters that are meant to move together (`test/fixtures/apalache/LockStep.tla`). Every variable and
constant has a type annotation in a comment, which Apalache requires:

```tla
CInit == Max = 5 /\ Fault = FALSE
CInitFault == Max = 5 /\ Fault = TRUE
Init == a = 0 /\ b = 0
Next ==
  /\ a < Max
  /\ a' = a + 1
  /\ b' = IF Fault THEN b + 2 ELSE b + 1
\* True in every reachable state, but not inductive: from a = 0 and b = Max one step reaches b = Max + 1.
Bounded == b <= Max
\* The conjunct that is missing: the counters move together.
InStep == a = b
IndInv == Bounded /\ InStep
\* The states to step from, in assignment form: each variable ranges over its type.
WeakInit == a \in 0..Max /\ b \in 0..Max /\ Bounded
StrongInit == a \in 0..Max /\ b \in 0..Max /\ IndInv
```

### A bounded check

`check` looks for a violation in every execution of up to the given number of steps. Here the invariant `Bounded` holds for five steps:

```sh
zillib apalache check test/fixtures/apalache/LockStep.tla --cinit CInit --inv Bounded --length 5 | grep -v -e '^tool:' -e '^output:'
```

```text
no violation of Bounded in any execution of 5 steps.
This says nothing about longer executions, and nothing about other constants.
```

With the defect switched on (`CInitFault`), the counters drift apart at the first step, and the tool returns a counterexample:

```sh
zillib apalache check test/fixtures/apalache/LockStep.tla --cinit CInitFault --inv InStep --length 3 > /tmp/check.txt || echo "exit status $?"
grep -v -e '^tool:' -e '^output:' /tmp/check.txt
```

```text
exit status 1
InStep is violated. The counterexample:
State 0
  Fault = TRUE
  Max = 5
  a = 0
  b = 0
State 1
  Fault = TRUE
  Max = 5
  a = 1
  b = 2
```

A pass is evidence for the stated number of steps and the stated constants. It says nothing about longer executions or other constants. By
default the tool also reports a state without a successor as a deadlock; `--no-deadlock` turns that off.

### An inductive invariant

An invariant is *inductive* when every initial state satisfies it and every step from a state that satisfies it leads to a state that
satisfies it. An inductive invariant holds in every reachable state, however long the execution. `induct` checks both cases. For the step it
needs a predicate in assignment form that describes the states to step from: each variable ranges over its type, and the invariant holds.
In `LockStep.tla` these are `WeakInit` and `StrongInit`.

`Bounded` is true in every reachable state, but it is not inductive on its own. The tool finds a state that satisfies it and leaves it after
one step (the counter `a` is still at 0 while `b` has already reached its maximum):

```sh
zillib apalache induct test/fixtures/apalache/LockStep.tla --cinit CInit --indinit WeakInit --inv Bounded > /tmp/weak.txt || echo "exit status $?"
grep -v -e '^tool:' -e '^output:' /tmp/weak.txt
```

```text
exit status 1
Bounded: not inductive. The state below satisfies WeakInit and leaves Bounded after one step.
A counterexample to induction is a finding, not a defect: the state may be unreachable, and the invariant may need a stronger conjunct.
State 0
  Fault = FALSE
  Max = 5
  a = 0
  b = 5
State 1
  Fault = FALSE
  Max = 5
  a = 1
  b = 6
```

That state may be unreachable, so a counterexample to induction is a finding and not a defect of the model. It points at the missing
conjunct: the counters must be equal. With `InStep` added, the invariant is inductive at these constants:

```sh
zillib apalache induct test/fixtures/apalache/LockStep.tla --cinit CInit --indinit StrongInit --inv IndInv | grep -v -e '^tool:' -e '^output:'
```

```text
IndInv: inductive at the constants that were set. Both cases passed.
This holds for these constants only. It is not a proof for other sizes.
```

This holds for `Max = 5` only. A statement for every value of `Max` needs a proof outside the tool. With the defect switched on, the step
fails even for the strengthened invariant, which shows that the check can fail.

### Evidence

`--evidence FILE` writes the run as a `ZIL-EVIDENCE/1` envelope. The producer is outside Lean, so the authority is `external` and the
assurance is `externally-attested`. The identity of the envelope covers the model, the modules it extends, the request and the version of the
tool, so changing any of them changes it. A run that times out is recorded as inconclusive, never as a pass, and a run that the tool rejects
has no envelope.

```sh
zillib apalache induct test/fixtures/apalache/LockStep.tla --cinit CInit --indinit StrongInit --inv IndInv --evidence /tmp/evidence.json > /dev/null
python3 -I -c 'import json, sys; e = json.load(open(sys.argv[1])); p = json.loads(e["payload"]); print(e["authority"], e["assurance"]); print(p["verdict"]); print(p["statement"])' /tmp/evidence.json
```

```text
external externally-attested
inductive-at-the-constants
IndInv holds in every initial state and is preserved by every step from StrongInit, so it holds in every reachable state at the constants set by CInit and at no other constants
```

### Exit codes

| Exit status | Meaning |
|---|---|
| 0 | no violation within the bound, or the invariant is inductive at the constants |
| 1 | an invariant is violated, a state has no successor (a deadlock), or the invariant is not inductive |
| 2 | the tool rejected the input or failed, or the command line was wrong |
| 3 | there is no tool |
| 4 | the deadline passed, so the result is inconclusive |

`zilLib apalache trace FILE.itf.json` prints a trace file written by the tool, one state after the other.

## Repository layout

| Path | What |
|---|---|
| `lakefile.lean` | the Lake package definition and the dependency pin: `require «zil-lean»` at one full commit |
| `ZilLib/` | the Lean library; `Model.lean` reads a model with the core's parser |
| `ZilLib/CLI/Main.lean` | the `zilLib` executable (`zilLib summary <model.zc>`, `zilLib apalache ...`) |
| `ZilLib/Tour.lean` | the Lean theorem used in question 4 of the tour |
| `ZilLib/Apalache/` | running Apalache: `Itf.lean` reads its traces, `Run.lean` finds and runs it, `Evidence.lean` records a run, `Induct.lean` checks that an invariant is inductive |
| `ZilLib/CLI/ApalacheCommands.lean` | the `zilLib apalache` commands |
| `examples/tour/` | the four example models of the tour and the shell helper functions |
| `scripts/test.sh` | the test suite (CI gate) |
| `scripts/test-tour.sh` | runs every command in the tour and compares its output with this README |
| `test/fixtures/apalache/` | traces and models the tool wrote or that were written for it, and a stand-in tool for tests that must not start a JVM |
| `docs/targets.md` | the work list for the Apalache toolkit |
| `docs/move-libsets.md` | the plan for moving the macro libraries here (completed) |

## Build and test

The requirements are `lake` and `git`; `elan` installs the Lean toolchain named in `lean-toolchain`:

```sh
scripts/test.sh
lake exe zilLib summary examples/tiny.zc
```

The test suite puts stub `java`, `apalache-mc` and `clojure` programs that always fail first on `PATH`, which shows that none of them is
needed to build or test. Apalache is a Java program; it is looked up at run time, and only by features that use it. Add `--full` to also
run the library tests, which takes about ten minutes.

## Libraries

Opt-in macro libraries, loaded with `--lib`. Each one is covered by a golden-file test in the test matrix (`scripts/matrix.sh`) unless
noted otherwise.

| Library | Adds | Tested by (matrix row: model) |
|---|---|---|
| `libsets/aws-model` | a reusable AWS modeling layer: baseline catalog entities (service, region, control), compatibility targets and gap checks | `aws-model`: `examples/aws-model-extension-with-icons.zc` |
| `libsets/aws-namespace` | the AWS layer with namespace-scoped compatibility | `aws-namespace`: `examples/aws-namespace-compat.zc` |
| `libsets/aws-transfer-family` | the AWS Transfer Family domain: the resources of its API reference | `aws-transfer-family`: `examples/generated/tf_api_model.zc` |
| `libsets/bitemporal` | a bitemporal layer (valid time and transaction time) | `bitemporal`: `examples/bitemporal-history-replay.zc` |
| `libsets/config-declarative` | a declarative configuration layer | `config-declarative`: `examples/config-declarative-macros.zc` |
| `libsets/diff-patch` | structural diffs and patchsets (not in the matrix: its rules spell variables as typed names and need a redesign) | no test yet |
| `libsets/discovery-api` | rules and queries over a Discovery-style API description (methods, schemas, fields, references) | `discovery-api`: `examples/discovery-api/sample-model.zc` |
| `libsets/everparse-interop` | an EverParse interoperability layer | `everparse-interop`: `examples/everparse-interop-demo.zc` |
| `libsets/k8s-helm-compat` | Kubernetes CRD and Helm compatibility modeling | `k8s-helm-compat`: `examples/k8s-helm-compat.zc` |
| `libsets/model-substrate` | a shared vocabulary for structure, requirements and test scenarios, with consistency queries | `scripts/test-model-substrate.sh` |
| `libsets/namespace-pn-nd` | namespace hierarchy, n-dimensional context products, category-style morphism reachability and Petri-net style resolution flow | `namespace-pn-nd`: `examples/namespace-pn-nd-extension.zc` |
| `libsets/org-pn-nd` | an organization, Petri net and n-dimensional embedding layer | `org-pn-nd`: `examples/org-pn-nd-embedding.zc` |
| `libsets/process-algebra` | process-algebra constructs: temporal prefixes, pi-calculus hand-offs, vector clocks with required orderings, and a discrete clock with time windows | `process-algebra`: `examples/process-algebra-checks.zc` |
| `libsets/proof-evidence` | `LEAN_PROOF` and `LEAN_LEMMA_PROOF`, the proof-evidence form that `theorem-audit` reads | `proof-evidence`: `examples/proof-evidence/contracts.zc` |
| `libsets/rbac-dac` | discretionary access control (owner grants) combined with role-based access control | `rbac-dac`: `examples/rbac-dac-orange-book.zc` |
| `libsets/request-form` | requests for data, effectful actions, compounds and recursive structures | `request-form`: `examples/request-form-recursive.zc` |
| `libsets/souffle-compat` | relations and facts in the form a Souffle program uses | `souffle-compat`: `examples/souffle-transitive-closure.zc` |
| `libsets/theorem-dsl-ci` | theorem, category-theory and theorem-impact DSLs | `category-theory`: `examples/lean4-integration/category-theory-spec.zc`, `theorem-dsl`: `examples/theorem-dsl-incident.zc`, `theorem-impact`: `examples/theorem-impact-devops-sre.zc` |

## Updating the pinned core

Edit the commit in `lakefile.lean`, run `lake update zil-lean`, and then run `scripts/test.sh`. The test suite checks that
`lakefile.lean` and `lake-manifest.json` name the same full commit.

## Project rules

- This repository makes no changes to the core, and the core's build and tests never need Apalache, Java or any other external tool.
- The macro libraries live in `libsets/`; they were moved here from the core (see `docs/move-libsets.md`). The vocabulary for declaring
  what to check (bounds, invariants, public projections, operations) is planned as another library.
- A bounded model-checking result is evidence up to its stated bounds, not a proof for all sizes.
- All examples are synthetic. No content from a private system is included, and the core's `PUBLIC-CONTENT-POLICY.md` applies.

## License

This project is licensed under the [Apache License 2.0](LICENSE), including the tour examples and everything in `libsets/`.
Contributions are accepted under the same license (section 5 of the license).

# zil-lib

[ZIL](https://github.com/jagg-ix/zil-lean) is a small language for writing down facts, rules and questions about a system, and getting
answers that show their work. **zil-lib** is a set of ready-made macro libraries for ZIL, and a toolkit that checks ZIL models. This
repository is not part of ZIL: it depends on the ZIL core at a pinned commit, and the core knows nothing of it.

Licensed under the [Apache License 2.0](LICENSE).

- **`libsets/`**: opt-in macro libraries (model substrate, process algebra, proof evidence, discovery API, AWS, Souffle compatibility and
  more), each qualified against a reviewed golden output by `scripts/matrix.sh`. A library is used with the core's `--lib` flag.
- **The toolkit** (`ZilLib/`, started): checking ZIL models with [Apalache](https://apalache-mc.org), a symbolic model checker for TLA+: rules,
  queries and administrative operations over all fact sets of a bounded size and all operation sequences of a bounded length, with every
  counterexample replayed by the ZIL evaluator before it is reported. `docs/targets.md` is the work list, `docs/apalache-plan.md` the plan and
  `docs/tool-notes.md` what was measured.

## Try it

You need `git` and [`elan`](https://github.com/leanprover/elan), which installs the Lean version this repository asks for. Nothing else:
no Java, no Clojure, no database.

```sh
git clone https://github.com/jagg-ix/zil-lib
cd zil-lib
lake build ZilLib zil-lean/zil zil-lean/zilTheoremAudit zil-lean/Zil
. examples/tour/helpers.sh
```

The first build compiles the ZIL core; on a laptop it took about a minute. Lean prints warnings about functions that newer toolchains have deprecated
in the core while it builds; they do not change the result.

The last line loads a few small shell helpers. Read them once; they are all the tooling the tour uses:

```sh
zil()   { lake env zil "$@"; }
audit() { lake env zilTheoremAudit "$@"; }

# ask FILE QUERY: the answers to a query, one per line
ask()   { zil explain-query "$1" "$2" | awk -F'\t' '$1 == "witness" {print $3}'; }

# answers FILE QUERY...: the answers to each query on one line, or (none)
answers() { local file="$1" q found; shift; for q in "$@"; do found="$(ask "$file" "$q" | paste -sd' ' -)"; echo "$q: ${found:-(none)}"; done; }

# why FILE QUERY TEXT: how the first answer containing TEXT was derived: each rule that fired, and the facts it used
why()   { zil explain-query "$1" "$2" | awk -F'\t' -v pat="$3" '
  $1 == "witness" && goal == "" && index($3, pat) { goal = $4 }
  $1 == "origin" && $3 == "rule" { rule[$2] = $4; from[$2] = $5; args[$2] = $NF }
  function walk(id,  n, p, k) { if ((id in rule) && !(id in seen)) { seen[id] = 1; n = split(from[id], p, ","); for (k = 1; k <= n; k++) walk(p[k]) } }
  END { walk(goal); for (id = 0; id <= goal; id++) if (id in seen) printf "%2s  %-16s from %-4s %s\n", id, rule[id], from[id], args[id] }'; }

# verdict MODEL: the audit's one line per theorem: its status, its name, and its proof or the reason it failed
# (the audit exits 1 when a claim fails; the line says so, so the exit status is dropped here)
verdict() { { audit "$1" - || true; } | awk -F'\t' '$1 == "theorem" {printf "%s  %s  %s\n", $3, $2, ($NF == "" ? $(NF - 1) : "reason: " $NF)}'; }
```

## A tour: one small shop, four questions

Everything below is in [`examples/tour/`](examples/tour). The shop is invented, and each question needs a different part of ZIL. The
outputs are real: `scripts/test-tour.sh` runs every command on this page and fails if the output on the page is different.

### 1. If a service goes down, which customer journeys break?

This one needs only the ZIL core. A fact is `subject#relation@object`. Write down who calls whom, and where each customer journey starts:

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

Then say what follows from the facts. A rule has an `IF` side and a `THEN` side, and `?x` is a variable:

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

Look at what these four rules do. `depends_through` uses its own conclusion (`depends_on`) as a premise, so a chain of calls of any length is
followed until nothing new turns up. And `single_point` says `NOT`: a journey is exposed with no safety net.

Ask the questions:

```sh
ask examples/tour/01-blast-radius.zc what_breaks_if_payments_is_down
```

```text
j=journey.buy
```

```sh
ask examples/tour/01-blast-radius.zc single_points
```

```text
j=journey.buy,x=service.checkout
j=journey.buy,x=service.payments
j=journey.buy,x=service.inventory
j=journey.buy,x=service.card_gateway
```

`service.warehouse_db` is not in the list: the `buy` journey depends on it (through `inventory`), but it has a fallback.

Now ask *why* the card gateway is a single point of failure. Every derived fact remembers the rule that produced it and the facts it used:

```sh
why examples/tour/01-blast-radius.zc single_points x=service.card_gateway
```

```text
 9  depends_directly from 0    a=service.web,b=service.checkout
15  depends_through  from 9,1  a=service.web,b=service.checkout,c=service.payments
23  depends_through  from 15,3 a=service.web,b=service.payments,c=service.card_gateway
25  journey_exposed  from 6,23 j=journey.buy,s=service.web,x=service.card_gateway
30  single_point     from 25   j=journey.buy,x=service.card_gateway
```

Read it from the top: `web` calls `checkout` (a fact you wrote, number 0), so `web` depends on it (9); through `payments` (15) and on to
the `card_gateway` (23); the `buy` journey starts at `web`, so it is exposed (25); and nothing gives the gateway a fallback, so it is a
single point (30). The numbers are fact numbers; the ones that are not listed are your own input facts.

The same program is also a Lean file:

```sh
zil compile examples/tour/01-blast-radius.zc /tmp/Blast.lean Tour.Blast
lake env lean /tmp/Blast.lean
grep 'def sourceProgram' /tmp/Blast.lean
```

```text
def sourceProgram : Zil.Program := {
```

Lean accepts the file without a word. It holds the program as a Lean value, so a Lean theorem can talk about it; question 4 uses that
side of the toolkit.

### 2. Does the design agree with itself?

Real designs live in several places at once: a state machine says what the system *is*, use cases say what people *want*, and test
scenarios say what is *checked*. Nothing makes them agree. The `model-substrate` library gives all three one vocabulary, so that
disagreement becomes a query.

A library is a set of macros, and a macro is one line that stands for many facts. `USE MODEL_STATE(paid, order)` is one such line.
The shop's checkout, in three groups of them:

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

Expand it with the library on the path. `explain-query` reads a plain file, so the macros are expanded first. Thirty-one lines of `USE`
become 98 lines of facts and rules:

```sh
grep -c '^USE' examples/tour/02-design-coherence.zc
zil expand examples/tour/02-design-coherence.zc /tmp/design.zc --lib libsets/model-substrate
awk 'END {print NR}' /tmp/design.zc
```

```text
31
98
```

Now the three coherence questions the library defines: which use cases have no test, which tests belong to no use case, and which test
steps check something no operation of the model does:

```sh
answers /tmp/design.zc c_uncovered_usecases c_orphan_scenarios c_unrealized_then_steps
```

```text
c_uncovered_usecases: uc=ship_order
c_orphan_scenarios: (none)
c_unrealized_then_steps: st=t2
```

Two real holes, found without running the shop. Nobody tests `ship_order`, and the step "confirmation email is sent" checks something no
operation of the model does. `02-design-coherence-fixed.zc` closes both: a test for shipping, and an operation for the email. What changed:

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
answers /tmp/design-fixed.zc c_uncovered_usecases c_orphan_scenarios c_unrealized_then_steps
```

```text
c_uncovered_usecases: (none)
c_orphan_scenarios: (none)
c_unrealized_then_steps: (none)
```

### 3. Did the events happen in the order the business requires?

Services that do not share a clock cannot tell which of two events came first. The `process-algebra` library keeps a vector clock per
event and works out the order from those. Each service numbers its own events (`c1` is before `c2`, which is before `c3`), and an event
lists the number each service had reached when it saw it:

```zil
USE VC_COMPONENT(order_placed, shop, c1).
USE VC_COMPONENT(payment_captured, shop, c2).
USE VC_COMPONENT(shipment_dispatched, shop, c3).
USE VC_COMPONENT(shipment_dispatched, carrier, c1).
USE VC_COMPONENT(delivered, carrier, c2).
USE VC_COMPONENT(refund_issued, shop, c1).      // logged before the capture: the clocks disagree
USE VC_COMPONENT(invoice_sent, accounting, c1).  // never saw the shop's clock: nothing links it
```

Then what the business requires:

```zil
// What the business requires.
USE VC_REQUIRE_BEFORE(order_placed, payment_captured).
USE VC_REQUIRE_BEFORE(payment_captured, shipment_dispatched).
USE VC_REQUIRE_BEFORE(shipment_dispatched, delivered).
USE VC_REQUIRE_BEFORE(payment_captured, refund_issued).
USE VC_REQUIRE_BEFORE(payment_captured, invoice_sent).
```

The library says which orders are kept and which are broken. Two rules of our own split the broken ones in two, because they need
different action: the clocks *contradict* the order (the data says it went the other way), or nothing *proves* it either way (missing information):

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
for q in orders_kept orders_contradicted orders_unproven; do echo "$q:"; ask /tmp/order.zc $q | sed 's/^/  /'; done
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

The refund was logged with a clock that says it happened before the payment it refunds: a contradiction. The invoice comes from a service
that never saw the shop's clock: no evidence either way. Collapsing the two into "wrong order" would send the wrong people to look.

### 4. A claim that needs a proof

ZIL can hold a claim as data: a theorem, what it assumes, what it promises, how much it matters.

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

The `proof-evidence` library adds one macro for saying where the proof is:

```zil
MACRO LEAN_PROOF(theorem, lean_name):
EMIT theorem:{{theorem}}#proof_token@proof:{{lean_name}}.
EMIT proof:{{lean_name}}#kind@entity:proof.
EMIT proof:{{lean_name}}#engine@engine:lean4.
ENDMACRO.
```

So the last two lines of `examples/tour/04-claims-need-proofs.zc` name the Lean theorem that proves the claim. ZIL ships an audit that
refuses a high-criticality claim with no proof. The `verdict` helper shows the audit's one line per theorem (`audit` prints the whole
report). Try the file with and without those lines:

```sh
zil expand examples/tour/04-claims-need-proofs.zc /tmp/claims.zc --lib libsets/proof-evidence
verdict /tmp/claims.zc
```

```text
pass  theorem.discountNeverExceedsPrice  proof.ZilLib.Tour.discounted_le
```

```sh
grep -v '^USE LEAN_' examples/tour/04-claims-need-proofs.zc > /tmp/claims-bare.zc
zil expand /tmp/claims-bare.zc /tmp/claims-bare.expanded.zc --lib libsets/proof-evidence
verdict /tmp/claims-bare.expanded.zc
```

```text
fail  theorem.discountNeverExceedsPrice  reason: proof-evidence-missing
```

The audit checks that a proof is *named*. That the named theorem really says what the claim says is Lean's job, and the theorem is in this
repository ([`ZilLib/Tour.lean`](ZilLib/Tour.lean)), built with the library:

```lean
/-- Taking a percentage off a price never gives more than the price. -/
theorem discounted_le (price pct : Nat) (_h : pct ≤ 100) : price * (100 - pct) / 100 ≤ price := by
  apply Nat.div_le_of_le_mul
  calc price * (100 - pct) ≤ price * 100 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 100 * price := Nat.mul_comm _ _
```

Ask Lean's kernel what the proof rests on:

```sh
printf 'import ZilLib.Tour\n#print axioms ZilLib.Tour.discounted_le\n' | lake env lean --stdin
```

```text
'ZilLib.Tour.discounted_le' depends on axioms: [propext]
```

Only `propext`, an axiom of Lean itself. So the claim is data, the proof is code that Lean checked, and the audit refuses a claim that
names no proof. One link is not checked by any of them: that the name in the ZIL file is the name of a real Lean theorem. That is the one
to guard in your own CI; a `#check` line for every proof name is enough.

### What you used

| ZIL feature | Seen in |
|---|---|
| facts, rules, queries, and rules that use their own conclusions | 1 |
| negation (`NOT`), and queries over what is *absent* | 1, 2, 3 |
| the derivation behind every answer | 1 |
| macros and libraries (`USE`, `--lib`) | 2, 3, 4 |
| the same program as a Lean file | 1, 4 |
| claims and proofs as data, audited | 4 |

## Write your own library

A library is a directory of `.zc` files that hold `MACRO` definitions; `--lib DIR` puts them in scope. The `LEAN_PROOF`
macro shown in question 4 is a whole one: a name, its parameters, and the facts it stands for. Start from one of the shorter libraries in
`libsets/` (`proof-evidence` is 21 lines), put yours in a directory, and run `zil expand FILE - --lib YOUR_DIR`.

## What is here

| Path | What |
|---|---|
| `lakefile.lean` | the package, and the pin: `require «zil-lean»` at one full commit |
| `ZilLib/` | the library; `Model.lean` reads a model through the core's parser |
| `ZilLib/CLI/Main.lean` | the `zilLib` executable (`zilLib summary <model.zc>`) |
| `ZilLib/Tour.lean` | the Lean theorem behind question 4 of the tour |
| `examples/tour/` | the tour: four small models, their helpers and the outputs the README shows |
| `scripts/test.sh` | the gate |
| `scripts/test-tour.sh` | runs every command in the tour and compares with the README |
| `docs/targets.md` | the work list of the Apalache toolkit |
| `docs/move-libsets.md` | the plan to move the macro libraries here |

## Build and test

With `lake` and `git` (Lean is installed by `elan` from `lean-toolchain`):

```sh
scripts/test.sh
lake exe zilLib summary examples/tiny.zc
```

The gate runs with failing `java`, `apalache-mc` and `clojure` programs first on `PATH`: nothing here may need them to build or
test. Apalache is a Java program and is found at run time when a target needs it.

## Libraries

Opt-in macro libraries, selected with `--lib`. Each is qualified by the matrix (`scripts/matrix.sh`) except where noted.

| Library | Adds | Qualified by (matrix row: model) |
|---|---|---|
| `libsets/aws-model` | a reusable AWS modeling layer: baseline catalog entities (service, region, control), compatibility targets and gap checks | `aws-model`: `examples/aws-model-extension-with-icons.zc` |
| `libsets/aws-namespace` | the AWS layer with namespace-scoped compatibility | `aws-namespace`: `examples/aws-namespace-compat.zc` |
| `libsets/aws-transfer-family` | the AWS Transfer Family domain: the resources of its API reference | `aws-transfer-family`: `examples/generated/tf_api_model.zc` |
| `libsets/bitemporal` | a bitemporal layer (valid time and transaction time) | `bitemporal`: `examples/bitemporal-history-replay.zc` |
| `libsets/config-declarative` | a declarative configuration layer | `config-declarative`: `examples/config-declarative-macros.zc` |
| `libsets/diff-patch` | structural diffs and patchsets (not in the matrix: its rules spell variables as typed names and need a redesign) | not qualified yet |
| `libsets/discovery-api` | rules and queries over a Discovery-style API description (methods, schemas, fields, references) | `discovery-api`: `examples/discovery-api/sample-model.zc` |
| `libsets/everparse-interop` | an EverParse interoperability layer | `everparse-interop`: `examples/everparse-interop-demo.zc` |
| `libsets/k8s-helm-compat` | Kubernetes CRD and Helm compatibility modeling | `k8s-helm-compat`: `examples/k8s-helm-compat.zc` |
| `libsets/model-substrate` | one vocabulary for structure, intent and scenarios, with coherence queries (qualified by `scripts/test-model-substrate.sh`) | `scripts/test-model-substrate.sh` |
| `libsets/namespace-pn-nd` | namespace hierarchy, n-dimensional context products, category-style morphism reachability and Petri-net style resolution flow | `namespace-pn-nd`: `examples/namespace-pn-nd-extension.zc` |
| `libsets/org-pn-nd` | an organization, Petri net and n-dimensional embedding layer | `org-pn-nd`: `examples/org-pn-nd-embedding.zc` |
| `libsets/process-algebra` | temporal process prefixes, pi-calculus hand-offs, vector clocks with required orders, a discrete clock with windows | `process-algebra`: `examples/process-algebra-checks.zc` |
| `libsets/proof-evidence` | `LEAN_PROOF` and `LEAN_LEMMA_PROOF`, the kernel-evidence form `theorem-audit` reads | `proof-evidence`: `examples/proof-evidence/contracts.zc` |
| `libsets/rbac-dac` | discretionary controls (owner grants) and role controls together | `rbac-dac`: `examples/rbac-dac-orange-book.zc` |
| `libsets/request-form` | requests for data, effectful actions, compounds and recursive structures | `request-form`: `examples/request-form-recursive.zc` |
| `libsets/souffle-compat` | relations and facts in the form a Souffle program uses | `souffle-compat`: `examples/souffle-transitive-closure.zc` |
| `libsets/theorem-dsl-ci` | theorem, category-theory and theorem-impact DSLs | `category-theory`: `examples/lean4-integration/category-theory-spec.zc`, `theorem-dsl`: `examples/theorem-dsl-incident.zc`, `theorem-impact`: `examples/theorem-impact-devops-sre.zc` |

## Moving the pin

Edit the commit in `lakefile.lean`, run `lake update zil-lean`, then `scripts/test.sh`. The gate checks that the lakefile and
`lake-manifest.json` name the same full commit.

## Rules

- No change to the core from here, and no Apalache, Java or other external tool in the core's build or tests.
- The macro libraries (`libsets/`) are moving here from the core; `docs/move-libsets.md` is the plan. The vocabulary for declaring
  what to check (bounds, invariants, public projections, operations) is written as one of them.
- Results are evidence within a bound and a depth, never a proof.
- Examples are invented. Nothing from a private system enters this repository; the core's `PUBLIC-CONTENT-POLICY.md` applies.

## License

[Apache License 2.0](LICENSE). The tour examples and everything in `libsets/` are under it too, and a contribution is accepted under the same
terms (section 5 of the license).

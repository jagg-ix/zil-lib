# zil-lib

A toolkit that uses [ZIL](https://github.com/jagg-ix/zil-lean). It is not part of ZIL: it depends on the ZIL core at a
pinned commit, and the core knows nothing of it.

The first purpose is checking ZIL models with [Apalache](https://apalache-mc.org), a symbolic model checker for TLA+: rules,
queries and administrative operations over all fact sets of a bounded size and all operation sequences of a bounded length,
with every counterexample replayed by the ZIL evaluator before it is reported. Nothing of that is built yet; `docs/targets.md`
is the work list, with the order, the tests and what each result may be called.

## What is here

| Path | What |
|---|---|
| `lakefile.lean` | the package, and the pin: `require «zil-lean»` at one full commit |
| `ZilLib/` | the library; `Model.lean` reads a model through the core's parser |
| `ZilLib/CLI/Main.lean` | the `zilLib` executable (`zilLib summary <model.zc>`) |
| `scripts/test.sh` | the gate |
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

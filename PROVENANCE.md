# Provenance

The macro libraries and what qualifies them were copied from zil-lean at commit
`4f6e1f5b701c440e49166fc6c287eb3f6f703d62` (2026-10-23). The core's history keeps every earlier change to these paths
(`git log -- libsets` there); nothing was rewritten.

| Here | From the core | Changed |
|---|---|---|
| `libsets/` (18 libraries, 26 files) | `libsets/` | no |
| `spec/macro-extension-matrix.tsv` | `spec/macro-extension-matrix.tsv` | only the 18 rows whose library is under `libsets/` (the 15 others stay in the core) |
| `spec/macro-extension-golden/` (18 files) | the goldens of those rows | no |
| `scripts/matrix.sh` | `tools/macro_extension_matrix.sh` | finds the compiler and typechecker through the pinned dependency |
| `ZilLib/Test/ModelSubstrate.lean`, `test/fixtures/model-substrate/` | `Zil/Test/ModelSubstrate.lean`, `test/fixtures/model-substrate/` | namespace; the core's flat `lib/` reached through the dependency |
| `scripts/test-model-substrate.sh`, `scripts/check-model-substrate-names.sh`, `scripts/test-extension-libraries.sh` | the scripts of the same names | compiler path; the names check also scans the core's `lib/` and examples; the substrate gate removes the test module's build output first |
| `scripts/check-corpus.sh`, `spec/corpus-status.tsv` (54 files) | `scripts/check-corpus.sh`; the rows of the moved files | scope and compiler path; every recorded status equals the core's |
| `scripts/aws-namespace-smoke.sh` | `tools/aws_namespace_smoke.sh` | compiler path |
| `tools/tf-api-emit-zil.py`, `examples/generated/tf_api_schema.json` | the same paths | no |
| `examples/` (28 models and data files named by a matrix row or a gate, plus `diff-patch-demo.zc`, `kubernetes-compat*.zc` and the generated EverParse extension) | the same paths | no |
| `spec/macro-extension-v1.md`, `model-substrate-v0.1.md`, `model-substrate-targets-v0.md`, `souffle-macro-compat-v1.md` | the same paths | script and test names |

Not copied, and why: see `docs/move-libsets.md` (the 15 rows that qualify `lib/` and inline macros, the two smoke scripts that
the Clojure removal broke, the generators that write the core's `lib/` or read a file that is not in a repository).

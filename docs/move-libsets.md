# Moving `libsets/` from zil-lean to zil-lib

Decision (2026-10-23): the macro libraries leave the core and live in `zil-lib`. This file is the plan: what moves, in what
order, how each step is shown to work, and what has to be true before the core drops them.

Progress (2026-10-23): LIB-01 to LIB-08 and LIB-12 are done and `scripts/test.sh --full` passes here (6 min 37 s, with failing
`java`, `apalache-mc` and `clojure` programs on `PATH`). The libraries now exist twice. The core is untouched. The steps that
publish or remove (LIB-09, LIB-10, LIB-11) wait for the maintainer.

Why: the core is the language and its engine. A macro library is data that the engine expands; a library collection has its own
pace, its own examples and its own qualification, and depends on the core while the core depends on none of it. With the
libraries here, the vocabulary the toolkit needs (`docs/targets.md`, APL-05) is one more library, not a special case.

"Core" below is zil-lean; "here" is zil-lib. Counts were taken from the core at `4f6e1f5` on 2026-10-23.

## What moves

| Item | Size | Notes |
|---|---|---|
| `libsets/` | 18 libraries, 26 files, 200 KB | `aws-model`, `aws-namespace`, `aws-transfer-family`, `bitemporal`, `config-declarative`, `diff-patch`, `discovery-api`, `everparse-interop`, `k8s-helm-compat`, `model-substrate`, `namespace-pn-nd`, `org-pn-nd`, `process-algebra`, `proof-evidence`, `rbac-dac`, `request-form`, `souffle-compat`, `theorem-dsl-ci`. `diff-patch` is not in the matrix (its rules need a redesign); it moves as it is. |
| The qualification matrix | `spec/macro-extension-matrix.tsv` (33 rows: 18 libsets, 8 inline, 7 single files from `lib/`), `spec/macro-extension-golden/` (532 KB), the runner `tools/macro_extension_matrix.sh` | The runner needs one change: it finds the model and library paths relative to its own root; here that root is zil-lib and the compiler is the core's. |
| The model-substrate Lean tests | `Zil/Test/ModelSubstrate.lean` | Reads `libsets/model-substrate` and lists `libsets/`; the same relative paths work from this repository's root. |
| The extension gates | `scripts/test-extension-libraries.sh`, `scripts/test-model-substrate.sh`, `scripts/check-model-substrate-names.sh` | They use the core's `zil` and `zilTheoremAudit`. |
| Library examples | `examples/model-substrate/`, `examples/discovery-api/`, `examples/proof-evidence/`, `examples/macro-extension/`, `examples/process-algebra-checks.zc`, and each loose example whose matrix row or gate names a libset | Chosen by a script (LIB-06), not by hand. |
| Generators and smoke tools | `tools/aws_extension_icons_smoke.sh`, `aws_namespace_smoke.sh`, `k8s_helm_compat_smoke.sh`, `namespace_pn_nd_smoke.sh`, `generate_k8s_helm_compat.py`, `generate_everparse_2505_17335_extension.py`, `tf-api-emit-zil.py` | Paths into `libsets/` stay the same shape. |
| Specifications | `spec/macro-extension-v1.md`, `spec/model-substrate-v0.1.md`, `spec/model-substrate-targets-v0.md`, `spec/souffle-macro-compat-v1.md`, and the library catalog of the README | `spec/native-macro-v0.1.md` stays: it defines how the engine expands macros. |

## What stays in the core

- The macro engine: `Zil/Parser/Macro.lean`, `Zil/Core/Macro.lean`, `--lib DIR` on `compile`, `expand`, `query-ci`, and the nearest-`lib/`
  discovery rule. Its tests are self-contained: `Zil/Test/Macro.lean` and `MacroLibrary.lean` build their library text inline.
- `bin/zil corpus` and `spec/corpus-status.tsv`, for the examples the core keeps (82 of the 127 recorded files are examples, 26 are
  in `libsets/`, 19 in `lib/`).
- A small set of fixture libraries under `test/fixtures/macros/` for the engine's own end-to-end tests, so the core can be
  tested alone.
- `lib/` (19 flat macro files, 164 KB) stays until LIB-13 decides it; see *Open decisions*.

## Who uses `libsets/` today

| Consumer | How | Change |
|---|---|---|
| zil-lean | the matrix, three gates, the corpus script, `ModelSubstrate.lean`, README, INSTALLING, `bin/zil --help` text, 40 example references | LIB-11 |
| a project that pins the core | reads `libsets/...` paths through its pinned copy of the core | LIB-10 |
| third parties | links and `--lib libsets/...` paths into the public core | a note in the core README and a tag (LIB-11) |

## Verified before planning

From this repository, with the core as a pinned Lake dependency (checked 2026-10-23):

- `lake exe zil expand examples/tiny.zc -` runs the core's compiler, and `lake exe zilTheoremAudit` runs its audit;
- `lake env` puts the core's `.olean` files on `LEAN_PATH`, so `lake env lean` can typecheck the Lean the compiler writes.

So the matrix runner and the gates can run here without copying anything from the core's build.

## Order

Each step is one pull request in the repository it names. Steps with the same prerequisite can run in parallel.

| ID | Step | Done when | Needs | Status |
|---|---|---|---|---|
| LIB-01 | Decisions | The *Open decisions* below are answered in this file | the maintainer | done 2026-10-23: the recommendations below were accepted ("proceed as proposed") |
| LIB-02 | Runner here | `scripts/matrix.sh` runs the matrix here against the pinned core; one row (`aws-model`) passes first, then the timing of all 33 rows is recorded | LIB-01 | done 2026-10-23: `scripts/matrix.sh` runs against the pinned core; one row 22 s; all 18 rows 7 min 15 s |
| LIB-03 | Copy the libraries, matrix and goldens | `libsets/`, the matrix and the goldens are here in one commit whose message names the core commit and the exact paths; all 33 rows pass; a library with a deliberately broken macro fails its row (real rebuild, not a build that failed) | LIB-02 | done 2026-10-23: 18 libraries, 18 rows and their goldens copied (see `PROVENANCE.md`); 18 of 18 rows pass; a macro changed on purpose makes its row fail, restoring it makes it pass |
| LIB-04 | Lean tests | `ModelSubstrate.lean` runs as this repository's test executable with the same assertions as in the core; one broken library line fails it | LIB-03 | done 2026-10-23: `lake build zilLibTests`; a library line changed on purpose fails it (the gate removes the module's build output first, because Lake does not track the files the tests read) |
| LIB-05 | Gates | the three extension gates pass here with failing `java` and `clojure` programs on `PATH` | LIB-03 | done 2026-10-23: the three gates pass here with failing `java` and `clojure` programs on `PATH`; the substrate gate fails on a deliberate break |
| LIB-06 | Examples and corpus | a script lists the examples the matrix and gates name; they are here; this repository has its own `spec/corpus-status.tsv`; the core's still passes with the rest | LIB-03 | done 2026-10-23: 28 example files plus four library demos; `spec/corpus-status.tsv` has 54 files and every status equals the core's record |
| LIB-07 | Generators and smoke tools | each runs here and writes what it wrote in the core, byte for byte | LIB-03 | done with a narrower scope than planned (see *Found while doing it*): `scripts/aws-namespace-smoke.sh` and `tools/tf-api-emit-zil.py` (regenerates `tf_api_model.zc` byte for byte) |
| LIB-08 | Specifications and catalog | the specs are here, the library catalog is this repository's README, and no link in either points at a path that no longer exists | LIB-03 | done 2026-10-23: four specs and the library catalog (`README.md`); links checked |
| LIB-09 | zil-lib public | its history is scanned, the maintainer agrees, and it is public | LIB-03 to LIB-08, the maintainer | not started |
| LIB-10 | Consumers | a project that pins the core also pins zil-lib for the libraries it reads, and its chain gives the same result as before | LIB-09 | not started |
| LIB-11 | Core removal | in one core pull request: `libsets/`, the matrix, goldens, runner, gates, tools, examples and tests that moved are gone; fixtures for the engine's tests are added; `scripts/test.sh` drops three steps and adds one; the README, `INSTALLING.md` and `bin/zil --help` point here; the corpus passes; `bin/zil test --profile lean` passes with failing `java` and `clojure` programs on `PATH`; a tag `last-with-libsets` marks the commit before | LIB-09, LIB-10, the maintainer | not started |
| LIB-12 | Pin discipline | moving the core pin here runs the matrix and the gates; a script tries the core's current main without changing the pin and reports which goldens would change; a core pull request that changes expansion output says so | LIB-03 | done 2026-10-23: `scripts/try-core.sh [REV]` runs the corpus check and the matrix against another core commit in a scratch copy and says what would change |
| LIB-13 | `lib/` | decided, and if it moves, moved by the same steps as `libsets/` | LIB-11 | not started |
| LIB-14 | The checking vocabulary | APL-05 (`docs/targets.md`) is written directly in `libsets/` here | LIB-03, APL-00 | not started |
| LIB-15 | One runner | the core's `tools/macro_extension_matrix.sh` takes `--root DIR`, this repository calls it with its own matrix, and `scripts/matrix.sh` here is deleted | LIB-13 | not started |

The core is not touched until LIB-11. Until then both repositories pass their own gates and the libraries exist twice.

## Decisions (LIB-01, accepted 2026-10-23)

1. **Visibility.** The core is public and so are its libraries. If this repository stays private, a public user of the core
   loses them at LIB-11. The recommendation is: do not start LIB-11 before LIB-09. If the repository is to stay private, the
   libraries stay in the core.
2. **`lib/`.** It holds the same kind of file and is found by a core feature (nearest `lib/`). Moving only `libsets/` leaves two
   homes for macro libraries. Recommendation: move `libsets/` first, then decide `lib/` at LIB-13 with the numbers in hand; the
   discovery rule stays in the core either way, tested with fixtures.
3. **History.** Copy with a provenance commit (recommended): the core's history keeps every change to `libsets/`, and nothing is
   rewritten. The alternative is a path-limited history import, which keeps authorship in this repository but needs a rewrite tool
   and produces commits that never ran against this repository's gate.
4. **The runner.** Copy it now, and give the core's one a `--root` option later so the copy can go (LIB-15). The core cannot lose its runner
   before `lib/` moves, because 15 rows still use it.
5. **A pointer in the core.** After LIB-11, a short note in the core README and the tag are enough. A `libsets/README.md` stub is
   cheap but keeps a directory the core no longer has a reason to hold.
6. **Which core commits a library release supports.** Recommendation: one pinned commit at a time, recorded in `lakefile.lean`;
   a tag here names the core commit it was qualified against.
7. **Where APL-05 goes.** Here (LIB-14), as the first library written in the new home.

## Found while doing it

Facts that differ from the plan as first written; the plan above has been read with these in mind.

1. **The matrix does not move whole.** 18 of its 33 rows have a library under `libsets/` and moved. The other 15 qualify the core's flat
   `lib/` files (7 rows) or models that define their macros inline (8 rows). They exercise the engine and `lib/`, so they stay in the core
   until LIB-13, and so does the core's runner. The runner therefore exists twice (here it differs only in where the compiler is found).
   LIB-15 removes the copy: give the core's runner a `--root` option so this repository calls it with its own matrix.
2. **The substrate tests read more than `libsets/`.** They read the core's `lib/tlm-macros.zc`, scan the core's whole `lib/` for collisions,
   and use fixtures under `test/fixtures/model-substrate/`. The fixtures moved; the core's `lib/` is reached through the dependency path.
3. **Lake does not track files that tests read while the module compiles.** An edit to a library does not re-run `ModelSubstrate.lean`
   by itself. The substrate gate deletes that module's build output before building. The core's gate has the same gap.
4. **Two smoke scripts have been broken in the core since the Clojure removal** (`k8s_helm_compat_smoke.sh`, `namespace_pn_nd_smoke.sh` call a
   `preprocess` command that no longer exists), and a third (`aws_extension_icons_smoke.sh`) needs data that is not in the repository. None of
   the three is part of any gate. Only `aws_namespace_smoke.sh` works and moved. Decision for LIB-11: delete the other three; the matrix
   rows for the same libraries cover them.
5. **Two generators stay in the core.** `generate_k8s_helm_compat.py` also writes the core's `lib/k8s-helm-compat-macros.zc` and needs PyYAML;
   `generate_everparse_2505_17335_extension.py` reads a PDF that is not in any repository. Neither can be shown to reproduce its output here.
   `tf-api-emit-zil.py` moved: it regenerates the checked-in model byte for byte. Its first step, `tf-api-extract.py`, moved with it unrun (it reads a PDF that is not in any repository).
6. **Four more demos belong to libraries** than the matrix names: `diff-patch-demo.zc`, `kubernetes-compat.zc`, `kubernetes-compat-negative.zc` and
   `generated/everparse-2505-17335-extension.zc`. They moved.
7. **Core files that name `libsets/` and must be edited at LIB-11:** `examples/lean4-integration/access-control.zc` and its `README.md` (commands
   with `--lib libsets/rbac-dac`), `README.md`, `INSTALLING.md`, `bin/zil --help`, `scripts/check-corpus.sh`, `scripts/test.sh`, and the
   corpus record.

## Risks

- **Goldens depend on the expander.** A core change to expansion output changes goldens here. Moving the pin is a deliberate step
  with the matrix in its gate (LIB-12); the core's side is a note in its pull request, not a block.
- **Time.** The full matrix took about 500 seconds in the core's profile. The same cost moves here; the gate keeps a
  `--only NAME` option so a library author runs one row.
- **Two repositories for one change.** A new macro feature needs a core pull request, then a pin move here. The order is always
  core first.
- **Silent loss of coverage in the core.** The core's lean profile stops running the matrix. LIB-11 adds an engine-level fixture
  test, and the moved rows are proven to run here before anything is deleted.
- **Third-party paths break.** `--lib libsets/...` into the core stops working. The tag and the README note are the answer; the
  core's history keeps the files.
- **A consumer's pin.** A project that pins the core stays on a core commit that still has `libsets/` until it also pins this repository
  (LIB-10); after LIB-11 its next core pin move has to come with a zil-lib pin.

## Not in scope

- Changing what any library means. A move is a move: every golden is byte-identical before and after.
- Redesigning `diff-patch`.
- Moving the engine's macro semantics (`spec/native-macro-v0.1.md`), the parser or `bin/zil`.

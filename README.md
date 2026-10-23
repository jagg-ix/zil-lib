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
| `docs/targets.md` | the work list |

## Build and test

With `lake` and `git` (Lean is installed by `elan` from `lean-toolchain`):

```sh
scripts/test.sh
lake exe zilLib summary examples/tiny.zc
```

The gate runs with failing `java`, `apalache-mc` and `clojure` programs first on `PATH`: nothing here may need them to build or
test. Apalache is a Java program and is found at run time when a target needs it.

## Moving the pin

Edit the commit in `lakefile.lean`, run `lake update zil-lean`, then `scripts/test.sh`. The gate checks that the lakefile and
`lake-manifest.json` name the same full commit.

## Rules

- No change to the core from here, and no Apalache, Java or other external tool in the core's build or tests.
- The vocabulary for declaring what to check (bounds, invariants, public projections, operations) is a macro extension in the
  core's `libsets/`, because that is where the macro libraries and the tool that qualifies them live.
- Results are evidence within a bound and a depth, never a proof.
- Examples are invented. Nothing from a private system enters this repository.

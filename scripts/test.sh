#!/usr/bin/env bash
# The gate of the toolkit.
#
#   scripts/test.sh [--skip-build] [--full]   (--skip-build expects `lake build` to have built what --full needs)
#
# 1. the pin in lakefile.lean is the commit lake-manifest.json resolved, and is a full commit id;
# 2. a clean build needs only lake and git: the gate runs with `java`, `apalache-mc` and `clojure` shims that exit 99 first on PATH;
# 3. the executable reads a model through the pinned core and reports what it holds.
# With --full it also runs everything that qualifies the macro libraries in libsets/ (about ten minutes): the prefix check, the
# model-substrate Lean tests and examples, the extension gates, the corpus, the 18-row matrix, the AWS+namespace smoke and a
# byte-for-byte regeneration of the Transfer Family model. Tests that need Apalache are not part of this skeleton; when they
# exist they run only with --with-tool.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
skip_build=0; full=0
for argument in "$@"; do
  case "$argument" in
    --skip-build) skip_build=1 ;;
    --full) full=1 ;;
    *) echo "usage: $0 [--skip-build] [--full]" >&2; exit 2 ;;
  esac
done
work="$(mktemp -d "${TMPDIR:-/tmp}/zil-lib.XXXXXX")"
trap 'rm -rf "$work"' EXIT
failures=0
pass() { echo "PASS  $1"; }
fail() { echo "FAIL  $1" >&2; failures=$((failures + 1)); }

# the tools this package must never need: calling one fails the gate
for tool in java apalache-mc clojure clj; do
  printf '#!/bin/sh\necho "FAIL: %s was called" >&2\nexit 99\n' "$tool" >"$work/$tool"
  chmod +x "$work/$tool"
done
export PATH="$work:$PATH"

# 1. the pin
pinned="$(sed -n 's/^require «zil-lean» from git ".*" @ "\([0-9a-f]*\)".*$/\1/p' lakefile.lean)"
resolved="$(python3 -I -c 'import json; m=json.load(open("lake-manifest.json")); print([p["rev"] for p in m["packages"] if p["name"].strip("«»")=="zil-lean"][0])')"
if [[ "${#pinned}" -eq 40 && "$pinned" == "$resolved" ]]; then pass "the pin is one full commit and the manifest agrees ($pinned)"
else fail "the pin in lakefile.lean ($pinned) and lake-manifest.json ($resolved) must be the same full commit id"; fi

# 2. build
if [[ "$skip_build" -eq 0 ]]; then
  # the library gates run the core's compiler and audit and typecheck against its library: build them with the package
  targets=(); [[ "$full" -eq 1 ]] && targets=(zilLibTests zil-lean/zil zil-lean/zilTheoremAudit zil-lean/Zil)
  if lake build "${targets[@]}" >"$work/build.log" 2>&1; then pass "a build with failing java, apalache-mc and clojure shims succeeds"
  else fail "build"; tail -20 "$work/build.log" >&2; fi
fi

# 3. the executable
out="$(lake exe zilLib summary examples/tiny.zc)"
if [[ "$out" == $'facts: 3\nrules: 1\nqueries: 1\ndeclarations: 0' ]]; then pass "summary of a model read through the pinned core"
else fail "summary of a model: got $(printf '%s' "$out" | tr '\n' ' ')"; fi
set +e; lake exe zilLib summary examples/does-not-exist.zc >/dev/null 2>&1; missing=$?
lake exe zilLib bogus >/dev/null 2>&1; usage=$?; set -e
[[ "$missing" -eq 2 && "$usage" -eq 2 ]] && pass "refused: a missing model, an unknown command" || fail "refusals ($missing $usage)"

# 4. the libraries
if [[ "$full" -eq 1 ]]; then
  step() { # description command...
    local description="$1"; shift
    if "$@" >"$work/step.log" 2>&1; then pass "$description"; else fail "$description"; tail -15 "$work/step.log" >&2; fi
  }
  step "no other library defines a MODEL_ or SCENARIO_ name" scripts/check-model-substrate-names.sh
  step "model-substrate gate (Lean tests, example golden, row counts)" scripts/test-model-substrate.sh --skip-build
  step "extension libraries gate" scripts/test-extension-libraries.sh --skip-build
  step "corpus: no file changed status" scripts/check-corpus.sh --skip-build
  step "AWS and namespace smoke" scripts/aws-namespace-smoke.sh
  python3 tools/tf-api-emit-zil.py --out "$work/tf_api_model.zc" >/dev/null
  if cmp -s "$work/tf_api_model.zc" examples/generated/tf_api_model.zc; then pass "the Transfer Family model regenerates byte for byte"
  else fail "the Transfer Family model regenerates byte for byte"; fi
  step "macro matrix: 18 rows equal their goldens, compile and typecheck" scripts/matrix.sh --skip-build
fi

if [[ "$failures" -eq 0 ]]; then echo "zil-lib: all checks passed"; else echo "zil-lib: $failures check(s) failed" >&2; exit 1; fi

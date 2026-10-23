#!/usr/bin/env bash
# The gate of the toolkit.
#
#   scripts/test.sh [--skip-build]
#
# 1. the pin in lakefile.lean is the commit lake-manifest.json resolved, and is a full commit id;
# 2. a clean build needs only lake and git: the gate runs with `java`, `apalache-mc` and `clojure` shims that exit 99 first on PATH;
# 3. the executable reads a model through the pinned core and reports what it holds.
# Tests that need Apalache are not part of this skeleton; when they exist they run only with --with-tool.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
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
if [[ "${1:-}" != "--skip-build" ]]; then
  if lake build >"$work/build.log" 2>&1; then pass "a build with failing java, apalache-mc and clojure shims succeeds"
  else fail "build"; tail -20 "$work/build.log" >&2; fi
fi

# 3. the executable
out="$(lake exe zilLib summary examples/tiny.zc)"
if [[ "$out" == $'facts: 3\nrules: 1\nqueries: 1\ndeclarations: 0' ]]; then pass "summary of a model read through the pinned core"
else fail "summary of a model: got $(printf '%s' "$out" | tr '\n' ' ')"; fi
set +e; lake exe zilLib summary examples/does-not-exist.zc >/dev/null 2>&1; missing=$?
lake exe zilLib bogus >/dev/null 2>&1; usage=$?; set -e
[[ "$missing" -eq 2 && "$usage" -eq 2 ]] && pass "refused: a missing model, an unknown command" || fail "refusals ($missing $usage)"

if [[ "$failures" -eq 0 ]]; then echo "zil-lib: all checks passed"; else echo "zil-lib: $failures check(s) failed" >&2; exit 1; fi

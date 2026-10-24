#!/usr/bin/env bash
# The gate of the toolkit.
#
#   scripts/test.sh [--skip-build] [--full] [--with-tool]   (--skip-build expects `lake build` to have built what --full needs)
#
# 0. LICENSE is the Apache License 2.0 as apache.org publishes it (SHA-256 of LICENSE-2.0.txt);
# 1. the pin in lakefile.lean is the commit lake-manifest.json resolved, and is a full commit id;
# 2. a clean build needs only lake and git: the gate runs with `java`, `apalache-mc` and `clojure` shims that exit 99 first on PATH;
# 3. the executable reads a model through the pinned core and reports what it holds;
# 4. the Apalache modules (trace reader, runner, evidence, induction) and the `zilLib apalache` commands, against a stand-in tool that
#    starts no JVM, so the failing `java` and `apalache-mc` programs are never called;
# 5. the certificate checker and `zilLib certify`: the engine's answers checked by an independent program;
# 6. the SMT-LIB 2 backend and `zilLib smt`: BMC, k-induction, Lean replay reference verification, and ZIL-EVIDENCE/1.
# With --full it also runs everything that qualifies the macro libraries in libsets/ (about ten minutes): the prefix check, the
# model-substrate Lean tests and examples, the extension gates, the corpus, the 18-row matrix, the AWS+namespace smoke and a
# byte-for-byte regeneration of the Transfer Family model. With --with-tool it also runs the tests that start the real Apalache
# (found through APALACHE_HOME or PATH; skipped, and said so, when it is not there), and with --full also the Apalache section of the README.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
skip_build=0; full=0; with_tool=0
for argument in "$@"; do
  case "$argument" in
    --skip-build) skip_build=1 ;;
    --full) full=1 ;;
    --with-tool) with_tool=1 ;;
    *) echo "usage: $0 [--skip-build] [--full] [--with-tool]" >&2; exit 2 ;;
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
original_path="$PATH"   # the tests that start the real tool need the real java
export PATH="$work:$PATH"

# 0. the licence
licence_sum="$(python3 -I -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1], "rb").read()).hexdigest())' LICENSE)"
if [[ "$licence_sum" == "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30" ]]; then pass "LICENSE is the unmodified Apache License 2.0"
else fail "LICENSE is not the unmodified Apache License 2.0 text (sha256 $licence_sum)"; fi

# 1. the pin
pinned="$(sed -n 's/^require «zil-lean» from git ".*" @ "\([0-9a-f]*\)".*$/\1/p' lakefile.lean)"
resolved="$(python3 -I -c 'import json; m=json.load(open("lake-manifest.json")); print([p["rev"] for p in m["packages"] if p["name"].strip("«»")=="zil-lean"][0])')"
if [[ "${#pinned}" -eq 40 && "$pinned" == "$resolved" ]]; then pass "the pin is one full commit and the manifest agrees ($pinned)"
else fail "the pin in lakefile.lean ($pinned) and lake-manifest.json ($resolved) must be the same full commit id"; fi

# 2. build
if [[ "$skip_build" -eq 0 ]]; then
  # the library gates run the core's compiler and audit and typecheck against its library: build them with the package
  targets=(zilLibApalacheTests zilLibCertifyTests zilLibSmtTests); [[ "$full" -eq 1 ]] && targets+=(zilLibTests zil-lean/zil zil-lean/zilTheoremAudit zil-lean/Zil)
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

# 4. Apalache, against the stand-in tool
if [[ "$(lake exe zilLibApalacheTests 2>&1 | tee "$work/apalache-tests.log" | tail -1)" =~ ^[0-9]+\ passed,\ 0\ failed$ ]]; then
  pass "Apalache modules: trace reader, runner, evidence, induction ($(tail -1 "$work/apalache-tests.log"))"
else fail "Apalache modules"; grep '^FAIL' "$work/apalache-tests.log" >&2 || tail -5 "$work/apalache-tests.log" >&2; fi
fixtures=test/fixtures/apalache
fake="$fixtures/fake-home"
apalache() { APALACHE_HOME="$root/$fake" lake exe zilLib apalache "$@"; }
exit_of() { # expected-code description command...
  local expected="$1" description="$2"; shift 2
  set +e; "$@" >"$work/command.out" 2>"$work/command.err"; local code=$?; set -e
  if [[ "$code" -eq "$expected" ]]; then pass "$description (exit $code)"
  else fail "$description (exit $code, expected $expected)"; tail -3 "$work/command.out" "$work/command.err" >&2; fi
}
exit_of 0 "zilLib apalache: a run with no violation" apalache check "$fixtures/fake-models/Passing.tla" --inv Inv --length 5
exit_of 1 "zilLib apalache: a violation, with the trace printed" apalache check "$fixtures/fake-models/Violating.tla" --inv Inv --length 5
grep -q '^State 3$' "$work/command.out" && pass "the counterexample is printed state by state" || fail "the counterexample is not printed"
exit_of 1 "zilLib apalache: a deadlock" apalache check "$fixtures/fake-models/Deadlocking.tla" --inv Inv --length 5
exit_of 2 "zilLib apalache: input the tool rejects" apalache check "$fixtures/fake-models/Rejected.tla" --inv Inv --length 5
exit_of 2 "zilLib apalache: a command line without an invariant" apalache check "$fixtures/fake-models/Passing.tla"
exit_of 4 "zilLib apalache: a run past its deadline" apalache check "$fixtures/fake-models/Slow.tla" --inv Inv --timeout 1
exit_of 0 "zilLib apalache: an inductive invariant" apalache induct "$fixtures/fake-models/Inductive.tla" --indinit IndInit --inv IndInv
exit_of 1 "zilLib apalache: an invariant that is not inductive" apalache induct "$fixtures/fake-models/NotInductive.tla" --indinit IndInit --inv IndInv
exit_of 0 "zilLib apalache: a trace file is printed" lake exe zilLib apalache trace "$fixtures/counter.violation.itf.json"
exit_of 3 "zilLib apalache: no tool: the failing apalache-mc program first on PATH does not report a version" lake exe zilLib apalache version
exit_of 3 "zilLib apalache: no tool: nothing in APALACHE_HOME" env APALACHE_HOME=/nonexistent lake exe zilLib apalache check "$fixtures/fake-models/Passing.tla" --inv Inv
set +e; apalache check "$fixtures/fake-models/Violating.tla" --inv Inv --length 5 --evidence "$work/evidence.json" >/dev/null 2>&1; set -e
if python3 -I - "$work/evidence.json" <<'PY'
import hashlib, json, sys
envelope = json.load(open(sys.argv[1]))
assert envelope["schema"] == "ZIL-EVIDENCE/1"
assert envelope["authority"] == "external" and envelope["assurance"] == "externally-attested"
assert envelope["evidence_id"].startswith("evidence:") and len(envelope["evidence_id"]) == 73
assert envelope["output_sha256"] == "sha256:" + hashlib.sha256(envelope["payload"].encode()).hexdigest()
assert json.loads(envelope["payload"])["verdict"] == "violation-found"
PY
then pass "the evidence file is a ZIL-EVIDENCE/1 envelope whose digest matches its payload (checked outside Lean)"
else fail "the evidence file"; fi

if [[ "$with_tool" -eq 1 ]]; then
  if PATH="$original_path" lake exe zilLibApalacheTests --with-tool 2>&1 | tee "$work/apalache-real.log" | tail -1 | grep -qE '^[0-9]+ passed, 0 failed$'; then
    if grep -q '^SKIP' "$work/apalache-real.log"; then pass "tests with the real Apalache: skipped, apalache-mc not found"
    else pass "tests with the real Apalache ($(grep '^tool:' "$work/apalache-real.log"); $(tail -1 "$work/apalache-real.log"))"; fi
  else fail "tests with the real Apalache"; grep '^FAIL' "$work/apalache-real.log" >&2 || tail -5 "$work/apalache-real.log" >&2; fi
fi

# 5. the certificate checker (docs/certifying-datalog.md)
if [[ "$(lake exe zilLibCertifyTests 2>&1 | tee "$work/certify-tests.log" | tail -1)" =~ ^[0-9]+\ passed,\ 0\ failed$ ]]; then
  pass "certificate checker: soundness, closure, stratification, faults, the engine's fixpoint ($(tail -1 "$work/certify-tests.log"))"
else fail "certificate checker"; grep '^FAIL' "$work/certify-tests.log" >&2 || tail -5 "$work/certify-tests.log" >&2; fi
exit_of 0 "certify: the engine's trace of the shop model is certified" lake exe zilLib certify examples/tour/01-blast-radius.zc
exit_of 0 "certify: the engine's trace of a chain of 70 steps is certified (it stopped at 64 rounds before zil-lean cdec3f2)" lake exe zilLib certify examples/certify/chain.zc
exit_of 1 "certify: the trace the engine printed before that fix is not closed" lake exe zilLib certify examples/certify/chain.zc test/fixtures/certify/chain.old-engine-trace.txt
grep -q 'not-closed.*n66' "$work/command.out" && pass "certify: the missing fact is named" || fail "certify: the missing fact is not named"
exit_of 2 "certify: a bound of 64 rounds is an error of the engine, not a shorter trace" lake exe zilLib certify examples/certify/chain.zc --fuel 64
exit_of 2 "certify: a model that does not exist" lake exe zilLib certify "$work/absent.zc"
exit_of 2 "certify: a command line without a model" lake exe zilLib certify
printf 'fact\t0\t0\trel\tnode:a\tr\tnode:b\t\n' >"$work/broken-trace.txt"
exit_of 2 "certify: a report that cannot be read" lake exe zilLib certify examples/tour/01-blast-radius.zc "$work/broken-trace.txt"
exit_of 0 "certify: write a certificate as JSON" lake exe zilLib certify examples/tour/01-blast-radius.zc --json "$work/tour.cert.json"
exit_of 0 "certify: read back and verify the JSON certificate" lake exe zilLib certify examples/tour/01-blast-radius.zc "$work/tour.cert.json"
lake exe zilLib certify examples/tour/01-blast-radius.zc --json "$work/tour2.cert.json" >/dev/null 2>&1
cmp -s "$work/tour.cert.json" "$work/tour2.cert.json" && pass "certify: the JSON certificate is byte-deterministic" \
  || fail "certify: the JSON certificate is not byte-deterministic"
# a model is read with the macro libraries named by --lib, as the core's expand reads them
rows=0; unsound=""; json_unsound=""
while IFS=$'\t' read -r name library model; do
  case "$library" in -) options=() ;; @*) options=(--lib "${library#@}") ;; *) options=(--lib "$library") ;; esac
  rows=$((rows + 1))
  lake exe zilLib certify "$model" ${options[@]+"${options[@]}"} --verified --json "$work/$name.cert.json" >"$work/row.out" 2>"$work/row.err" || unsound="$unsound $name"
  grep -q "proved checker.*accepted" "$work/row.out" || unsound="$unsound $name(proved)"
  lake exe zilLib certify "$model" ${options[@]+"${options[@]}"} "$work/$name.cert.json" --json "$work/$name.cert2.json" >/dev/null 2>&1 || json_unsound="$json_unsound $name(verify)"
  cmp -s "$work/$name.cert.json" "$work/$name.cert2.json" || json_unsound="$json_unsound $name(bytes)"
done < <(grep -v "^#" spec/macro-extension-matrix.tsv)
[[ "$rows" -eq 18 && -z "$unsound" ]] && pass "certify: all $rows models of spec/macro-extension-matrix.tsv, read with their libraries, are certified, and accepted by the proved checker" \
  || fail "certify: $rows rows read, not certified:$unsound"
[[ "$rows" -eq 18 && -z "$json_unsound" ]] && pass "certify: all $rows models of spec/macro-extension-matrix.tsv: JSON certificates read back, certified, and byte-deterministic" \
  || fail "certify: $rows JSON certificates read, not certified:$json_unsound"
lake exe zilLib certify examples/tour/01-blast-radius.zc --json >"$work/stdout.cert.json" 2>"$work/stdout.cert.err"
if python3 -I -c 'import json, sys; d = json.load(open(sys.argv[1])); assert d["format"] == "ZIL-CERTIFICATE/1"' "$work/stdout.cert.json" 2>/dev/null; then
  pass "certify: --json without a file writes valid JSON to stdout without text report"
else
  fail "certify: --json without a file does not write valid JSON to stdout"
fi
exit_of 0 "certify: the tour model is also accepted by the proved checker (--verified)" lake exe zilLib certify examples/tour/01-blast-radius.zc --verified
grep -q 'proved checker.*accepted' "$work/command.out" && pass "certify: the proved checker's verdict is printed" || fail "certify: the proved checker's verdict is missing"
exit_of 0 "certify: the answers to a query are certified" lake exe zilLib certify examples/tour/01-blast-radius.zc --query single_points
grep -q 'query single_points: 4 answer(s), the same rows' "$work/command.out" && pass "certify: the four rows of single_points agree with the engine's" || fail "certify: the rows of single_points"
exit_of 2 "certify: a query that does not exist" lake exe zilLib certify examples/tour/01-blast-radius.zc --query nonexistent
grep -q 'no query named nonexistent; the queries are: what_breaks_if_payments_is_down, single_points' "$work/command.err" && pass "certify: the unknown query is named, with the queries there are" || fail "certify: the unknown query is not named"
exit_of 2 "certify: a model that uses a library macro, read without the library" lake exe zilLib certify examples/aws-model-extension-with-icons.zc
grep -q 'unknown macro AWS_PROVIDER' "$work/command.err" && pass "certify: the missing macro is named" || fail "certify: the missing macro is not named"
exit_of 0 "certify: a library given as one file" lake exe zilLib certify examples/aws-model-extension-with-icons.zc --lib libsets/aws-model/aws-model-macros.zc
exit_of 0 "certify: three libraries given one by one" lake exe zilLib certify examples/aws-namespace-compat.zc \
  --lib libsets/aws-model/aws-model-macros.zc --lib libsets/aws-namespace/aws-namespace-bridge-macros.zc --lib libsets/namespace-pn-nd/namespace-pn-nd-macros.zc
cp "$work/command.out" "$work/three-files.out"
lake exe zilLib certify examples/aws-namespace-compat.zc --lib libsets/aws-namespace >"$work/directory.out" 2>/dev/null
cmp -s "$work/three-files.out" "$work/directory.out" && pass "certify: those three files give the same result as the directory that holds them" \
  || fail "certify: three files and their directory differ"
exit_of 2 "certify: --lib without a path" lake exe zilLib certify examples/tiny.zc --lib
exit_of 2 "certify: --lib with a directory that has no .zc file" lake exe zilLib certify examples/tiny.zc --lib test/fixtures/certify
exit_of 2 "certify: --lib with a path that does not exist" lake exe zilLib certify examples/tiny.zc --lib "$work/absent"
exit_of 0 "certify: facts written as zil_fact lines, with a rule in .zc" lake exe zilLib certify examples/certify/lean-facts.zc
grep -q '4 facts, 3 from the database and 1 derived' "$work/command.out" && pass "certify: the three zil_fact lines are facts and the rule derived one more" \
  || fail "certify: the zil_fact lines were not read as three facts"
printf 'MODULE m.\nzil_fact node(a) ⟶[r]\n' >"$work/broken-lines.zc"
exit_of 2 "certify: a zil_fact line in another shape is refused" lake exe zilLib certify "$work/broken-lines.zc"
grep -q 'line 2:' "$work/command.err" && pass "certify: the refusal names the line" || fail "certify: the refusal does not name the line"

# 6. SMT-LIB 2 backend (TS-03)
if [[ "$(lake exe zilLibSmtTests 2>&1 | tee "$work/smt-tests.log" | tail -1)" =~ ^[0-9]+\ passed,\ 0\ failed$ ]]; then
  pass "SMT-LIB 2 backend: BMC, k-induction, model parser, replay validation, Z3 runner ($(tail -1 "$work/smt-tests.log"))"
else fail "SMT-LIB 2 backend"; grep '^FAIL' "$work/smt-tests.log" >&2 || tail -5 "$work/smt-tests.log" >&2; fi

exit_of 0 "zilLib smt: version reports solver" lake exe zilLib smt version
exit_of 0 "zilLib smt: BMC on passing Counter" lake exe zilLib smt check Counter --inv x_nonneg --length 5
exit_of 1 "zilLib smt: BMC on defective Counter finds violation" lake exe zilLib smt check CounterDefective --inv x_lt_3 --length 5
grep -q '^State 3$' "$work/command.out" && pass "zilLib smt: counterexample printed state by state" || fail "zilLib smt: counterexample not printed"
exit_of 0 "zilLib smt: k-induction on Counter" lake exe zilLib smt induct Counter --inv x_nonneg --step 1
exit_of 1 "zilLib smt: k-induction on non-inductive invariant" lake exe zilLib smt induct CounterDefective --inv x_lt_3 --step 1
exit_of 2 "zilLib smt: command line without an invariant" lake exe zilLib smt check Counter --length 5
exit_of 2 "zilLib smt: unknown module" lake exe zilLib smt check Nonexistent --inv x_nonneg
exit_of 2 "zilLib smt: unknown invariant" lake exe zilLib smt check Counter --inv nonexistent
set +e; lake exe zilLib smt check CounterDefective --inv x_lt_3 --length 5 --evidence "$work/smt-evidence.json" >/dev/null 2>&1; set -e
if python3 -I - "$work/smt-evidence.json" <<'PY'
import hashlib, json, sys
envelope = json.load(open(sys.argv[1]))
assert envelope["schema"] == "ZIL-EVIDENCE/1"
assert envelope["authority"] == "external" and envelope["assurance"] == "externally-attested"
assert envelope["role"] == "bounded-model-checker"
assert envelope["evidence_id"].startswith("evidence:") and len(envelope["evidence_id"]) == 73
assert envelope["output_sha256"] == "sha256:" + hashlib.sha256(envelope["payload"].encode()).hexdigest()
assert json.loads(envelope["payload"])["verdict"] == "violation-found"
PY
then pass "zilLib smt: the evidence file is a valid ZIL-EVIDENCE/1 envelope"
else fail "zilLib smt: the evidence file failed verification"; fi

# 7. the libraries
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
  step "README tour: every command on the page prints what the page shows" scripts/test-tour.sh --skip-build
  if [[ "$with_tool" -eq 1 ]]; then
    step "README tour, Apalache section: the commands start the real tool" env PATH="$original_path" scripts/test-tour.sh --skip-build --with-tool
  fi
fi

if [[ "$failures" -eq 0 ]]; then echo "zil-lib: all checks passed"; else echo "zil-lib: $failures check(s) failed" >&2; exit 1; fi

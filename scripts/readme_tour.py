#!/usr/bin/env python3
"""Run the README's examples, as the README shows them.

    python3 -I scripts/readme_tour.py [--show] [--with-tool]

Three sections are read:
  * "## A tour" up to "## Writing your own library", always;
  * "## Certifying the engine's answers" up to the next "## " heading, always;
  * "## Checking TLA+ models with Apalache" up to the next "## " heading, only with --with-tool, because its commands start the real
    tool (found through APALACHE_HOME or PATH; without it the section is skipped and the run says so).
In both:
  * every ```sh block runs, in order, with the tour helpers loaded and /tmp/ replaced by a scratch directory; when a ```text block
    follows, the block's standard output must equal it;
  * every ```zil, ```lean and ```tla block must be a contiguous piece of one of the source files the examples use, so a quoted line
    cannot go stale.
The ```sh block that defines the helpers (in "Try it") must be the helpers file. --show prints each block's actual output instead of
comparing (for writing the README).
"""
import pathlib, re, subprocess, sys, tempfile

root = pathlib.Path(__file__).resolve().parent.parent
show = "--show" in sys.argv
with_tool = "--with-tool" in sys.argv
readme = (root / "README.md").read_text()
sources = {p: p.read_text() for p in [*root.glob("examples/tour/*.zc"), root / "ZilLib/Tour.lean",
                                       root / "libsets/proof-evidence/proof-evidence-macros.zc",
                                       *root.glob("test/fixtures/apalache/*.tla"), *root.glob("examples/certify/*.zc")]}

def blocks(text):
    return [(m.group(1), m.group(2).rstrip("\n")) for m in re.finditer(r"^```(\w*)\n(.*?)^```", text, re.M | re.S)]

failures = 0
def fail(message):
    global failures
    failures += 1
    print("FAIL  " + message, file=sys.stderr)

def section(first, last):
    """The text from the heading `first` to the heading `last` (or the next '## ' heading when `last` is None)."""
    if first not in readme:
        sys.exit(f"FAIL  the README has no heading starting with {first!r}")
    start = readme.index(first)
    if last is None:
        end = readme.find("\n## ", start + 1)
        return readme[start:end if end != -1 else len(readme)]
    if last not in readme:
        sys.exit(f"FAIL  the README has no heading starting with {last!r}")
    return readme[start:readme.index(last)]

def run_section(label, text, work):
    parts = blocks(text)
    for position, (language, body) in enumerate(parts):
        if language in ("zil", "lean", "tla"):
            if any(body in source for source in sources.values()):
                print(f"PASS  {label}: quoted {language} block {position + 1} is in a source file")
            else:
                fail(f"{label}: quoted {language} block {position + 1} is in no source file:\n{body[:200]}")
        elif language == "sh":
            command = body.replace("/tmp/", work + "/")
            run = subprocess.run(["bash", "-c", "set -euo pipefail; . examples/tour/helpers.sh\n" + command],
                                 cwd=root, capture_output=True, text=True)
            first_line = body.splitlines()[0][:60]
            if run.returncode != 0:
                fail(f"{label}: command failed ({run.returncode}): {first_line}\n{run.stderr[-600:]}")
                continue
            got = run.stdout.rstrip("\n").replace(work + "/", "/tmp/")
            following = parts[position + 1] if position + 1 < len(parts) else None
            if show:
                print(f"--- {first_line}\n{got}")
            elif following and following[0] == "text":
                if got == following[1]:
                    print(f"PASS  {label}: {first_line}")
                else:
                    fail(f"{label}: output differs: {first_line}\n--- page\n{following[1]}\n--- actual\n{got}")
            elif got:
                fail(f"{label}: command printed output the page does not show: {first_line}\n{got[:300]}")
            else:
                print(f"PASS  {label}: {first_line}")

helpers = (root / "examples/tour/helpers.sh").read_text().split("\n", 1)[1].rstrip("\n")
if helpers in [b for _, b in blocks(readme)]:
    print("PASS  the README shows examples/tour/helpers.sh as it is")
else:
    fail("the README does not show examples/tour/helpers.sh as it is")

with tempfile.TemporaryDirectory(prefix="zil-tour.") as work:
    run_section("tour", section("## A tour", "## Writing your own library"), work)
    run_section("certify", section("## Certifying the engine's answers", None), work)
    if with_tool:
        run_section("apalache", section("## Checking TLA+ models with Apalache", None), work)
    else:
        print("SKIP  the Apalache section: it starts the real tool (run with --with-tool)")

if failures:
    print(f"tour: {failures} check(s) failed", file=sys.stderr)
    sys.exit(1)
print("tour: all checks pass")

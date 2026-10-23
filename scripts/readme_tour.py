#!/usr/bin/env python3
"""Run the README's tour, as the README shows it.

    python3 -I scripts/readme_tour.py [--show]

Between the headings "## A tour" and "## Write your own library":
  * every ```sh block runs, in order, with the tour helpers loaded and /tmp/ replaced by a scratch directory; when a ```text block follows,
    the block's standard output must equal it;
  * every ```zil and ```lean block must be a contiguous piece of one of the source files the tour uses, so a quoted line cannot go stale.
The ```sh block that defines the helpers (in "Try it") must be the helpers file. --show prints each block's actual output instead of
comparing (for writing the README).
"""
import pathlib, re, subprocess, sys, tempfile

root = pathlib.Path(__file__).resolve().parent.parent
show = "--show" in sys.argv
readme = (root / "README.md").read_text()
sources = {p: p.read_text() for p in [*root.glob("examples/tour/*.zc"), root / "ZilLib/Tour.lean",
                                       root / "libsets/proof-evidence/proof-evidence-macros.zc"]}

def blocks(text):
    return [(m.group(1), m.group(2).rstrip("\n")) for m in re.finditer(r"^```(\w*)\n(.*?)^```", text, re.M | re.S)]

failures = 0
def fail(message):
    global failures
    failures += 1
    print("FAIL  " + message, file=sys.stderr)

helpers = (root / "examples/tour/helpers.sh").read_text().split("\n", 1)[1].rstrip("\n")
if helpers in [b for _, b in blocks(readme)]:
    print("PASS  the README shows examples/tour/helpers.sh as it is")
else:
    fail("the README does not show examples/tour/helpers.sh as it is")

start, end = readme.index("## A tour"), readme.index("## Write your own library")
tour = blocks(readme[start:end])
with tempfile.TemporaryDirectory(prefix="zil-tour.") as work:
    for position, (language, body) in enumerate(tour):
        if language in ("zil", "lean"):
            if any(body in text for text in sources.values()):
                print(f"PASS  quoted {language} block {position + 1} is in a source file")
            else:
                fail(f"quoted {language} block {position + 1} is in no source file:\n{body[:200]}")
        elif language == "sh":
            command = body.replace("/tmp/", work + "/")
            run = subprocess.run(["bash", "-c", "set -euo pipefail; . examples/tour/helpers.sh\n" + command],
                                 cwd=root, capture_output=True, text=True)
            label = body.splitlines()[0][:60]
            if run.returncode != 0:
                fail(f"command failed ({run.returncode}): {label}\n{run.stderr[-600:]}")
                continue
            got = run.stdout.rstrip("\n").replace(work + "/", "/tmp/")
            following = tour[position + 1] if position + 1 < len(tour) else None
            if show:
                print(f"--- {label}\n{got}")
            elif following and following[0] == "text":
                if got == following[1]:
                    print(f"PASS  {label}")
                else:
                    fail(f"output differs: {label}\n--- page\n{following[1]}\n--- actual\n{got}")
            elif got:
                fail(f"command printed output the page does not show: {label}\n{got[:300]}")
            else:
                print(f"PASS  {label}")

if failures:
    print(f"tour: {failures} check(s) failed", file=sys.stderr)
    sys.exit(1)
print("tour: all checks pass")

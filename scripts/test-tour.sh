#!/usr/bin/env bash
# The README tour, run for real: every command on the page is executed and its output compared with the page (scripts/readme_tour.py).
#
#   scripts/test-tour.sh [--skip-build] [--show] [--with-tool]
#
# --show prints what each command printed, to write the README from. --with-tool also runs the commands that start the real Apalache.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
skip_build=0; show=(); with_tool=()
for argument in "$@"; do
  case "$argument" in
    --skip-build) skip_build=1 ;;
    --show) show=(--show) ;;
    --with-tool) with_tool=(--with-tool) ;;
    *) echo "usage: $0 [--skip-build] [--show] [--with-tool]" >&2; exit 2 ;;
  esac
done
if [[ "$skip_build" -eq 0 ]]; then
  lake build ZilLib zilLib zil-lean/zil zil-lean/zilTheoremAudit zil-lean/Zil >/dev/null 2>&1 || { echo "build failed" >&2; exit 1; }
fi
exec python3 -I scripts/readme_tour.py ${show[@]+"${show[@]}"} ${with_tool[@]+"${with_tool[@]}"}

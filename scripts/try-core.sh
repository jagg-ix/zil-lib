#!/usr/bin/env bash
# What would moving the pin to another core commit change here?
#
#   scripts/try-core.sh [REV] [matrix.sh options...]
#
# Copies this repository to a scratch directory, points the copy's pin at REV (default: the head of the core's main branch),
# updates the dependency there, then runs the corpus check and the macro matrix and prints which golden outputs or file statuses
# would change. Nothing here is modified. Run it before moving the pin for real, and put its output in the pull request.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
url="$(sed -n 's/^require «zil-lean» from git "\(.*\)" @ ".*".*$/\1/p' "$root/lakefile.lean")"
rev="${1:-}"
[[ -n "$rev" && "$rev" != --* ]] && shift || rev="$(git ls-remote "$url" refs/heads/main | cut -f1)"
[[ "${#rev}" -eq 40 ]] || { echo "need a full 40-hex commit id, got '$rev'" >&2; exit 2; }
current="$(sed -n 's/^require «zil-lean» from git ".*" @ "\([0-9a-f]*\)".*$/\1/p' "$root/lakefile.lean")"
echo "pin: $current -> $rev"

scratch="$(mktemp -d "${TMPDIR:-/tmp}/zil-lib-try.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
rsync -a --exclude .lake --exclude .git "$root/" "$scratch/"
sed -i.bak "s/$current/$rev/" "$scratch/lakefile.lean" && rm "$scratch/lakefile.lean.bak"
cd "$scratch"
git init -q && git add -A   # the corpus check lists files with git
rm -f lake-manifest.json
lake update >/dev/null 2>&1 || { echo "the dependency could not be updated to $rev" >&2; exit 2; }

status=0
echo "== corpus"; scripts/check-corpus.sh || status=1
echo "== matrix"; scripts/matrix.sh "$@" || status=1
if [[ "$status" -eq 0 ]]; then echo "moving the pin to $rev changes nothing here"
else echo "moving the pin to $rev changes the results above: review them, then update the goldens with scripts/matrix.sh --update"; fi
exit "$status"

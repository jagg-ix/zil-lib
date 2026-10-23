# Helpers for the tour. Source this from the repository root: . examples/tour/helpers.sh
zil()   { lake env zil "$@"; }
audit() { lake env zilTheoremAudit "$@"; }

# ask FILE QUERY: the answers to a query, one per line
ask()   { zil explain-query "$1" "$2" | awk -F'\t' '$1 == "witness" {print $3}'; }

# answers FILE QUERY...: the answers to each query on one line, or (none)
answers() { local file="$1" q found; shift; for q in "$@"; do found="$(ask "$file" "$q" | paste -sd' ' -)"; echo "$q: ${found:-(none)}"; done; }

# why FILE QUERY TEXT: how the first answer containing TEXT was derived: each rule that fired, and the facts it used
why()   { zil explain-query "$1" "$2" | awk -F'\t' -v pat="$3" '
  $1 == "witness" && goal == "" && index($3, pat) { goal = $4 }
  $1 == "origin" && $3 == "rule" { rule[$2] = $4; from[$2] = $5; args[$2] = $NF }
  function walk(id,  n, p, k) { if ((id in rule) && !(id in seen)) { seen[id] = 1; n = split(from[id], p, ","); for (k = 1; k <= n; k++) walk(p[k]) } }
  END { walk(goal); for (id = 0; id <= goal; id++) if (id in seen) printf "%2s  %-16s from %-4s %s\n", id, rule[id], from[id], args[id] }'; }

# verdict MODEL: the audit's one line per theorem: its status, its name, and its proof or the reason it failed
# (the audit exits 1 when a claim fails; the line says so, so the exit status is dropped here)
verdict() { { audit "$1" - || true; } | awk -F'\t' '$1 == "theorem" {printf "%s  %s  %s\n", $3, $2, ($NF == "" ? $(NF - 1) : "reason: " $NF)}'; }

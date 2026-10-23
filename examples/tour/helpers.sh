# Helper functions for the tour. Load them from the repository root: . examples/tour/helpers.sh
zil()   { lake env zil "$@"; }
audit() { lake env zilTheoremAudit "$@"; }

# query FILE NAME: print the result bindings of a query, one per line
query() { zil explain-query "$1" "$2" | awk -F'\t' '$1 == "witness" {print $3}'; }

# queries FILE NAME...: print the results of each query on one line, or (none)
queries() { local file="$1" name results; shift; for name in "$@"; do results="$(query "$file" "$name" | paste -sd' ' -)"; echo "$name: ${results:-(none)}"; done; }

# explain FILE NAME TEXT: print the derivation (provenance) of the first result whose binding contains TEXT:
# each rule that was applied, with the IDs of the facts it used
explain() { zil explain-query "$1" "$2" | awk -F'\t' -v pat="$3" '
  $1 == "witness" && goal == "" && index($3, pat) { goal = $4 }
  $1 == "origin" && $3 == "rule" { rule[$2] = $4; from[$2] = $5; args[$2] = $NF }
  function walk(id,  n, p, k) { if ((id in rule) && !(id in seen)) { seen[id] = 1; n = split(from[id], p, ","); for (k = 1; k <= n; k++) walk(p[k]) } }
  END { walk(goal); for (id = 0; id <= goal; id++) if (id in seen) printf "%2s  %-16s from %-4s %s\n", id, rule[id], from[id], args[id] }'; }

# audit_summary MODEL: print one line per theorem from the audit: status, name, and its proof or the failure reason
# (the audit exits with status 1 when a theorem fails, so that exit status is ignored here)
audit_summary() { { audit "$1" - || true; } | awk -F'\t' '$1 == "theorem" {printf "%s  %s  %s\n", $3, $2, ($NF == "" ? $(NF - 1) : "reason: " $NF)}'; }

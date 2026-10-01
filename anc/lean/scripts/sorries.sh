#!/usr/bin/env bash
# Real `sorry` audit: lists every genuine `sorry` (not a backquoted mention in a docstring like
# "no `sorry`") grouped by file, with the enclosing declaration name, then a total and a
# file-descending ranking.
#
# Usage (from the project root):
#
#   bash scripts/sorries.sh
#
# Exit code is always 0 on a clean run (sorries are the normal, expected state pre-completion;
# this is a report, not a check). A non-zero exit means the script itself failed.
set -euo pipefail

cd "$(dirname "$0")/.."

# Match `sorry` as a whole token, not as part of a longer identifier (`sorryAx`) nor with a
# trailing `?` / `!` (`sorry?`).  Comments are removed before this is applied -- see `strip`
# below -- so no backtick-based heuristic is needed or wanted here.
pattern='(^|[^A-Za-z_.])sorry([^A-Za-z_?!]|$)'

files=$(find Nivat.lean Nivat -name '*.lean' | sort)

echo "FILE:LINE                                          DECLARATION"
echo "--------------------------------------------------------------"

total=0
# Initialise, do not merely declare: under `set -u` an empty `declare -a` array is still
# "unset", so `${#rank_names[@]}` aborts the script -- which is exactly what happens on the
# happy path, when no file has a `sorry` and nothing ever appends to these.
declare -a rank_names=()
declare -a rank_counts=()

for f in $files; do
  # Single gawk pass: for each real `sorry` line, print "file:line  decl", where `decl` is the
  # name of the nearest enclosing theorem/lemma/def (scanning upward); last line is "@COUNT n".
  #
  # Every line is first passed through `strip`, which deletes Lean comments -- `--` to end of
  # line, and `/- ... -/` blocks, which in Lean *nest* (`/-- ... -/` docstrings are just block
  # comments and are stripped too).  Both the `sorry` match and the declaration-name scan run on
  # the stripped text, so prose like "case (α) is fully proved (zero sorry)" or a commented-out
  # `theorem foo` can no longer be mistaken for code.  Limitation: `--` and `/-` inside a string
  # literal would be treated as comment openers; no such literal occurs in this project.
  out=$(gawk -v pat="$pattern" '
    function strip(line,   i, n, two, out) {
      i = 1; n = length(line); out = ""
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth > 0) {
          if (two == "-/") { depth--; i += 2 }
          else if (two == "/-") { depth++; i += 2 }
          else i++
        } else {
          if (two == "/-") { depth++; i += 2 }
          else if (two == "--") { return out }
          else { out = out substr(line, i, 1); i++ }
        }
      }
      return out
    }
    BEGIN { decl = "(none)"; count = 0; depth = 0 }
    {
      code = strip($0)
      if (match(code, /^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+)*(theorem|lemma|def|abbrev|instance)[[:space:]]+([A-Za-z_][A-Za-zA-Z0-9_.'"'"']*)/, m)) {
        decl = m[3]
      }
      if (code ~ pat) {
        print FILENAME ":" FNR "  " decl
        count++
      }
    }
    END { print "@COUNT " count }
  ' "$f")
  cnt=$(printf '%s\n' "$out" | tail -n1 | sed 's/@COUNT //')
  if [ "$cnt" -gt 0 ]; then
    printf '%s\n' "$out" | sed '$d'
    total=$((total + cnt))
    rank_names+=("$f")
    rank_counts+=("$cnt")
  fi
done

echo "--------------------------------------------------------------"
echo "TOTAL: $total"
echo
echo "Ranking (file, descending):"
if [ "${#rank_names[@]}" -eq 0 ]; then
  echo "  (none)"
else
  for i in "${!rank_names[@]}"; do
    printf '%d %s\n' "${rank_counts[$i]}" "${rank_names[$i]}"
  done | sort -rn | awk '{printf "  %-46s %5d\n", $2, $1}'
fi

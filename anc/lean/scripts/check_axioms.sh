#!/usr/bin/env bash
# Axiom audit: for each given declaration name, prints the axioms it depends on and fails if any
# of them is outside the whitelist (Lean's own three axioms: propext, Classical.choice,
# Quot.sound; see `scripts/check_axioms.lean`). `sorryAx` is deliberately NOT whitelisted, so any
# declaration still resting on a `sorry` (directly or transitively) is reported and fails.
#
# Usage (from the project root):
#
#   bash scripts/check_axioms.sh Nivat.nivat_conjecture
#   bash scripts/check_axioms.sh Nivat.foo Nivat.bar   # multiple declarations at once
#
# This wraps `scripts/check_axioms.lean`, a throwaway driver run via `lake env lean --run`, which
# only reads the already-built `Nivat` .olean and is safe to run without the lake build lock.
set -euo pipefail

cd "$(dirname "$0")/.."

if [ "$#" -eq 0 ]; then
  echo "usage: bash scripts/check_axioms.sh DECL [DECL ...]" >&2
  exit 2
fi

lake env lean --run scripts/check_axioms.lean "$@"

#!/usr/bin/env bash
# CI check (book/M1-BRIEF.md): engine/ is executable code that goes into the wasm build and must
# not require anything beyond std/batteries, and must never import Mathlib. proofs/ is the only
# place Mathlib may appear.
set -euo pipefail
cd "$(dirname "$0")/.."
status=0
allowed='^(std|batteries)$'
reqs=$(awk '/^\[\[require\]\]/{r=1;next} r&&/^name/{gsub(/["[:space:]]/,"",$0);sub(/^name=/,"",$0);print;r=0}' engine/lakefile.toml || true)
for r in $reqs; do
  if ! [[ $r =~ $allowed ]]; then echo "engine/lakefile.toml requires '$r' (only std/batteries allowed)"; status=1; fi
done
if grep -rn --include='*.lean' --exclude-dir=toolchains --exclude-dir=.lake -E '^import (Mathlib|Proofs)' engine/ ; then
  echo "engine/ imports Mathlib or proofs/"; status=1
fi
[ $status -eq 0 ] && echo "engine/ dependencies OK (requires: ${reqs:-none})"
exit $status

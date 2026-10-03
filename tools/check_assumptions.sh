#!/bin/sh
# Fail unless every headline theorem is closed under the global context
# (no axioms, no admitted lemmas, no parameters).
set -eu
cd "$(dirname "$0")/.."
out=$(coqc -R theories Sciuridae theories/Assumptions.v 2>&1)
printf '%s\n' "$out"
if printf '%s\n' "$out" | grep -q "Axioms:"; then
  echo "FAIL: some theorem depends on an axiom" >&2; exit 1
fi
n=$(printf '%s\n' "$out" | grep -c "Closed under the global context" || true)
echo "OK: $n theorems closed under the global context"

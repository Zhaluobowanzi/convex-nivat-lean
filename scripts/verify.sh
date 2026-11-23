#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
upstream=.lake/packages/nivat
pin=4e3614024227acd273c3e8ab41df92c2709e5ab0
test "$(git -C "$upstream" rev-parse HEAD)" = "$pin"
git -C "$upstream" diff --exit-code "$pin" -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
lake build
lake env lean ConvexNivat.lean | tee "$work/axioms.log"
python3 "$upstream/scripts/check_axioms.py" ConvexNivat.lean "$work/axioms.log"
lake env leanchecker --verbose ConvexNivat
for unit in Rectangle Bridge; do
  source="StatementAudit/$unit.lean"
  lake env lean "$source" | tee "$work/$unit.log"
  python3 "$upstream/scripts/check_axioms.py" "$source" "$work/$unit.log"
done
for unit in Targets Rectangle Bridge; do
  lake env leanchecker --verbose "StatementAudit.$unit"
done
NIVAT_DEPENDENCY_TSV="$work/dependencies.tsv" lake env lean scripts/Dependencies.lean
cmp "$work/dependencies.tsv" evidence/direct-dependencies.tsv

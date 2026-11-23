#!/usr/bin/env bash
# Run after building the pinned upstream Nivat and Solution targets.
set -euo pipefail
cd "$(dirname "$0")/../.lake/packages/nivat"
export LEAN_NUM_THREADS=1
while IFS= read -r path; do
  module=${path%.lean}
  lake env leanchecker --verbose "${module//\//.}"
done < <(find Nivat -name '*.lean' | LC_ALL=C sort)
lake env leanchecker --verbose Solution
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Asking the CLI for "Nivat" selects its whole prefix in parallel.
# Invoke the same toolchain routine on the single root module here.
printf 'import LeanChecker\n#eval replayFromImports `Nivat\n' > "$work/RootReplay.lean"
lake env lean "$work/RootReplay.lean"
echo 'Root import module Nivat replayed. EXIT_CODE=0'

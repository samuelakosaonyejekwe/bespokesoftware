#!/bin/sh
# Every check that must pass before anything is published. Stops at the first failure.
#   sh tools/verify.sh          (about half an hour on a quiet machine)
set -e
cd "$(dirname "$0")/.."
echo "== models";        node tests/check-models.mjs | tail -1
echo "== equations";     node tests/check-consistency.mjs | tail -1
echo "== relations";     node tests/check-atlas.mjs | tail -1
echo "== prompts";       node tests/check-prompts.mjs | tail -1
echo "== reading";       node tests/check-reading.mjs | tail -1
echo "== sweeps";        node tests/check-sweeps.mjs | grep -v "^  "
echo "== whole ranges";  node tests/check-range.mjs | head -2
echo "all checks passed"

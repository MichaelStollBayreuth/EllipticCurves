#!/usr/bin/env bash

# Run the leanprover/comparator check for this project locally.
#
# Certifies that the repository proves the challenge statement(s) in the given config
# (default: the Mordell-Weil theorem). See comparator/README.md for what is checked.
#
# Requires three binaries; override any location via the environment:
#   COMPARATOR_BIN         the `comparator` binary (built from leanprover/comparator)
#   COMPARATOR_LEAN4EXPORT `lean4export`, built at THIS project's Lean version (tag v4.xx.0)
#   COMPARATOR_LANDRUN     `landrun`, built from its `main` branch
# NB: rebuild lean4export whenever the project's Lean version changes (see ~/lean4/UPDATE.md).

set -euo pipefail

COMPARATOR_BIN="${COMPARATOR_BIN:-$HOME/lean4/comparator/.lake/build/bin/comparator}"
: "${COMPARATOR_LEAN4EXPORT:=$HOME/lean4/lean4export/.lake/build/bin/lean4export}"
: "${COMPARATOR_LANDRUN:=$HOME/go/bin/landrun}"
export COMPARATOR_LEAN4EXPORT COMPARATOR_LANDRUN
export PATH="$(dirname "$COMPARATOR_LANDRUN"):$PATH"

# Config file to check (default: the Mordell-Weil theorem).
CONFIG="${1:-comparator/fg_point_of_numberField.json}"

# Move to the repository root (this script lives in scripts/).
cd "$(dirname "$0")/.."

# Fail early with a helpful message if a binary is missing.
for bin in "$COMPARATOR_BIN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_LANDRUN"; do
  if [ ! -x "$bin" ]; then
    echo "ERROR: comparator binary not found or not executable: $bin" >&2
    echo "See comparator/README.md for how to build/install it; override via env vars." >&2
    exit 1
  fi
done

# Ensure the library oleans are current so the sandboxed Solution build reuses them.
lake build EllipticCurves

# Run the check (exit 0 and "Your solution is okay!" = certified).
exec lake env "$COMPARATOR_BIN" "$CONFIG"

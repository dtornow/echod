#!/usr/bin/env bash
# Verify the kernel with Verus. VERUS_DIR is a Verus source tree with a
# release build in target-verus/release (see BUILD.md in verus-lang/verus).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
VERUS_DIR="${VERUS_DIR:-$HOME/verus-lang/verus/source}"
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-$VERUS_DIR/z3}"
export PATH="$VERUS_DIR/target-verus/release:$PATH"
exec cargo verus verify -p echod-kernel -- --triggers-mode silent --multiple-errors 12 "$@"

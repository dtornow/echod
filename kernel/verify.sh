#!/usr/bin/env bash
# Verify the kernel with Verus. VERUS_DIR is a Verus source tree with a
# release build in target-verus/release (see BUILD.md in verus-lang/verus).
#
# The kernel has no dependencies under Verus (serde is cfg'd away), so the
# verifier runs on the crate root directly. `cargo build` is the other
# compiler: the same sources with the ghost code erased.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
VERUS_DIR="${VERUS_DIR:-$HOME/verus-lang/verus/source}"
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-$VERUS_DIR/z3}"
exec "$VERUS_DIR/target-verus/release/verus" --crate-type=lib src/lib.rs \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

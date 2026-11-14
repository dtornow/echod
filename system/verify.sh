#!/usr/bin/env bash
# Verify the system model with Verus. VERUS_DIR is a Verus source tree with a
# release build in target-verus/release (see BUILD.md in verus-lang/verus).
#
# The system imports the kernel: its documents are kernel states and its
# node's actions are the kernel's node, commit and step functions. The
# kernel is verified first and
# exported — its Verus metadata and an rlib compiled by Verus's own rustc —
# into the kernel's target-verus/, and imported here. `cargo build` is the
# other compiler: the same sources with the ghost code erased.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

if [[ -x /tmp/verus-release/verus-x86-linux/verus ]]; then
  VERUS=/tmp/verus-release/verus-x86-linux/verus
  export VERUS_Z3_PATH="${VERUS_Z3_PATH:-/tmp/verus-release/verus-x86-linux/z3}"
else
  VERUS_DIR="${VERUS_DIR:-$HOME/verus-lang/verus/source}"
  VERUS="$VERUS_DIR/target-verus/release/verus"
  export VERUS_Z3_PATH="${VERUS_Z3_PATH:-$VERUS_DIR/z3}"
fi

KERNEL=../kernel
OUT="$KERNEL/target-verus"
VIR="$OUT/echod_kernel.vir"
RLIB="$OUT/libechod_kernel.rlib"
if [ ! -f "$VIR" ] || [ ! -f "$RLIB" ] || [ -n "$(find "$KERNEL/src" -newer "$VIR" -name '*.rs')" ]; then
  echo "exporting the kernel" >&2
  mkdir -p "$OUT"
  (cd "$KERNEL" && ./verify.sh --export "$PWD/target-verus/echod_kernel.vir" --compile --out-dir "$PWD/target-verus" --crate-name echod_kernel)
fi
exec "$VERUS" --crate-type=lib src/lib.rs \
  --import "echod_kernel=$VIR" --extern "echod_kernel=$RLIB" -L "$OUT" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

#!/usr/bin/env bash
# Verify the executable codec and its round-trip laws against the kernel types.
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
if [[ ! -f "$VIR" || ! -f "$RLIB" ]] || [[ -n "$(find "$KERNEL/src" -newer "$VIR" -name '*.rs' -print -quit)" ]]; then
  mkdir -p "$OUT"
  (cd "$KERNEL" && "$VERUS" --crate-type=lib src/lib.rs \
    --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check \
    --export "$PWD/target-verus/echod_kernel.vir" \
    --compile --out-dir "$PWD/target-verus" --crate-name echod_kernel)
fi

exec "$VERUS" --crate-type=lib src/lib.rs \
  --import "echod_kernel=$VIR" --extern "echod_kernel=$RLIB" -L "$OUT" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

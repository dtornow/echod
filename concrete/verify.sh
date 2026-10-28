#!/usr/bin/env bash
# Verify the row-native Concrete model against the exported kernel.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
VERUS_DIR="${VERUS_DIR:-$HOME/verus-lang/verus/source}"
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-$VERUS_DIR/z3}"
KERNEL=../kernel
OUT="$KERNEL/target-verus"
VIR="$OUT/echod_kernel.vir"
RLIB="$OUT/libechod_kernel.rlib"
if [ ! -f "$VIR" ] || [ ! -f "$RLIB" ] || [ -n "$(find "$KERNEL/src" -newer "$VIR" -name '*.rs')" ]; then
  echo "exporting the kernel" >&2
  mkdir -p "$OUT"
  (cd "$KERNEL" && ./verify.sh --export "$PWD/target-verus/echod_kernel.vir" --compile --out-dir "$PWD/target-verus" --crate-name echod_kernel)
fi
exec "$VERUS_DIR/target-verus/release/verus" --crate-type=lib src/lib.rs \
  --import "echod_kernel=$VIR" --extern "echod_kernel=$RLIB" -L "$OUT" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

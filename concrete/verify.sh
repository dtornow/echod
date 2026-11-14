#!/usr/bin/env bash
# Verify the document-bucket Concrete model against the exported kernel.
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
KERNEL_OUT="$KERNEL/target-verus"
KERNEL_VIR="$KERNEL_OUT/echod_kernel.vir"
KERNEL_RLIB="$KERNEL_OUT/libechod_kernel.rlib"
if [ ! -f "$KERNEL_VIR" ] || [ ! -f "$KERNEL_RLIB" ] || [ -n "$(find "$KERNEL/src" -newer "$KERNEL_VIR" -name '*.rs')" ]; then
  echo "exporting the kernel" >&2
  mkdir -p "$KERNEL_OUT"
  (cd "$KERNEL" && ./verify.sh --export "$PWD/target-verus/echod_kernel.vir" --compile --out-dir "$PWD/target-verus" --crate-name echod_kernel)
fi
CODEC=../codec
CODEC_OUT="$CODEC/target-verus"
CODEC_VIR="$CODEC_OUT/echod_codec.vir"
CODEC_RLIB="$CODEC_OUT/libechod_codec.rlib"
if [ ! -f "$CODEC_VIR" ] || [ ! -f "$CODEC_RLIB" ] || [ -n "$(find "$CODEC/src" -newer "$CODEC_VIR" -name '*.rs')" ]; then
  echo "exporting the codec" >&2
  mkdir -p "$CODEC_OUT"
  (cd "$CODEC" && ./verify.sh --export "$PWD/target-verus/echod_codec.vir" --compile --out-dir "$PWD/target-verus" --crate-name echod_codec)
fi
exec "$VERUS" --crate-type=lib src/lib.rs \
  --import "echod_kernel=$KERNEL_VIR" --extern "echod_kernel=$KERNEL_RLIB" \
  --import "echod_codec=$CODEC_VIR" --extern "echod_codec=$CODEC_RLIB" \
  -L "$KERNEL_OUT" -L "$CODEC_OUT" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

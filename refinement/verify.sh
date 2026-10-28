#!/usr/bin/env bash
# Verify the local Concrete-to-Abstract refinement boundary.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

if [[ -x /tmp/verus-release/verus-x86-linux/verus ]]; then
  VERUS=/tmp/verus-release/verus-x86-linux/verus
  export VERUS_Z3_PATH="${VERUS_Z3_PATH:-/tmp/verus-release/verus-x86-linux/z3}"
else
  VERUS_DIR="${VERUS_DIR:-$HOME/verus-lang/verus/source}"
  VERUS="$VERUS_DIR/target-verus/release/verus"
  export VERUS_Z3_PATH="${VERUS_Z3_PATH:-$VERUS_DIR/z3}"
fi

mkdir -p kernel/target-verus abstract/target-verus concrete/target-verus

"$VERUS" --crate-type=lib kernel/src/lib.rs \
  --export kernel/target-verus/echod_kernel.vir \
  --compile --out-dir kernel/target-verus --crate-name echod_kernel \
  --triggers-mode silent --multiple-errors 20 --no-auto-recommends-check

"$VERUS" --crate-type=lib abstract/src/lib.rs \
  --export abstract/target-verus/echod_abstract.vir \
  --compile --out-dir abstract/target-verus --crate-name echod_abstract \
  --triggers-mode silent --multiple-errors 20 --no-auto-recommends-check

"$VERUS" --crate-type=lib concrete/src/lib.rs \
  --import echod_kernel=kernel/target-verus/echod_kernel.vir \
  --extern echod_kernel=kernel/target-verus/libechod_kernel.rlib \
  -L kernel/target-verus \
  --export concrete/target-verus/echod_concrete.vir \
  --compile --out-dir concrete/target-verus --crate-name echod_concrete \
  --triggers-mode silent --multiple-errors 20 --no-auto-recommends-check

"$VERUS" --crate-type=lib refinement/src/lib.rs \
  --import echod_kernel=kernel/target-verus/echod_kernel.vir \
  --extern echod_kernel=kernel/target-verus/libechod_kernel.rlib \
  --import echod_abstract=abstract/target-verus/echod_abstract.vir \
  --extern echod_abstract=abstract/target-verus/libechod_abstract.rlib \
  --import echod_concrete=concrete/target-verus/echod_concrete.vir \
  --extern echod_concrete=concrete/target-verus/libechod_concrete.rlib \
  -L kernel/target-verus -L abstract/target-verus -L concrete/target-verus \
  --triggers-mode silent --multiple-errors 20 --no-auto-recommends-check

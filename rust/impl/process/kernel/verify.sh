#!/usr/bin/env bash
# Verify the concrete specification, then the kernel against it.
#
# Verus does not read Cargo's dependency graph. This builds echod_concrete
# first and passes that rlib to the kernel, which is what `promise_create`'s
# ensures names. `cargo build` is the other compiler: the same sources with
# the ghost code erased. serde and the abstract model are cfg'd out of the
# Verus run; cargo still typechecks both.
#
# Extra arguments are forwarded to both Verus invocations.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
VERUS_DIR="${VERUS_DIR:-$HOME/verus-lang/verus/source}"
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-$VERUS_DIR/z3}"
VERUS="$VERUS_DIR/target-verus/release/verus"
OUT="${TMPDIR:-/tmp}/echod-verus"
mkdir -p "$OUT"

"$VERUS" --crate-type=lib --crate-name echod_concrete \
  ../../../spec/concrete/src/lib.rs \
  --out-dir "$OUT" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

exec "$VERUS" --crate-type=lib --crate-name echod_kernel src/lib.rs \
  --extern "echod_concrete=$OUT/libechod_concrete.rlib" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

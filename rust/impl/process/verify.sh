#!/usr/bin/env bash
# Verify the concrete specification, then the proved modules of the process.
#
# Verus does not read Cargo's dependency graph, and it does not load the
# rest of this crate: the protocol, the cache, and the store-call machines
# stay outside this run. This builds echod_types, then echod_concrete,
# and passes those rlibs to src/verified/mod.rs, which is what a handler's
# ensures names.
# `cargo build` is the other compiler: the same sources with the ghost
# code erased. serde and the abstract model are cfg'd out of the Verus
# run; cargo still typechecks both.
#
# Extra arguments are forwarded to each Verus invocation.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
VERUS_DIR="${VERUS_DIR:-$HOME/verus-lang/verus/source}"
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-$VERUS_DIR/z3}"
VERUS="$VERUS_DIR/target-verus/release/verus"
OUT="${TMPDIR:-/tmp}/echod-verus"
mkdir -p "$OUT"

"$VERUS" --crate-type=lib --crate-name echod_types \
  ../../comm/types/src/lib.rs \
  --out-dir "$OUT" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

"$VERUS" --crate-type=lib --crate-name echod_concrete \
  ../../spec/concrete/src/lib.rs \
  --extern "echod_types=$OUT/libechod_types.rlib" \
  --out-dir "$OUT" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

exec "$VERUS" --crate-type=lib --crate-name echod_logic \
  src/verified/mod.rs \
  --extern "echod_types=$OUT/libechod_types.rlib" \
  --extern "echod_concrete=$OUT/libechod_concrete.rlib" \
  --triggers-mode silent --multiple-errors 12 --no-auto-recommends-check "$@"

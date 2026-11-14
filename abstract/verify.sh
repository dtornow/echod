#!/usr/bin/env bash
# Verify directly, then prove that the crate also builds in a workspace whose
# only member is this crate. No echod crate is available in that build.
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

"$VERUS" --crate-type=lib src/lib.rs \
  --triggers-mode silent --multiple-errors 20 --no-auto-recommends-check "$@"

reduced="$(mktemp -d)"
trap 'rm -rf "$reduced"' EXIT
mkdir -p "$reduced/abstract"
cp -R Cargo.toml src tests "$reduced/abstract/"
cat >"$reduced/Cargo.toml" <<'EOF'
[workspace]
resolver = "2"
members = ["abstract"]
EOF
if rustup toolchain list | grep -q '^1.99.1-x86_64-unknown-linux-gnu'; then
  RUSTUP_TOOLCHAIN=1.99.1-x86_64-unknown-linux-gnu \
    cargo test --manifest-path "$reduced/Cargo.toml" -p echod-abstract
else
  cargo test --manifest-path "$reduced/Cargo.toml" -p echod-abstract
fi

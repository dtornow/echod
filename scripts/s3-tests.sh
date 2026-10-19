#!/usr/bin/env bash
# Run the store contract tests and the end-to-end tests against a real S3
# API. By default the Rust emulator `s3s-fs` (cargo install s3s-fs --features
# binary), started here on a temporary directory. With RUSTFS set to a RustFS
# binary (the other Rust S3 server, releases at github.com/rustfs/rustfs),
# RustFS instead, which also honours conditional reads and makes versions
# from content as S3 does. With ECHOD_STORE set, a store you name.
#
#   scripts/s3-tests.sh                                   # s3s-fs
#   RUSTFS=~/rustfs scripts/s3-tests.sh                   # RustFS
#   ECHOD_STORE=s3://my-bucket scripts/s3-tests.sh        # a real bucket, credentials from the environment
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [ -z "${ECHOD_STORE:-}" ]; then
  root="$(mktemp -d)"
  if [ -n "${RUSTFS:-}" ]; then
    "$RUSTFS" server --address 127.0.0.1:9000 --access-key k --secret-key s --region us-east-1 "$root" >"$root/rustfs.log" 2>&1 &
    pid=$!
    export AWS_ACCESS_KEY_ID=k AWS_SECRET_ACCESS_KEY=s ECHOD_ENDPOINT=http://127.0.0.1:9000
    for _ in $(seq 1 30); do curl -s -o /dev/null http://127.0.0.1:9000/ && break; sleep 1; done
    cargo run -q -p echod-server --example mkbucket -- echod "$ECHOD_ENDPOINT"
  else
    mkdir -p "$root/echod"
    s3s-fs --host 127.0.0.1 --port 8014 --access-key k --secret-key s "$root" >"$root/s3s.log" 2>&1 &
    pid=$!
    export AWS_ACCESS_KEY_ID=k AWS_SECRET_ACCESS_KEY=s ECHOD_ENDPOINT=http://127.0.0.1:8014
    sleep 1
  fi
  trap 'kill $pid 2>/dev/null; rm -rf "$root"' EXIT
  export ECHOD_STORE=s3://echod ECHOD_REGION=us-east-1
fi
cargo test -p echod-server --test store "$@"
cargo test -p echod-server --test e2e "$@"

#!/usr/bin/env bash
# Run the store contract tests and the end-to-end tests against an S3 API.
# By default `fakes3` (rust/test/cli/fakes3), built here: the S3 surface
# echod uses, in memory, including the S3 Express appends no other emulator
# serves, so both clients run, the object_store one and the SDK one. With
# RUSTFS set to a RustFS binary (releases at github.com/rustfs/rustfs) or
# S3S_FS=1 (cargo install s3s-fs --features binary), one of those instead:
# a second implementation's reading of conditional writes, without appends.
# With ECHOD_STORE set, a store you name; ECHOD_EXPRESS_BUCKET names a
# directory bucket for the appending client, if you have one.
#
#   scripts/s3-tests.sh                                   # fakes3
#   RUSTFS=~/rustfs scripts/s3-tests.sh                   # RustFS
#   S3S_FS=1 scripts/s3-tests.sh                          # s3s-fs
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
    cargo run -q -p echod-runtime --example mkbucket -- echod "$ECHOD_ENDPOINT"
  elif [ -n "${S3S_FS:-}" ]; then
    mkdir -p "$root/echod"
    s3s-fs --host 127.0.0.1 --port 8014 --access-key k --secret-key s "$root" >"$root/s3s.log" 2>&1 &
    pid=$!
    export AWS_ACCESS_KEY_ID=k AWS_SECRET_ACCESS_KEY=s ECHOD_ENDPOINT=http://127.0.0.1:8014
    sleep 1
  else
    cargo build -q -p fakes3
    "${CARGO_TARGET_DIR:-target}/debug/fakes3" --address 127.0.0.1:9000 --bucket echod --bucket echod-express >"$root/fakes3.log" 2>&1 &
    pid=$!
    export AWS_ACCESS_KEY_ID=k AWS_SECRET_ACCESS_KEY=s ECHOD_ENDPOINT=http://127.0.0.1:9000 ECHOD_EXPRESS_BUCKET=echod-express
    for _ in $(seq 1 30); do curl -s -o /dev/null http://127.0.0.1:9000/ && break; sleep 1; done
  fi
  trap 'kill $pid 2>/dev/null; rm -rf "$root"' EXIT
  export ECHOD_STORE=s3://echod ECHOD_REGION=us-east-1
fi
cargo test -p echod-store-tests --test store "$@"
cargo test -p echod-store-tests --test e2e "$@"

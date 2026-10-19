#!/usr/bin/env bash
# Run the store conformance tests and the end-to-end tests against a real S3
# API: by default the Rust emulator `s3s-fs` (cargo install s3s-fs --features
# binary), started here on a temporary directory; or a bucket you name.
#
#   scripts/s3-tests.sh                       # emulator
#   ECHOD_S3_BUCKET=my-bucket scripts/s3-tests.sh   # a real bucket, credentials from the environment
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [ -z "${ECHOD_S3_BUCKET:-}" ]; then
  root="$(mktemp -d)"
  mkdir -p "$root/echod"
  s3s-fs --host 127.0.0.1 --port 8014 --access-key k --secret-key s "$root" >"$root/s3s.log" 2>&1 &
  pid=$!
  trap 'kill $pid 2>/dev/null; rm -rf "$root"' EXIT
  sleep 1
  export AWS_ACCESS_KEY_ID=k AWS_SECRET_ACCESS_KEY=s ECHOD_S3_ENDPOINT=http://127.0.0.1:8014 ECHOD_S3_BUCKET=echod
fi
cargo test -p echod-server --test s3_store "$@"
cargo test -p echod-server --test e2e "$@"

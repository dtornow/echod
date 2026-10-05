#!/bin/sh
# Fetches Porcupine (MIT, github.com/anishathalye/porcupine) at a pinned commit,
# for its test histories (test_data/jepsen, test_data/kv) and its Go benchmarks.
set -e
cd "$(dirname "$0")"
if [ ! -d porcupine ]; then
  git clone -q https://github.com/anishathalye/porcupine.git
fi
git -C porcupine checkout -q 97cd067defd99df172053ba7f4ca5bbae57fe446

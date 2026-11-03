#!/usr/bin/env bash
set -euo pipefail

concrete="$(dirname "$0")/../src/concrete"

if rg -n \
  'import .*abstract|Resonate\.(run|runWork|handleExternal)|Direct\.' \
  "$concrete"
then
  echo "a concrete file imports or invokes an abstract transition" >&2
  exit 1
fi

echo "concrete architecture check passed"

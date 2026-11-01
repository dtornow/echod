#!/usr/bin/env bash
set -euo pipefail

model="$(dirname "$0")/../concrete/Model.lean"

if rg -n \
  'import .*abstract|Resonate\.(run|runWork|handleExternal)|Direct\.' \
  "$model"
then
  echo "concrete Model imports or invokes an abstract transition" >&2
  exit 1
fi

echo "concrete architecture check passed"

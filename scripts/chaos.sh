#!/usr/bin/env bash
# echod as deployed, under real faults: the fleet of compose.yaml (three
# nodes over fakes3, each behind a chaos-agent) built, brought up, driven by
# echod-chaos for a while with nodes crashed, stopped, frozen, partitioned
# and slowed, then healed, settled, read back and checked; then torn down.
# The report lands in target/chaos/chaos.json, the fleet's logs beside it.
#
#   scripts/chaos.sh                        # seed 1, a minute of faults
#   scripts/chaos.sh --seed 7 --duration-secs 120
#   scripts/chaos.sh --no-chaos             # the same run on a healthy fleet
#   scripts/chaos.sh --keep                 # leave the fleet up afterwards
#   COMPOSE="podman compose" scripts/chaos.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [ -z "${COMPOSE:-}" ]; then
  if docker compose version >/dev/null 2>&1; then
    COMPOSE="docker compose"
  elif podman compose version >/dev/null 2>&1; then
    COMPOSE="podman compose"
  elif command -v podman-compose >/dev/null 2>&1; then
    COMPOSE="podman-compose"
  else
    echo "chaos.sh: neither docker compose nor podman compose is here" >&2
    exit 2
  fi
fi
keep=
export COMPOSE_PROJECT_NAME="echod-chaos-$(date +%s)-$$"
while [ $# -gt 0 ]; do
  case "$1" in
    --seed) export CHAOS_SEED="$2"; shift 2 ;;
    --duration-secs) export CHAOS_DURATION_SECS="$2"; shift 2 ;;
    --every-ms) export CHAOS_EVERY_MS="$2"; shift 2 ;;
    --no-chaos) export CHAOS_NONE=true; shift ;;
    --keep) keep=1; shift ;;
    *) echo "chaos.sh: unknown argument $1" >&2; exit 2 ;;
  esac
done
mkdir -p target/chaos
finish() {
  $COMPOSE --profile chaos logs --no-color --timestamps >target/chaos/logs.txt 2>&1 || true
  if [ -z "$keep" ]; then
    $COMPOSE --profile chaos down --timeout 5 >/dev/null 2>&1 || true
  fi
}
trap finish EXIT
$COMPOSE --profile chaos up --build --abort-on-container-exit --exit-code-from chaos

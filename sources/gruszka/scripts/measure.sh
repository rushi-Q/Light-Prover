#!/bin/bash
CAP=${CAP:-$(cd "$(dirname "$0")" && pwd)/capped}
# Measures gruszka on a .susz file: verdict, instructions, cycles, wall,
# max RSS, peak footprint. Takes the shared measure.lock (mkdir; waits while
# another holds it; releases after the batch). Usage:
#   measure.sh FILE "WORKERS..." RUNS [MB] [SECONDS]
# ARGS (milestone 26) goes before FILE, e.g. ARGS="--only Int.neg_ediv";
# BIN may be another kernel taking FILE WORKERS (Pestka's main).
S=${GRUSZKA_WORK:-${TMPDIR:-/tmp}/gruszka-work}
BIN=${BIN:-$(cd "$(dirname "$0")/.." && pwd)/target/release/gruszka}
F=$1; WS=${2:-1}; RUNS=${3:-3}; MB=${4:-8000}; SECS=${5:-900}
LOCK=$S/measure.lock
until mkdir $LOCK 2>/dev/null; do sleep 5; done
trap 'rmdir $LOCK' EXIT
echo "# $(date '+%F %T') $(pmset -g batt | head -1 | sed "s/Now drawing from //") $(git -C ${GRUSZKA_DIR:-$(cd "$(dirname "$0")/.." && pwd)} rev-parse --short HEAD) $(basename $F) $(basename $BIN)"
cat $F > /dev/null
for w in $WS; do
  for r in $(seq 1 $RUNS); do
    out=$( { "$CAP" $MB $SECS /usr/bin/time -l $BIN $ARGS $F $w; } 2>&1 )
    v=$(echo "$out" | grep -E "^(accepted|rejected|declined|checked|index invalid)" | head -1 | cut -c1-${VW:-60})
    echo "$out" | awk -v w=$w -v v="$v" '
      /real/ {wall=$1} /maximum resident/ {rss=$1/1048576} /instructions retired/ {ins=$1/1e9}
      /cycles elapsed/ {cyc=$1/1e9} /peak memory footprint/ {fp=$1/1048576}
      END {printf "workers %d  wall %6.2f s  instr %8.2f G  cycles %7.2f G  maxRSS %6.0f MiB  footprint %6.0f MiB  %s\n", w, wall, ins, cyc, rss, fp, v}'
  done
done

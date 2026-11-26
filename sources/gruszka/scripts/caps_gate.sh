#!/bin/bash
CAP=${CAP:-$(cd "$(dirname "$0")" && pwd)/capped}
# Milestone 19: the full paths of the reserved ranges, on a knobs build.
# A block arena of SK_SLAB_IDS ids and worker slabs of SK_TABLE_CAP entries
# must make a declaration decline (never crash, never accept a bad file):
# Init at 1 and 4 workers with each cap declines with the expected
# message (SK_SLAB_IDS caps the overflow arenas too), and the bad vectors
# are still rejected or declined.
# Usage: caps_gate.sh KNOBS_BIN; prints CAPSDONE bad=N.
D=${GRUSZKA_DIR:-$(cd "$(dirname "$0")/.." && pwd)}
S=${GRUSZKA_WORK:-${TMPDIR:-/tmp}/gruszka-work}
BIN=$1
bad=0
for w in 1 4; do
  r=$(SK_SLAB_IDS=8192 "$CAP" 4000 120 $BIN $S/sz/init.susz $w 2>/dev/null | tail -1)
  echo "slab ids 8192 w$w: $r"; case "$r" in "declined: "*"block arena is full"*) ;; *) bad=1;; esac
  r=$(SK_TABLE_CAP=4096 "$CAP" 4000 120 $BIN $S/sz/init.susz $w 2>/dev/null | tail -1)
  echo "table cap 4096 w$w: $r"; case "$r" in "declined: "*"worker table is full"*) ;; *) bad=1;; esac
done
# slabs small enough to be filled, but each a range of its own: Init
# accepted poisoned at 4 and 8 workers (slabs that overlap corrupt it)
for w in 4 8; do
  r=$(SK_POISON=1 SK_SLAB_IDS=131072 "$CAP" 4000 120 $BIN $S/sz/init.susz $w 2>/dev/null | tail -1)
  echo "slab ids 131072 poison w$w: $r"; case "$r" in accepted*) ;; *) bad=1;; esac
done
# milestone 35: a declaration whose blocks do not fit its worker's arena
# runs again in the overflow arenas, so the verdict does not depend on the
# arena size (FLT at 192 workers declined): slabs of 8192 ids with the
# overflow arenas at their default size, Init and con-leche accepted
# poisoned at 4 and 8 workers, and declarations ran there
for c in init con-leche; do
  for w in 4 8; do
    o=$(SK_POISON=1 SK_SLAB_IDS=8192 SK_BIG_IDS=0 "$CAP" 6000 600 $BIN $S/sz/$c.susz $w 2>&1)
    r=$(echo "$o" | tail -1); n=$(echo "$o" | awk '/^note: worker .* overflow/ {n += $4} END {print n + 0}')
    echo "slab ids 8192, overflow default, poison $c w$w: $r ($n overflow runs)"
    case "$r" in accepted*) [ "$n" -gt 0 ] || bad=1;; *) bad=1;; esac
  done
done
for f in $D/tests/adv/bad_*.ndjson; do
  for env in SK_SLAB_IDS=8192 SK_TABLE_CAP=64; do
    r=$(env $env "$CAP" 2000 60 $BIN $f 1 2>/dev/null | tail -1)
    case "$r" in rejected*|declined*) ;; *) echo "$env $(basename $f): $r"; bad=1;; esac
  done
done
echo "CAPSDONE bad=$bad"
exit $bad

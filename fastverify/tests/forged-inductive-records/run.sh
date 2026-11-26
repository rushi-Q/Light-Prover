#!/bin/bash
# tests/forged-inductive-records/run.sh [FV_ROOT]: the pinned official-kernel leg (PIN
# pleanchecker of check/sound/pins.env, run exactly like check-sound.sh's wrapper: -jT -v, LEAN_STACK_SIZE_KB=917376) on
# exports whose inductive records differ from the kernel's (README.md). bad = must be rejected (exit 1); good = must be
# accepted (exit 0); either = the official 4.36 replay accepts it, the replay veto check C2 rejects it (both are correct policies).
set -u
FV=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}; X=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)/x
P=$(awk '$1=="PIN" && $2=="pleanchecker" {print $4}' "$FV/check/sound/pins.env"); T=${THREADS:-4}
pass=0; fail=0
for spec in T-honest:good Tonly-honest:good T-isrec-forged:either T-numidx-forged:either T-eta-honest-rec:bad \
            T-eta-forged-isrec:bad Tonly-allforged:bad T-allforged:bad T-ctor-forged:bad; do
  n=${spec%%:*}; want=${spec#*:}
  LEAN_STACK_SIZE_KB=917376 LEAN_ABORT_ON_PANIC=1 "$P" -j$T -v --from-export "$X/$n.export" > /dev/null 2>&1; rc=$?
  case "$want:$rc" in good:0|bad:1|either:0|either:1) echo "PASS $n ($want, rc=$rc)"; pass=$((pass+1));;
    *) echo "FAIL $n (want $want, rc=$rc)"; fail=$((fail+1));; esac
done
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]

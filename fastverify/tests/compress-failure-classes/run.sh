#!/bin/bash
# tests/compress-failure-classes/run.sh [WORK] : every Stage-3 failure-class regression test; RESULT PASS iff all pass
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); W=${1:-${SCRATCH:-${TMPDIR:-/tmp}}/$USER-compress-failure-classes}; mkdir -p "$W"
bad=0; n=0
for t in "$H"/*/run.sh; do
  [ -f "$t" ] || continue
  d=$(basename "$(dirname "$t")"); n=$((n + 1))
  out=$(bash "$t" "$W/$d" 2>&1); echo "$out" | grep -E '^(PASS|FAIL)' | sed "s/^/[$d] /"
  echo "$out" | grep -q '^RESULT PASS' || { echo "FAIL [$d] no RESULT PASS"; bad=1; }
done
[ $n = 0 ] && echo "PASS no failure classes recorded yet"
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

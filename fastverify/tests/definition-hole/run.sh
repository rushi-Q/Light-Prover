#!/bin/bash
# tests/definition-hole/run.sh [FV_ROOT]: a definition target that no theorem mentions must
# be axiom-checked: check-sound.sh REJECTS the solution whose hole is `sorry`, ACCEPTS the honest one (README.md).
set -u
FV=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}; X=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)/x
pass=0; fail=0
for spec in Solution:1 SolutionHonest:0; do
  n=${spec%%:*}; want=${spec#*:}
  "$FV/check/sound/check-sound.sh" "$X/$n.export" "$X/Challenge.export" "$X/comparator.json" --threads ${THREADS:-4} > /tmp/q04dh.$$ 2>&1; rc=$?
  if [ "$rc" = "$want" ]; then echo "PASS $n (rc=$rc)"; pass=$((pass+1)); else echo "FAIL $n (want $want, rc=$rc): $(tail -1 /tmp/q04dh.$$ | cut -c1-200)"; fail=$((fail+1)); fi
done
rm -f /tmp/q04dh.$$; echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]

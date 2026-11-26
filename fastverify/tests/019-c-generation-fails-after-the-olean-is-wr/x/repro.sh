#!/bin/bash
# Self-contained repro: OFFICIAL flow (lake build 4.33.1 + official lean4export + lake comparator 4.36)
# vs FAST flow (fastverify/pipeline/pipeline.sh + pchk run.sh) on the crafted project ./proj with the challenge ./challenge.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-019}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"
echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"

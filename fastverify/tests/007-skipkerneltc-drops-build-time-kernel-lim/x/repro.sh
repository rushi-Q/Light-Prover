#!/bin/bash
# Self-contained repro. Each crafted project proj/<case> is run through the OFFICIAL flow (lake build 4.33.1
# with the project's own lakefile + official lean4export v4.33.0 + unmodified lake comparator 4.36) and the FAST flow
# (fastverify/pipeline/pipeline.sh + pchk run.sh, see fastflow.sh for the host caveats).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-007}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; S=""
for c in a b c; do
  cp -a "$D/proj/$c" "$W/$c"
  echo "######## case $c"
  bash "$D/officialflow.sh" "$W/$c" "$W/official-$c" "$W/challenge"; orc=$?
  bash "$D/fastflow.sh" "$W/$c" "$W/fast-$c" "$W/challenge/challenge.export"; frc=$?
  S="$S case $c: official_rc=$orc fast_rc=$frc;"
done
echo "=== SUMMARY$S (0 = ACCEPTED)"

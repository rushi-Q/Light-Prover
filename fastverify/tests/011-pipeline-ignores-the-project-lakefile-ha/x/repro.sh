#!/bin/bash
# Self-contained repro. Three crafted projects (proj/a, proj/b, proj/c), each run through the OFFICIAL flow
# (lake build 4.33.1 with the project's own lakefile + official lean4export + lake comparator 4.36) and the FAST flow
# (fastverify/pipeline/pipeline.sh + pchk run.sh). ~1 min.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-011}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; S=""
for c in a b c d e f g h i; do
  cp -a "$D/proj/$c" "$W/$c"
  echo "######## case $c: $(sed -n 1p "$W/$c/src/Main.lean")"
  bash "$D/officialflow.sh" "$W/$c" "$W/official-$c" "$W/challenge"; orc=$?
  if [ -z "${FAST_PIPELINE_DIR:-}" ] && { [ $c = h ] || [ $c = i ]; }; then
    # cases h, i: the pipeline's DEPLOYED default pkgmode=local (case h needs its LEAN_PATH_PRE core-lib copy)
    PD=$W/pipeline-local-$c; rm -rf "$PD"; cp -a $LIGHT_LEAN/fastverify/pipeline "$PD"; echo off > "$PD/native.txt"
    FAST_PIPELINE_DIR=$PD bash "$D/fastflow.sh" "$W/$c" "$W/fast-$c" "$W/challenge/challenge.export"; frc=$?
  else
    bash "$D/fastflow.sh" "$W/$c" "$W/fast-$c" "$W/challenge/challenge.export"; frc=$?
  fi
  S="$S case $c: official_rc=$orc fast_rc=$frc;"
done
echo "=== SUMMARY$S (0 = ACCEPTED)"

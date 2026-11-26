#!/bin/bash
# ablate2.sh CORPUS OUTROOT THREADS REPEATS CASE : AMD-server ablation of the sound preset's build items on one small case
# (challenge given): sound | sound without the zygote items | sound with only the PGO toolchain + skip-kernel-tc +
# linter-off | sound --build B0 | export-in (sound --from-export of the case's own export: check stage only)
set -u
H=$(dirname "$(readlink -f "$0")")
C=$1; R=$2; T=$3; N=$4; CASE=$5
T1="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo"
NOZY="$T1,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,j1-saturated,sound-fast-path,cost-hints,native-pkg,merge,check-tail"
for i in $(seq 1 "$N"); do
  RUNTAG=r$i        "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given
  RUNTAG=nozy.r$i   "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --unsafe "$NOZY"
  RUNTAG=pgomin.r$i "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --unsafe "$T1,skip-kernel-tc,linter-off"
  RUNTAG=B0.r$i     "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --build B0 --export-dir none
  E=$R/runs/$CASE.sound.B0.r$i/solution.export
  [ -s "$E" ] && RUNTAG=exin.r$i "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --from-export "$E"
done

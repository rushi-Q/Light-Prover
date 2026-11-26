#!/bin/bash
# ablate.sh CORPUS OUTROOT THREADS REPEATS CASE : fixed-cost ablation of the sound preset on one small case (challenge
# export given = OUTROOT/given/CASE). Configurations (explicit flags override the preset):
#   sound | sound-min (--unsafe skip-kernel-tc,linter-off) | sound-B1 (--build B1) | sound-B0 (--build B0) |
#   sound-noovl (--overlap-targets none --export-dir none) | reference | fast-exact
set -u
H=$(dirname "$(readlink -f "$0")")
C=$1; R=$2; T=$3; N=$4; CASE=$5
for i in $(seq 1 "$N"); do
  RUNTAG=r$i            "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given
  RUNTAG=min.r$i        "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --unsafe skip-kernel-tc,linter-off
  RUNTAG=B1.r$i         "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --build B1
  RUNTAG=B0.r$i         "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --build B0
  RUNTAG=noovl.r$i      "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --overlap-targets none --export-dir none
  RUNTAG=r$i            "$H/run1.sh" "$C" "$CASE" reference "$R" "$T" given
  RUNTAG=r$i            "$H/run1.sh" "$C" "$CASE" fast-exact "$R" "$T" given
done

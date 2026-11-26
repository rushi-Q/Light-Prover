#!/bin/bash
# lane.sh CORPUS OUTROOT THREADS PRESETS CASE... : for every case: reference (challenge built officially) -> given
# challenge export -> every preset of PRESETS (comma list, e.g. sound,fast-exact) with the pinned given challenge.
set -u
H=$(dirname "$(readlink -f "$0")")
C=$1; R=$2; T=$3; PS=$4; shift 4
for CASE in "$@"; do
  if [ ! -s "$R/given/$CASE/challenge.export" ]; then
    "$H/run1.sh" "$C" "$CASE" reference "$R" "$T" src
    "$H/mkgiven.sh" "$C" "$R" "$CASE" || continue
  fi
  for P in ${PS//,/ }; do "$H/run1.sh" "$C" "$CASE" "$P" "$R" "$T" given; done
done
echo "LANE DONE $*" >> "$R/lanes.log"

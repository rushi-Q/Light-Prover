#!/bin/bash
# lane2.sh CORPUS OUTROOT THREADS CASE... : reference (challenge built officially) -> pinned challenge export ->
# --preset sound, --preset sound --build B0 (official lake build + E1 + CS) and --preset fast-exact for every case
# (LANE2_PRESETS overrides the list: e.g. "sound sound-B0").
set -u
H=$(dirname "$(readlink -f "$0")")
C=$1; R=$2; T=$3; shift 3
for CASE in "$@"; do
  if [ ! -s "$R/given/$CASE/challenge.export" ]; then
    "$H/run1.sh" "$C" "$CASE" reference "$R" "$T" src
    "$H/mkgiven.sh" "$C" "$R" "$CASE" || continue
  fi
  for P in ${LANE2_PRESETS:-sound sound-B0 fast-exact}; do
    case $P in
      sound-B0) RUNTAG=B0 "$H/run1.sh" "$C" "$CASE" sound "$R" "$T" given --build B0 ;;
      *) "$H/run1.sh" "$C" "$CASE" "$P" "$R" "$T" given ;;
    esac
  done
done
echo "LANE DONE $*" >> "$R/lanes.log"

#!/bin/bash
# lane3.sh CORPUS OUTROOT THREADS CASE... : failing attempts: reference -> given -> sound, sound --no-confirm-build-failure,
# sound --build B0, fast-exact
set -u
H=$(dirname "$(readlink -f "$0")")
C=$1; R=$2; T=$3; shift 3
for c in "$@"; do
  "$H/run1.sh" "$C" "$c" reference "$R" "$T" src && "$H/mkgiven.sh" "$C" "$R" "$c" || continue
  "$H/run1.sh" "$C" "$c" sound "$R" "$T" given
  RUNTAG=noconfirm "$H/run1.sh" "$C" "$c" sound "$R" "$T" given --no-confirm-build-failure
  RUNTAG=B0 "$H/run1.sh" "$C" "$c" sound "$R" "$T" given --build B0
  "$H/run1.sh" "$C" "$c" fast-exact "$R" "$T" given
done

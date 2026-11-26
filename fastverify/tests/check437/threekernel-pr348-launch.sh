#!/bin/bash
# threekernel-pr348-launch.sh [THREADS] - wait for the PR #348 export copy (sha256 a0b2ade4...) to be
# complete and sha-verified, then run the three-kernel record with the encapsulated replay (staged wiring v2.2 + pins-437e
# + the hide list) against the pinned RH challenge. Nothing here decides anything; the results are the JSON/TSV of the check.
set -u
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=${FV_PKG:-$(cd "$HERE/../.." && pwd)}   # the package under test unless FV_PKG is set
R437=${FV_RH437_DIR:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/rh437}   # 4.37 RH export, challenge-rh/ and hide lists
E=${FV_PR348_EXPORT:-$R437/pr348/solution-pr348.export}
[ -d "$(dirname "$E")" ] || { echo "SKIP $(basename "$0"): launcher of the three-kernel record; its inputs ($E) are not part of the repository"; exit 0; }
T=${1:-128}; WANT=a0b2ade4bc26cfa750cd0486bb9cdb1f6e699041e09e088e3ebd93565cba0158; SIZE=61172279192
O=${FV_WORK:-$(dirname "$E")}/threekernel-437e; mkdir -p "$O"
echo "[launch] $(date -u +%FT%TZ) waiting for $E ($SIZE B)"
while :; do s=$(stat -c %s "$E" 2>/dev/null || echo 0); [ "$s" = "$SIZE" ] && break; sleep 20; done
sleep 30; [ "$(stat -c %s "$E")" = "$SIZE" ] || { echo "[launch] size changed after completion?"; exit 2; }
echo "[launch] $(date -u +%FT%TZ) size ok, hashing"; got=$(sha256sum "$E" | cut -d' ' -f1); echo "$got  $E" > "$O/export.sha256"
[ "$got" = "$WANT" ] || { echo "[launch] SHA MISMATCH $got != $WANT"; exit 3; }
echo "[launch] $(date -u +%FT%TZ) sha ok $got"
export CS=${CS:-$PKG/check/sound/check-sound.sh} PINS437=${PINS437:-$PKG/check/sound/pins-437e.env} HIDE=${HIDE:-$R437/deps-only-no-expose.txt}
sha256sum "$CS" "$PINS437" "$HIDE" | tee "$O/inputs.sha256"
exec "$HERE/threekernel437.sh" "$E" $R437/challenge-rh/challenge.export $R437/challenge-rh/comparator.json "$O" "$T" "$PKG"

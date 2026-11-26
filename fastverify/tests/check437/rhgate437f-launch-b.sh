#!/bin/bash
# rhgate437f-launch-b.sh [THREADS] - variant of the encapsulated RH-scale check with the replay budget (pins-437f, deps-only hide list): export = the cache-based community-main
# export (read-only use), challenge = the pinned challenge-rh, the package under test (inputs under $FV_RH437_DIR).
set -u
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=${FV_PKG:-$(cd "$HERE/../.." && pwd)}   # the package under test unless FV_PKG is set
R437=${FV_RH437_DIR:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/rh437}   # 4.37 RH export, challenge-rh/ and hide lists
E=${FV_RH437_EXPORT:-$R437/solution.export}   # the cache-based community-main export (read-only use)
[ -f "$E" ] || { echo "SKIP $(basename "$0"): launcher of the RH-scale 4.37 check; its inputs ($E, $R437) are not part of the repository"; exit 0; }
export PINS437=${PINS437:-$PKG/check/sound/pins-437f.env} HIDE=${HIDE:-$R437/deps-only-no-expose.txt}
O=${FV_WORK:-$R437}/rh437f-b; mkdir -p "$O"
exec "$HERE/rhgate437.sh" "$E" $R437/challenge-rh/challenge.export $R437/challenge-rh/comparator.json "$O/gate" "${1:-56}" "$PKG"

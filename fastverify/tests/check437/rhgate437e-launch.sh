#!/bin/bash
# rhgate437e-launch.sh [THREADS] - the RH-scale soundness check with the ENCAPSULATED replay (pins-437e.env = pleanchecker 4e5a3d1f,
# check-sound.sh v2.2 --hide with a 37,560-name list); inputs under $FV_RH437_DIR.
set -u
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=${FV_PKG:-$(cd "$HERE/../.." && pwd)}   # the package under test unless FV_PKG is set
R437=${FV_RH437_DIR:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/rh437}   # 4.37 RH export, challenge-rh/ and hide lists
[ -f "$R437/solution.export" ] || { echo "SKIP $(basename "$0"): launcher of the RH-scale 4.37 check; its inputs ($R437) are not part of the repository"; exit 0; }
R=$R437; export PINS437=${PINS437:-$PKG/check/sound/pins-437e.env} HIDE=${HIDE:-$R437/hide-437-no-freealg.txt}
exec "$HERE/rhgate437.sh" $R/solution.export $R/challenge-rh/challenge.export $R/challenge-rh/comparator.json $R/gate-e "${1:-128}" "$PKG"

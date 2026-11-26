#!/bin/bash
# 014(e) END-TO-END: proj-liveness (LA: user simple scoped extension whose addEntry diverges when entries of LB1 and LB2 meet;
# Main imports LB1+LB2, never uses the extension, proves the 5 challenge theorems by rfl). OFFICIAL lake build is bounded to
# OFFICIAL_BUILD_TIMEOUT seconds (default 300; it never terminates), FAST = pipeline.sh + pchk with LEAN_TC=FAST_TC (a native build of the fast toolchain's sources).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-e2e-014e}
export FAST_TC=${FAST_TC:-/scratch/fast-tc/7586} OFFICIAL_BUILD_TIMEOUT=${OFFICIAL_BUILD_TIMEOUT:-300}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj-liveness" "$W/proj-liveness"
echo "=== OFFICIAL flow (lake build bounded to ${OFFICIAL_BUILD_TIMEOUT}s)"; bash "$D/officialflow-bounded.sh" "$W/proj-liveness" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow (FAST_TC=$FAST_TC)"; bash "$D/fastflow.sh" "$W/proj-liveness" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "=== SUMMARY proj-liveness official_rc=$orc fast_rc=$frc (0 = ACCEPTED; official 124/1 after the timeout = no result)"

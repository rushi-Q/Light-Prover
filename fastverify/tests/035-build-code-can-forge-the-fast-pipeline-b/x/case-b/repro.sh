#!/bin/bash
# 035(b) repro: build-time code writes $W/log/native.ready (writable in the build sandbox) before native.sh does; the
# scheduler appends its lines ('-DmaxRecDepth=100000') to every later lean call. Needs the artifact default native.txt=on
# (native.sh compiles the whole Mathlib cache C: ~3-5 min with 32 threads). Any test host.
D=$(cd "$(dirname "$0")" && pwd); H=$(ls -d $LIGHT_LEAN/fastverify/tests/063-*/x); W=${1:-${TMPDIR:-/tmp}/$USER-035b}
rm -rf "$W"; mkdir -p "$W"; cp -a "$H/challenge" "$W/challenge"; cp -a "$D/proj-inj" "$W/p"; unset LEAN_TC FAST_TC
P=$W/pipeline; cp -a $LIGHT_LEAN/fastverify/pipeline "$P"; echo on > "$P/native.txt"; echo symlink > "$P/pkgmode.txt"
echo "##### proj-inj"
bash "$H/officialflow.sh" "$W/p" "$W/off" "$W/challenge" > "$W/off.log" 2>&1; orc=$?
FAST_PIPELINE_DIR=$P EVAL_THREADS=${EVAL_THREADS:-32} bash "$H/fastflow.sh" "$W/p" "$W/fast" "$W/challenge/challenge.export" > "$W/fast.log" 2>&1; frc=$?
grep -E '^OFFICIAL|error: src' "$W/off.log" | head -2 | sed 's/^/  /'; grep -E '^FAST' "$W/fast.log" | sed 's/^/  /'
grep -h "NATIVE\|Built\|Failed" "$W/fast/run/log/sched.log" | head -5 | cut -c1-120 | sed 's/^/  fast: /'
echo "=== SUMMARY proj-inj official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
rm -rf "$W"

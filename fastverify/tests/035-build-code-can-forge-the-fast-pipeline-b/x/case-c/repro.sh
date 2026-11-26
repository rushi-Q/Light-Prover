#!/bin/bash
# 035(c) repro: with the artifact default pkgmode=local, pipeline.sh copies the build toolchain's core library into
# proj/.lake/tclib (FIRST on every lean's LEAN_PATH via LEAN_PATH_PRE), inside the build sandbox's writable proj bind. Module A's
# elaboration-time code (only when TOOLWRAP_LOG is set, i.e. inside the fast sandbox; the official harness and the real
# toolchains are never touched) compiles a forged core module Lean.Data.EditDistance into that copy; module C (imports A and the
# core module) then elaborates against the forged core. C is outside Main's export closure.
# OFFICIAL = officialflow.sh, FAST = fastflow.sh with a deployed pipeline copy (pkgmode=local, native off, LEAN_TC unset).
# Any test host, ~2 min (copies the 7.6 GB package cache once).
D=$(cd "$(dirname "$0")" && pwd); H=$(ls -d $LIGHT_LEAN/fastverify/tests/063-*/x); W=${1:-${TMPDIR:-/tmp}/$USER-035c}
rm -rf "$W"; mkdir -p "$W"; cp -a "$H/challenge" "$W/challenge"; cp -a "$D/proj-tclib" "$W/p"; unset LEAN_TC FAST_TC
P=$W/pipeline; cp -a $LIGHT_LEAN/fastverify/pipeline "$P"; echo off > "$P/native.txt"; echo local > "$P/pkgmode.txt"
echo "##### proj-tclib"
bash "$H/officialflow.sh" "$W/p" "$W/off" "$W/challenge" > "$W/off.log" 2>&1; orc=$?
FAST_PIPELINE_DIR=$P EVAL_THREADS=${EVAL_THREADS:-32} bash "$H/fastflow.sh" "$W/p" "$W/fast" "$W/challenge/challenge.export" > "$W/fast.log" 2>&1; frc=$?
grep -E '^OFFICIAL|error: src' "$W/off.log" | head -2 | sed 's/^/  /'; grep -E '^FAST' "$W/fast.log" | sed 's/^/  /'
grep -h "prepared" "$W/fast/pipeline.log" | sed 's/^/  fast: /'; echo "  fast: forge: $(head -c 120 $W/fast/run/proj/.lake/fc.out 2>/dev/null)"
grep -h "Built\|Failed" "$W/fast/run/log/sched.log" | sed 's/^/  fast: /'
echo "=== SUMMARY proj-tclib official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
rm -rf "$W"

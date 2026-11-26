#!/bin/bash
# 030 END-TO-END through the deployed pipeline (fastverify/pipeline/pipeline.sh + pchk), the end-to-end harness (copied here):
# e2e/proj = Helper (defines a command; matches prep.py's ktc_guard, keeps kernel TC) + Main (uses the command: no ktc_guard
# keyword -> built with -Ddebug.skipKernelTC=true). OFFICIAL = lake build 4.33.1 + official lean4export + lake comparator 4.36.
# FAST = pipeline.sh (test hosts: LEAN_TC-unset mode, deployed native exporter cannot run -> export.sh's official fallback;
# both exporters write the same substituted term here) + pchk run.sh. With FIXED=1 the pipeline copy gets
# fix-030-033-export.sh.patch (LEAN_ABORT_ON_PANIC=1 for the exporters).   usage: repro-e2e.sh [WORKDIR]
D=$(cd "$(dirname "$0")" && pwd); W=${1:-$(mktemp -d ${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-030e2e.XXXXXX)}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/e2e/challenge" "$W/challenge"; cp -a "$D/e2e/proj" "$W/proj"; rm -f "$W/challenge/challenge.export"
if [ -n "${FIXED:-}" ]; then
  P=$W/pipeline; cp -a $LIGHT_LEAN/fastverify/pipeline "$P"; echo off > "$P/native.txt"; echo symlink > "$P/pkgmode.txt"
  (cd "$P" && patch -s -p0 export.sh < "$D/fix-030-033-export.sh.patch.p0") && echo "[FIXED pipeline copy: export.sh runs exporters with LEAN_ABORT_ON_PANIC=1]"
  export FAST_PIPELINE_DIR=$P
fi
echo "=== OFFICIAL flow"; bash "$D/e2e/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/e2e/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
grep -h "ktc_guard" "$W/fast/run/log/"*.txt 2>/dev/null | head -0
echo "fast: ktc_guard.txt (modules keeping the kernel check): $(tr '\n' ' ' < "$W/fast/run/log/ktc_guard.txt" 2>/dev/null)"
grep -h "PANIC" "$W/fast/run/log/export."*.time 2>/dev/null | head -2 | sed 's/^/fast: export stderr: /'
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"
[ -n "${KEEP:-}" ] || rm -rf "$W"

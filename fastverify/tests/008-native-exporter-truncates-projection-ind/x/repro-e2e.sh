#!/bin/bash
# 008 END-TO-END through the deployed pipeline (fastverify/pipeline/pipeline.sh + pchk), the end-to-end harness (copied to e2e/):
# e2e/proj = Helper (defines a command; matches prep.py's ktc_guard, keeps kernel TC) + Main (uses the command: no ktc_guard
# keyword -> built with -Ddebug.skipKernelTC=true). OFFICIAL = lake build 4.33.1 + official lean4export + lake comparator 4.36.
# FAST = pipeline.sh with the NATIVE exporter: the deployed /scratch/fastverify/exporter/lean4export where it runs, else the
# same commit f581123 built for the test hosts ($B/lean4export-f581123); FIXED=1 uses the patched build
# $B/lean4export-fix008-010 instead.   usage: repro-e2e.sh [WORKDIR]
D=$(cd "$(dirname "$0")" && pwd); W=${1:-$(mktemp -d ${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-008e2e.XXXXXX)}
B=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/e2e/challenge" "$W/challenge"; cp -a "$D/e2e/proj" "$W/proj"; rm -f "$W/challenge/challenge.export"
NE=/scratch/fastverify/exporter/lean4export
if ! "$NE" --help >/dev/null 2>&1 && ldd "$NE" 2>&1 | grep -q "not found\|GLIBC"; then NE=$B/lean4export-f581123; fi
"$NE" 2>&1 | grep -q "GLIBC_2.38" && NE=$B/lean4export-f581123
[ -n "${FIXED:-}" ] && NE=$B/lean4export-fix008-010
[ -n "${NATIVE_EXPORTER_CANDIDATE:-}" ] && NE=$NATIVE_EXPORTER_CANDIDATE   # test a fixed exporter build
export NATIVE_EXPORTER=$NE; echo "[native exporter used by export.sh: $NE]"
echo "=== OFFICIAL flow"; bash "$D/e2e/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/e2e/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "fast: ktc_guard.txt (modules keeping the kernel check): $(tr '\n' ' ' < "$W/fast/run/log/ktc_guard.txt" 2>/dev/null)"
echo "fast: checked export contains idx 4294967297: $(grep -c "\"idx\":4294967297" "$W/fast/run/solution.export") time(s)  (0 = truncated by the native exporter)"
echo "official: projection in the official export of the FAST oleans would be idx 4294967297 (component repro.sh step 3)"
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"
[ -n "${KEEP:-}" ] || rm -rf "$W"

#!/bin/bash
# 010 END-TO-END through the deployed pipeline (fastverify/pipeline/pipeline.sh + pchk), the end-to-end harness (copied to e2e/):
# e2e/proj/src/Main.lean = the component repro's Main (a definition whose String literal holds invalid UTF-8, made by an
# unsafe metaprogram; the kernel never reads string bytes, so the original build accepts). OFFICIAL = lake build 4.33.1 + official lean4export + lake comparator 4.36.
# FAST = pipeline.sh with the NATIVE exporter: the deployed /scratch/fastverify/exporter/lean4export where it runs, else the
# same commit f581123 built for the test hosts ($B/lean4export-f581123); FIXED=1 uses the patched build
# $B/lean4export-fix008-010 instead.   usage: repro-e2e.sh [WORKDIR]
D=$(cd "$(dirname "$0")" && pwd); W=${1:-$(mktemp -d ${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-010e2e.XXXXXX)}
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
echo "fast: checked export is valid UTF-8: $(iconv -f UTF-8 -t UTF-8 "$W/fast/run/solution.export" >/dev/null 2>&1 && echo yes || echo NO)"; echo "official: official export is valid UTF-8: $(iconv -f UTF-8 -t UTF-8 "$W/official/solution.export" >/dev/null 2>&1 && echo yes || echo NO)"
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"
[ -n "${KEEP:-}" ] || rm -rf "$W"

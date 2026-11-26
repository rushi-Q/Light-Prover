#!/bin/bash
# fastflow.sh PRISTINE WORK CHALLENGE_EXPORT [pchk|dual]  -> prints "FAST: <verdict>" ; exit 0 iff ACCEPTED
# The original FAST flow: fastverify/pipeline/pipeline.sh with LEAN_TC=/scratch/fastverify/tc/stage1 and
# LEAN4EXPORT_BIN=/scratch/fastverify/exporter/lean4export, then pchk (run.sh with the challenge).
# FAST_PIPELINE_DIR (default: a copy of fastverify/pipeline with the documented speed knobs native.txt=off and
# pkgmode.txt=symlink, which only affect speed - set FAST_PIPELINE_DIR=$LIGHT_LEAN/fastverify/pipeline
# to run the artifact exactly as is; it then compiles the whole Mathlib cache natively first).
set -u
P=$(readlink -f "$1"); W=$2; CE=$(readlink -f "$3"); MODE=${4:-pchk}; R=$LIGHT_LEAN
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
PD=${FAST_PIPELINE_DIR:-}
if [ -z "$PD" ]; then PD=$W/pipeline; cp -a $R/fastverify/pipeline "$PD"; echo off > "$PD/native.txt"; echo symlink > "$PD/pkgmode.txt"; fi
# LEAN_TC: the PGO toolchain /scratch/fastverify/tc/stage1 needs GLIBC_2.38/GLIBCXX_3.4.31 and cannot run on hosts with glibc 2.35
# (every module would silently fall back to RETRY_OFFICIAL = pristine text, no LEAN_EXTRA). By default we therefore run the
# pipeline in its documented LEAN_TC-unset mode (official 4.33.1 lean, ALL pipeline transforms applied: hard-coded args,
# LEAN_EXTRA=-Ddebug.skipKernelTC=true -Dlinter.all=false, deny line, EARLY_RELEASE, retries). FAST_TC=dir overrides.
[ -n "${FAST_TC:-}" ] && export LEAN_TC=$FAST_TC
export LEAN4EXPORT_BIN=${NATIVE_EXPORTER:-/scratch/fastverify/exporter/lean4export} EVAL_THREADS=${EVAL_THREADS:-16}
# pipeline.sh bug: with native.txt=off it ends with `cat $W/log/native.log` under set -e and exits 1 although the export
# succeeded; pre-create that (empty) log so the knob works (no other effect).
mkdir -p "$W/run/log"; : > "$W/run/log/native.log"
echo "fast: pipeline.sh ($PD)"
bash "$PD/pipeline.sh" "$P" "$W/run" > "$W/pipeline.log" 2>&1; prc=$?
grep -E 'RETRY|NOTE|SUMMARY|EXIT|BUILD FAILED|export:' "$W/pipeline.log" | cut -c1-300 | sed 's/^/fast: /'
if [ $prc -ne 0 ] || [ ! -s "$W/run/solution.export" ]; then echo "FAST: REJECTED (pipeline failed rc=$prc)"; exit 1; fi
echo "fast: export $(stat -c %s "$W/run/solution.export") bytes sha256 $(sha256sum < "$W/run/solution.export" | cut -c1-16)"
if [ "$MODE" = dual ]; then
  D=/scratch/fastverify/checkers/dualkernel; echo "fast: dual kernel"; bash $D/kcompare/allof.sh "$CE" "$W/run/solution.export" > "$W/check.log" 2>&1; crc=$?
else
  S=/scratch/fastverify/checkers/pchk
  # pleanchecker-k (patched kernel) needs GLIBC_2.38 -> on hosts with an older glibc use a local rebuild if given, else pleanchecker
  if ! $S/.lake/build/bin/pleanchecker-k --help >/dev/null 2>&1 && [ -z "${CCMP_LEANCHECKER:-}" ]; then
    export CCMP_LEANCHECKER=${PCHK_K_REBUILD:-$S/.lake/build/bin/pleanchecker}; echo "fast: CCMP_LEANCHECKER=$CCMP_LEANCHECKER (deployed pleanchecker-k cannot run here)"; fi
  sh $S/run.sh $S "$W/run/solution.export" 16 "$CE" > "$W/check.log" 2>&1; crc=$?
fi
tail -4 "$W/check.log" | sed 's/^/fast: check: /'
if [ $crc -eq 0 ]; then echo "FAST: ACCEPTED ($MODE rc=0)"; exit 0; else echo "FAST: REJECTED ($MODE rc=$crc)"; exit 1; fi

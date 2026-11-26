#!/bin/bash
# Repro (~30 s). Runs the REAL fastverify/pipeline/pipeline.sh exactly as the earlier fast flow did
# (LEAN_TC=/scratch/fastverify/tc/stage1, LEAN4EXPORT_BIN=/scratch/fastverify/exporter/lean4export) on a trivial 1-module
# project (proj/). On these hosts both binaries cannot start (GLIBC_2.38/GLIBCXX_3.4.31 missing). Part 2: the documented
# knob native.txt=off makes pipeline.sh exit 1 after a successful export.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-036}; P=$LIGHT_LEAN/fastverify/pipeline
rm -rf "$W"; mkdir -p "$W"
echo "=== part 1: pipeline.sh as deployed (native.txt=on) with LEAN_TC + LEAN4EXPORT_BIN"
LEAN_TC=/scratch/fastverify/tc/stage1 LEAN4EXPORT_BIN=/scratch/fastverify/exporter/lean4export EVAL_THREADS=16 \
  bash $P/pipeline.sh "$D/proj" "$W/p1" > "$W/p1.log" 2>&1; echo "pipeline rc=$?"
grep -E "RETRY|SUMMARY|^EXIT|export: native rc|FAILED -> official|native: " "$W/p1.log" | cut -c1-220
echo "modules.jsonl attempts for Main: $(grep -c '"module": "Main"' "$W/p1/log/modules.jsonl"), official=$(grep -c '"official": true' "$W/p1/log/modules.jsonl")"
echo "=== part 2: copy of pipeline with the documented knob native.txt=off (LEAN_TC unset)"
mkdir -p "$W/pl"; cp -a $P/. "$W/pl/"; echo off > "$W/pl/native.txt"
EVAL_THREADS=16 bash "$W/pl/pipeline.sh" "$D/proj" "$W/p2" > "$W/p2.log" 2>&1; rc=$?
echo "pipeline rc=$rc; solution.export present: $(test -s "$W/p2/solution.export" && echo yes || echo no); last lines:"; tail -2 "$W/p2.log" | cut -c1-200

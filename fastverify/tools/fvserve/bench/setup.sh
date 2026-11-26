#!/bin/bash
# setup.sh ROOT FV WS [THREADS] — regenerate the inputs of the fvserve benchmarks on a node.
#   ROOT/corpus        the small-proof corpus (bench/throughput/corpus/gen.py): 108 problems + cheating variants
#   ROOT/pset          the problem set: challenge.export = the OFFICIAL export of the BATCH challenge (all 108 statements
#                      := sorry; built by `bin/fastverify ... --preset reference` = official lake build + official lean4export),
#                      comparator.json, challenge.export.sha256
#   ROOT/att-{pos,mix,neg}  attempt dirs (bench/throughput/mkattempts.py)
#   ROOT/stream        a realistic attempt stream (bench/throughput/mkstream.py, 1,000 attempts)
# FV = the package (a node-local copy made by bench/shapes/mklocal.sh), WS = the trusted workspace copy.
set -eu
ROOT=${1:?root}; FV=${2:?package}; WS=${3:?workspace}; T=${4:-16}
TP=$FV/bench/throughput
mkdir -p "$ROOT"
[ -d "$ROOT/corpus" ] || python3 -I "$TP/corpus/gen.py" "$ROOT/corpus" > "$ROOT/gen.log"
if [ ! -f "$ROOT/pset/challenge.export" ]; then
  rm -rf "$ROOT/ref-batch"
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$ROOT/corpus/projects/BATCH" \
    "$ROOT/corpus/challenges/BATCH" "$ROOT/ref-batch" --preset reference --threads "$T" --packages "$WS" > "$ROOT/ref-batch.log" 2>&1 || true
  python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print("official BATCH verdict:", r.get("verdict"), r.get("stage_seconds"))' "$ROOT/ref-batch/result.json"
  mkdir -p "$ROOT/pset"
  cp "$ROOT/ref-batch/challenge.export" "$ROOT/pset/challenge.export"
  cp "$ROOT/corpus/challenges/BATCH/comparator.json" "$ROOT/pset/comparator.json"
  (cd "$ROOT/pset" && sha256sum challenge.export > challenge.export.sha256)
  rm -f "$ROOT/ref-batch/solution.export"; rm -rf "$ROOT/ref-batch/work"
fi
for m in pos mix neg; do [ -d "$ROOT/att-$m" ] || python3 -I "$TP/mkattempts.py" "$ROOT/corpus" "$ROOT/att-$m" $m; done
[ -d "$ROOT/stream" ] || python3 -I "$TP/mkstream.py" "$ROOT/corpus" "$ROOT/stream" --n 1000 > "$ROOT/stream.log" 2>&1 || true
echo "setup done: $ROOT (pset sha256 $(cut -c1-16 "$ROOT/pset/challenge.export.sha256")...)"

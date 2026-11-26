#!/bin/bash
# batch.sh ROOT THREADS "PRESETS" CASE...   -> run.py for every case x preset, sequentially (generate missing cases first)
R=$(dirname "$(readlink -f "$0")")
ROOT=$1; T=$2; PRESETS=$3; shift 3
for c in "$@"; do
  [ -d "$ROOT/$c" ] || python3 -I $R/gen.py $ROOT $c > /dev/null
  for p in $PRESETS; do python3 -I $R/run.py $ROOT $c $p $T; done
done
echo BATCH DONE

#!/bin/bash
# Mathlib-as-project (qr slice): --interface mode for the edits Q, E, D (after run_ml_edits.sh / run_ml_edits2.sh)
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
BASE=$V/mlbase; CHX=$V/ml/chalx; CSHA=$(sha256sum $CHX/challenge.export | cut -d' ' -f1)
for e in Q E D; do O=$V/ml-incr/${e}i; rm -rf $O; echo "=== ${e}i $(date -u +%H:%M:%S)"
  INCR_TC=$V/local/elan/toolchains/leanprover--lean4---v4.33.1 $FVR/tools/incr/incr-reverify.sh $BASE $V/ml-edits/$e $CHX $O --challenge-sha256 $CSHA \
    --threads 96 --packages $V/local/ws --no-skip-kernel-tc --interface --reuse-plan | tail -1 | cut -c1-500
  cp $O/summary.json $V/results/ml/${e}i.json 2>/dev/null
done

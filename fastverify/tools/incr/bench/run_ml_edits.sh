#!/bin/bash
# Mathlib-as-project (qr slice) incremental re-verification scenarios. run_ml_edits.sh SCEN...
set -u
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
BASE=$V/mlbase; SRC=$V/ml/proj/qr; CHX=$V/ml/chalx
[ -d $CHX ] || { mkdir -p $CHX; cp $V/ml/chal/qr/* $CHX/; cp $BASE/challenge.export $CHX/; }
CSHA=$(sha256sum $CHX/challenge.export | cut -d' ' -f1)
mkdir -p $V/ml-edits $V/ml-incr $V/results/ml
ed() { [ -d $V/ml-edits/$1 ] || python3 -I $FVR/tools/incr/mk-edit.py $SRC $V/ml-edits/$1 $2 have $3 || exit 2; }
ed Q Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity quadratic_reciprocity
ed C Mathlib.GroupTheory.Perm.Cycle.Basic sameCycle_one
ed U Mathlib.Order.WithBot unbotD_bot   # created with kind term (rfl proof); 1,502 importers
for s in "$@"; do e=${s%?}; m=${s: -1}
  case $m in f) A=(--reuse-plan) ;; o) A=(--optimistic --reuse-plan) ;; w) A=(--optimistic --reuse-plan --warm $(readlink -f $BASE/solution.export)) ;; esac
  O=$V/ml-incr/$s; rm -rf $O; echo "=== $s $(date -u +%H:%M:%S) ${A[*]}"
  INCR_TC=$V/local/elan/toolchains/leanprover--lean4---v4.33.1 FASTVERIFY=$FVR \
  $FVR/tools/incr/incr-reverify.sh $BASE $V/ml-edits/$e $CHX $O --challenge-sha256 $CSHA \
    --threads 96 --packages $V/local/ws --no-skip-kernel-tc "${A[@]}" | tail -1 | cut -c1-600
  cp $O/summary.json $V/results/ml/$s.json 2>/dev/null
done

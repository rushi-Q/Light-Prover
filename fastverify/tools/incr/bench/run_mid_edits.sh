#!/bin/bash
# rh-mid incremental re-verification scenarios. Usage: run_mid_edits.sh BASE_OUT RESDIR SCENARIO...
# SCENARIO = <edit><mode>: edits M1..M4 (+ kinds via suffix letters), modes: f full, o optimistic, w optimistic+warm
set -u
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
BI=${FV_BENCH_INPUTS:?benchmark inputs root holding rh-mid/ (required)}
BASE=$1; RES=$2; shift 2
SRC=$V/src/rhmid0; CH=$BI/rh-mid/challenge
CSHA=851372abb99f64bc445e99148506af98db19df4d15f3fac888937c6a383505b9
T=${THREADS:-96}
mkdir -p $RES $V/mid-edits $V/mid-incr
edit() {  # edit TAG KIND MODULE DECL
  [ -d $V/mid-edits/$1 ] || python3 -I $FVR/tools/incr/mk-edit.py $SRC $V/mid-edits/$1 $3 $2 $4 > /dev/null || exit 2
}
edit M1 have GroundTheory.AutomorphicForms.RealGroupsIwasawa isUpperTriangular_conjTranspose_iff
edit M2 have Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecay rapid_decrease
edit M3 have Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway isRestrGroup_GAd
edit M4 have ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt chart_le_pull
edit M2s sorry Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecay rapid_decrease
edit M2b break Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecay rapid_decrease
edit M4a append ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt chart_le_pull
for s in "$@"; do
  e=${s%?}; m=${s: -1}
  case $m in f) A=(--reuse-plan) ;; o) A=(--optimistic --reuse-plan) ;; w) A=(--optimistic --reuse-plan --warm $BASE/solution.export) ;; p) A=() ;; esac
  O=$V/mid-incr/$s; rm -rf $O
  echo "=== $s $(date -u +%H:%M:%S) ${A[*]}"
  $FVR/tools/incr/incr-reverify.sh $BASE $V/mid-edits/$e $CH $O \
    --challenge-sha256 $CSHA --threads $T --packages $V/ws "${A[@]}" | tail -1
  cp $O/summary.json $RES/$s.json 2>/dev/null
done

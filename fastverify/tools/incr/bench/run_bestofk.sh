#!/bin/bash
# best-of-K candidate verification in a large project: K candidate proofs of ONE theorem of rh-mid
# (isRestrGroup_GAd in ExistsUniqueIsProdMeasureFinAway, 308 importers), each verified independently with the optimistic
# incremental path (rebuild the edited module only, E1, trusted check-sound), all K CONCURRENTLY on one node with T/K
# threads each. Candidates: 5 valid variants, 2 'sorry', 1 ill-typed.
set -u
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
BI=${FV_BENCH_INPUTS:?benchmark inputs root holding rh-mid/ (required)}
K=8; T=${THREADS:-96}; TPER=$((T / K)); BASE=$V/base1
SRC=$V/src/rhmid0; CH=$BI/rh-mid/challenge
CSHA=851372abb99f64bc445e99148506af98db19df4d15f3fac888937c6a383505b9
M=Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway; D=isRestrGroup_GAd
F=src/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsUniqueIsProdMeasureFinAway.lean
R=$V/bok; rm -rf $R; mkdir -p $R
for i in 1 2 3 4 5; do python3 -I $FVR/tools/incr/mk-edit.py $SRC $R/c$i $M have $D > /dev/null
  f=$R/c$i/$F; cp --remove-destination $f $f.tmp && sed -i "s/have _v05edit : (2 : Nat) + 2 = 4 := rfl/have _v05edit : ($i : Nat) + $((i*7)) = $((i*8)) := rfl/" $f.tmp && mv $f.tmp $f; done
for i in 6 7; do python3 -I $FVR/tools/incr/mk-edit.py $SRC $R/c$i $M sorry $D > /dev/null; done
python3 -I $FVR/tools/incr/mk-edit.py $SRC $R/c8 $M break $D > /dev/null
s0=$(date +%s.%N)
for i in $(seq 1 $K); do
  ( $FVR/tools/incr/incr-reverify.sh $BASE $R/c$i $CH $R/o$i --challenge-sha256 $CSHA \
      --threads $TPER --packages $V/ws --optimistic-only --reuse-plan > $R/o$i.log 2>&1; echo "c$i exit $? at $(echo "$(date +%s.%N) - $s0" | bc) s" ) &
done
wait
echo "ALL $K candidates in $(echo "$(date +%s.%N) - $s0" | bc) s (threads per candidate $TPER)"
for i in $(seq 1 $K); do python3 -c "import json;r=json.load(open('$R/o$i/summary.json'));print('c$i',r['verdict'],r['total_s'],[(a['attempt'],a['outcome'],a['build_s'],a['export_s'],a['check_s']) for a in r['attempts']])"; done

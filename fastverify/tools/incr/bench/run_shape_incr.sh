#!/bin/bash
# incremental re-verification on the synthetic chain core-deep-256-tactic (257 modules in one import chain): the
# full-cone rebuild is bounded by the cone's CRITICAL PATH (a chain = sequential), the optimistic path is not.
set -u
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
S=$V/shapes; P=$S/core-deep-256-tactic/project; CH=$S/challenge; B=$V/shbase
FV=$V/local/fv; TC=$V/local/elan/toolchains/leanprover--lean4---v4.33.1
U="toolchain-T1=lean4-7586a50cec-nopgo,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,sound-fast-path,native-pkg"
if [ ! -f $B/result.json ]; then rm -rf $B
  /usr/bin/time -f "WALL %e" $FV/bin/fastverify $P $CH $B --preset sound --unsafe "$U" --threads 96 --keep-work --overlap-targets none > $V/shbase.log 2>&1
  echo "BASE $?"; python3 -c "import json;r=json.load(open('$B/result.json'));print(r['verdict'],r['stage_seconds'])"
fi
CHX=$V/shchx; [ -d $CHX ] || { mkdir -p $CHX; cp $CH/comparator.json $CHX/ 2>/dev/null || cp $S/challenge/*.json $CHX/; cp $B/challenge.export $CHX/; }
CSHA=$(sha256sum $CHX/challenge.export | cut -d' ' -f1)
mkdir -p $V/results/shape
for i in 0 128 255; do
  E=$V/shedit$i; rm -rf $E; cp -a $P $E
  f=$E/Shp/M$i.lean; python3 - $f <<'PY'
import sys; p=sys.argv[1]; s=open(p).read()
s=s.replace(": x + 1 ≤ y + 1 := by omega", ": x + 1 ≤ y + 1 := by\n  have _v05edit : (2 : Nat) + 2 = 4 := by decide\n  omega", 1) if ": x + 1 ≤ y + 1 := by omega" in s else s.replace(":= by omega", ":= by\n  have _v05edit : (2 : Nat) + 2 = 4 := by decide\n  omega", 1)
open(p,"w").write(s)
PY
  for m in o f; do A=(--reuse-plan); [ $m = o ] && A+=(--optimistic)
    O=$V/shincr-$i$m; rm -rf $O; echo "=== M$i $m $(date -u +%H:%M:%S)"
    INCR_TC=$TC $FVR/tools/incr/incr-reverify.sh $B $E $CHX $O --challenge-sha256 $CSHA --threads 96 --packages $V/local/ws "${A[@]}" | tail -1 | cut -c1-400
    cp $O/summary.json $V/results/shape/M$i$m.json 2>/dev/null
  done
done

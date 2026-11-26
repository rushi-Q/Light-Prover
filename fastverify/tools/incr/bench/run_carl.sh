#!/bin/bash
# Carleson (real project, 123 .lean files) sound base without merge, --keep-work, then incremental edits
set -u
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
P=$V/bp/projects/carleson; CH=$V/bp/projects/carleson-challenge; WS=$V/bp/ws/carleson
B=$V/carlbase
if [ ! -f $B/result.json ]; then rm -rf $B
U="toolchain-T1=lean4-7586a50cec-nopgo,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,sound-fast-path,native-pkg"
/usr/bin/time -f "WALL %e" $V/local/fv/bin/fastverify $P $CH $B --preset sound --unsafe "$U" --threads 96 --packages $WS --keep-work --overlap-targets none
echo "BASE EXIT $?"; python3 -c "import json;r=json.load(open('$B/result.json'));print(r['verdict'],r['stage_seconds'],[(x.get('option'),x.get('exit'),x.get('seconds')) for x in r['build']['attempts']],r['export'].get('size'))"
fi
CHX=$V/carlchx; [ -d $CHX ] || { mkdir -p $CHX; cp $CH/comparator.json $CH/lean-toolchain $CHX/; cp $B/challenge.export $CHX/; }
CSHA=$(sha256sum $CHX/challenge.export | cut -d' ' -f1)
mkdir -p $V/carl-edits $V/results/carleson
for e in "$@"; do
  IFS=: read -r tag mod decl kind modes <<< "$e"
  [ -d $V/carl-edits/$tag ] || MKEDIT_PROOF="by decide" python3 -I $FVR/tools/incr/mk-edit.py $P $V/carl-edits/$tag $mod ${kind:-have} $decl || continue
  for m in $(echo $modes | tr ',' ' '); do
    case $m in f) A=(--reuse-plan) ;; o) A=(--optimistic --reuse-plan) ;; w) A=(--optimistic --reuse-plan --warm $(readlink -f $B/solution.export)) ;; esac
    O=$V/carl-incr/$tag$m; rm -rf $O; mkdir -p $V/carl-incr; echo "=== $tag$m $(date -u +%H:%M:%S) ${A[*]}"
    INCR_TC=$V/local/elan/toolchains/leanprover--lean4---v4.33.1 $FVR/tools/incr/incr-reverify.sh $B $V/carl-edits/$tag $CHX $O \
      --challenge-sha256 $CSHA --threads 96 --packages $WS "${A[@]}" | tail -1 | cut -c1-700
    cp $O/summary.json $V/results/carleson/$tag$m.json 2>/dev/null
  done
done

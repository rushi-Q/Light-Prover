#!/bin/bash
# G1 ablation ladder on rh-mid (node-local install $FV_SCRATCH/local, 96 threads): where does the build speed-up come from?
#   L1 fast-exact (B2 = official lean, Lake-planned scheduler + early release; E1; C1)
#   L2 sound, B3 with only toolchain-T1 (nopgo on hosts with glibc < 2.38) + sound-fast-path
#   L3 L2 + skip-kernel-tc + linter-off
#   L4 L3 + premise-off + fast-exact + retries + j1-saturated + cost-hints + native-pkg + check-tail  (= base1 config without zygote items; zygote inactive on hosts with glibc < 2.38 anyway)
set -u
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
BI=${FV_BENCH_INPUTS:?benchmark inputs root holding rh-mid/ (required)}
FV=$V/local/fv/bin/fastverify; SRC=$V/src/rhmid0; CH=$BI/rh-mid/challenge; WS=$V/local/ws
CSHA=851372abb99f64bc445e99148506af98db19df4d15f3fac888937c6a383505b9
T1="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo"
run() { tag=$1; shift; rm -rf $V/lad-$tag; echo "=== $tag $(date -u +%H:%M:%S) $*"
  /usr/bin/time -f "WALL %e" $FV $SRC $CH $V/lad-$tag --threads 96 --packages $WS "$@" > $V/lad-$tag.log 2>&1; echo "exit $?"
  tail -1 $V/lad-$tag.log
  python3 -c "import json;r=json.load(open('$V/lad-$tag/result.json'));b=r.get('build',{});print('$tag',r['verdict'],r.get('trust'),r['stage_seconds'],b.get('option'),[(x.get('option'),x.get('exit'),x.get('seconds')) for x in b.get('attempts',[])],(r.get('export') or {}).get('sha256'))"
  python3 -I $FVR/tools/sched_analyze.py $(ls -d $V/lad-$tag/log/build-fast*/sched.out | tail -1) 2>/dev/null | head -1
  E=$(readlink -f $V/lad-$tag/solution.export); case "$E" in /dev/shm/*) rm -rf "$(dirname "$E")";; esac
  rm -rf $V/lad-$tag/work
}
run L1 --preset fast-exact
run L2 --preset sound --challenge-sha256 $CSHA --unsafe "$T1,sound-fast-path" --overlap-targets none
run L3 --preset sound --challenge-sha256 $CSHA --unsafe "$T1,sound-fast-path,skip-kernel-tc,linter-off" --overlap-targets none
run L4 --preset sound --challenge-sha256 $CSHA --unsafe "$T1,sound-fast-path,skip-kernel-tc,linter-off,premise-off,fast-exact,retries,j1-saturated,cost-hints,native-pkg,check-tail" --overlap-targets none

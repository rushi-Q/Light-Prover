#!/bin/bash
# PGO training run of pleanchecker-pgoinstr (official v4.36.0 kernel libs, instrumented; few threads because the
# non-atomic profile counters thrash when many threads share them): rh-miniF (all jobs), the closure of three heavy RH
# declarations (mid3.export: fc_ι_c, ev_comb, comb_mem), arena good tests; merge -> /scratch/S03/kopt/kernel.profdata
set -u
K=/scratch/S03/kopt; R=$K/pgo-raw; rm -rf $R; mkdir -p $R
export LLVM_PROFILE_FILE=$R/t-%p-%m.profraw
B=$K/pleanchecker-pgoinstr
/usr/bin/time -f "rh-miniF %e s" $B -j2 --from-export /scratch/bench-inputs/rh-miniF/ref/solution.export | tail -1
/usr/bin/time -f "mid3 %e s" $B -j3 --from-export $K/mid3.export | tail -1
for f in $(find /scratch/bench-inputs/arena/suite/good -name '*.ndjson' | sort); do
  case $f in *perf/magma-list-deep-n36*|*perf/magma-list-pair-n21*) continue;; esac
  timeout 120 $B -j2 --from-export $f > /dev/null 2>&1 || true
done
/scratch/c06/envs/cenv/bin/llvm-profdata merge -o $K/kernel.profdata $R/*.profraw
ls -la $K/kernel.profdata

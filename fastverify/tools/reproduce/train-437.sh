#!/bin/bash
# train-437.sh BUNDLE OUTROOT  - PGO training of pleanchecker-437-pgoinstr (the S03 train.sh recipe for 4.36, same corpora):
# rh-miniF (all jobs, -j2), BUNDLE/mid3.export (closure of three heavy RH declarations, -j3), arena good tests (-j2);
# merge -> BUNDLE/kernel437.profdata. Few threads because the non-atomic profile counters thrash.
# FV_BENCH_INPUTS (required) = benchmark inputs root: rh-miniF/ref/solution.export, arena/suite/good/**.ndjson.
set -u
BUNDLE=${1:?usage: train-437.sh BUNDLE OUTROOT}; OUTROOT=${2:?usage: train-437.sh BUNDLE OUTROOT}
BI=${FV_BENCH_INPUTS:?benchmark inputs root holding rh-miniF/ and arena/suite/ (required)}
R=$OUTROOT/pgo-raw; rm -rf $R; mkdir -p $R
export LLVM_PROFILE_FILE=$R/t-%p-%m.profraw LEAN_ABORT_ON_PANIC=1 LEAN_STACK_SIZE_KB=917376
B=$OUTROOT/out/pleanchecker-437-pgoinstr
/usr/bin/time -f "rh-miniF %e s" $B -j2 --from-export "$BI/rh-miniF/ref/solution.export" 2>&1 | grep -v "^\[pchk" | tail -2
/usr/bin/time -f "mid3 %e s" $B -j3 --from-export $BUNDLE/mid3.export 2>&1 | grep -v "^\[pchk" | tail -2
n=0; for f in $(find "$BI/arena/suite/good" -name '*.ndjson' | sort); do
  case $f in *perf/magma-list-deep-n36*|*perf/magma-list-pair-n21*) continue;; esac
  timeout 120 $B -j2 --from-export $f > /dev/null 2>&1 || true; n=$((n+1))
done; echo "arena good: $n runs"
$BUNDLE/cenv/bin/llvm-profdata merge -o $BUNDLE/kernel437.profdata $R/*.profraw && ls -la $BUNDLE/kernel437.profdata && sha256sum $BUNDLE/kernel437.profdata
$BUNDLE/cenv/bin/llvm-profdata show --summary-only $BUNDLE/kernel437.profdata 2>/dev/null | head -8

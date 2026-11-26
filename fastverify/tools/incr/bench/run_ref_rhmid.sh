#!/bin/bash
# official flow (--preset reference = B0 lake build + E0 lean4export + C0 lake comparator) on rh-mid, local WS
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
BI=${FV_BENCH_INPUTS:?benchmark inputs root holding rh-mid/ (required)}
OUT=$1; T=${2:-96}
/usr/bin/time -v ${FVBIN:-$FVR/bin/fastverify} ${SRC:-$V/src/rhmid0} $BI/rh-mid/challenge $OUT \
  --preset reference --threads $T --packages ${WS:-$V/ws}
echo "EXIT $?"

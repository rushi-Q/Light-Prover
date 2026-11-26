#!/bin/bash
# cold --preset sound run of rh-mid WITHOUT merge, --keep-work (= base tree of the incremental experiment)
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
BI=${FV_BENCH_INPUTS:?benchmark inputs root holding rh-mid/ (required)}
OUT=$1; T=${2:-96}
FV=$FVR/bin/fastverify
U="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,check-tail"
/usr/bin/time -v $FV ${SRC:-$V/src/rhmid0} $BI/rh-mid/challenge $OUT \
  --preset sound --unsafe "$U" --threads $T --challenge-sha256 851372abb99f64bc445e99148506af98db19df4d15f3fac888937c6a383505b9 \
  --packages ${WS:-$V/ws} --keep-work
echo "EXIT $?"

#!/bin/bash
# bt.sh : backtrace of the native crash on 'module / import Mathlib' (official lean 4.33.1 + pipeline libpkgs.so + segv.so shim)
D=$(cd "$(dirname "$0")" && pwd); W=${W:-${TMPDIR:-/tmp}/$USER-057-natlib}; R=$LIGHT_LEAN; P=$R/verify/challenge/.lake/packages
[ -f $D/segv.so ] || gcc -shared -fPIC -O1 -o $D/segv.so $D/segv.c -ldl   # needs gcc
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
mkdir -p $W; [ -s $W/native.ready ] || bash $R/fastverify/pipeline/native.sh $P $W/native 48 $W/native.ready > $W/native.log 2>&1
LP=$(for d in $P/*/.lake/build/lib/lean; do printf '%s:' $d; done)$T33/lib/lean
cd $W && printf 'module\nimport Mathlib\n' > T.lean
LD_PRELOAD=$D/segv.so LEAN_PATH=$LP $T33/bin/lean $(cat $W/native.ready) -R . T.lean 2>&1 | head -40; echo "rc=${PIPESTATUS[0]}"

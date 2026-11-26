#!/bin/bash
D=$(cd "$(dirname "$0")" && pwd); W=${W:-${TMPDIR:-/tmp}/$USER-015-linarith}; mkdir -p $W; cp $D/L*.lean $W/; cd $W
bash $LIGHT_LEAN/fastverify/pipeline/native.sh $LIGHT_LEAN/verify/challenge/.lake/packages ${W:-${TMPDIR:-/tmp}/$USER-015-linarith}/native 24 ${W:-${TMPDIR:-/tmp}/$USER-015-linarith}/native.ready > native.log 2>&1
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; P=$LIGHT_LEAN/verify/challenge/.lake/packages
LP=$(for d in $P/*/.lake/build/lib/lean; do printf '%s:' $d; done)$T33/lib/lean
for f in L*.lean; do
  (LEAN_PATH=$LP $T33/bin/lean $f > ${f%.lean}.interp 2>&1; echo "rc=$?" >> ${f%.lean}.interp) &
  (LEAN_PATH=$LP $T33/bin/lean $(cat native.ready) $f > ${f%.lean}.native 2>&1; echo "rc=$?" >> ${f%.lean}.native) &
done; wait
for N in 150 170 190 200 210 220 230 240 250 270; do echo "N=$N interpreted:$(tail -1 L$N.interp) native:$(tail -1 L$N.native)"; done

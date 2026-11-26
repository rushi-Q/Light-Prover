#!/bin/sh
# A VALID Lean project (Main.lean: a helper theorem whose name is Name.anonymous, created with
# run_cmd addDecl and used in the proof of riemannHypothesis). Build + export with the OFFICIAL tools (Lean 4.33.1,
# official lean4export v4.33.0), then judge the SAME export with the official lake comparator 4.36 and the fast checks.
# Official comparator (Lean kernel + nanoda) ACCEPTS; fast A ACCEPTS; fast check B: susz (gruszka's export converter)
# rejects "declaration N declares the anonymous name" -> gruszka leg exit 1 -> check B dual AND single REJECT.
set -u
H=$(dirname "$(readlink -f "$0")"); W=$(mktemp -d /tmp/x08f.XXXXXX)
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
cp $H/Main.lean $W/ && cd $W && PATH=$T33/bin:$PATH lean -o Main.olean Main.lean && \
  LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:$PATH $EXP Main -- $(cat $H/export-targets.txt) > $H/solution.export || { echo "build/export failed"; exit 2; }
echo "official lean 4.33.1 build + official lean4export: ok ($(wc -c < $H/solution.export) bytes); anonymous-name decl: $(grep -m1 '"name":0,' $H/solution.export)"
# the native exporter (f581123, a portable build of the deployed version) gives the same bytes on this .olean
NX=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/lean4export-f581123
[ -x $NX ] && { LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:$PATH $NX Main -- $(cat $H/export-targets.txt) > $W/native.export 2>/dev/null; cmp -s $W/native.export $H/solution.export && echo "native exporter f581123: byte-identical export" || echo "native exporter f581123: DIFFERENT export"; }
FV=1 sh $H/flows.sh $H/challenge.export $H/solution.export
rm -rf $W

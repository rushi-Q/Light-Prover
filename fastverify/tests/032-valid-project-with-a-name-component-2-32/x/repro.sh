#!/bin/sh
# A VALID Lean project (Main.lean: a helper theorem named `helper.4294967296` = Name.num `helper 2^32, created with
# run_cmd addDecl and used in the proof of riemannHypothesis). Build + export with the OFFICIAL tools (Lean 4.33.1,
# official lean4export v4.33.0), then judge the SAME export with the official lake comparator 4.36 and the fast checks.
# Official nanoda parses name numbers as u32 -> "invalid value: integer `4294967296`, expected u32" -> official REJECT;
# fast A (pchk's nanoda) rejects too; fast check B (kcompare + gruszka [AND nl-fast]) ACCEPTS.
set -u
H=$(dirname "$(readlink -f "$0")"); W=$(mktemp -d /tmp/x08f.XXXXXX)
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
cp $H/Main.lean $W/ && cd $W && PATH=$T33/bin:$PATH lean -o Main.olean Main.lean && \
  LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:$PATH $EXP Main -- $(cat $H/export-targets.txt) > $H/solution.export || { echo "build/export failed"; exit 2; }
echo "official lean 4.33.1 build + official lean4export: ok ($(wc -c < $H/solution.export) bytes); name line: $(grep -m1 '"i":4294967296' $H/solution.export)"
FV=1 sh $H/flows.sh $H/challenge.export $H/solution.export
rm -rf $W

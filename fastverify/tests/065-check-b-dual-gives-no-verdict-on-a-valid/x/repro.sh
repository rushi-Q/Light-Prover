#!/bin/sh
# A VALID Lean project (Main.lean): `bigLit : Nat := 10^E` (an E+1-digit Nat literal, added with run_cmd addDecl) is
# referenced in the proof of riemannHypothesis, so the literal is in the exported closure. Official Lean 4.33.1 build +
# official lean4export v4.33.0, then the SAME export judged by the official lake comparator 4.36 (Lean kernel + nanoda),
# fast A (pchk) and fast B dual/single (flows.sh). nl-fast declines Nat literals with more than 65,536 decimal digits
# ('unsupported: natural literal too long', vendor/nano-lean/src/import/importer.rs:177/618) -> check B DUAL exit 2 (no
# verdict) where the official flow ACCEPTS. Control: E = 65535 (65,536 digits) -> every checker accepts.
set -u
H=$(dirname "$(readlink -f "$0")")
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
for E in 65535 65536; do
  W=$(mktemp -d /tmp/x08f.XXXXXX)
  sed "s/^def litE : Nat := 65536/def litE : Nat := $E/" $H/Main.lean > $W/Main.lean
  ( cd $W && PATH=$T33/bin:$PATH lean -o Main.olean Main.lean >/dev/null 2>&1 && \
    LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:$PATH $EXP Main -- $(cat $H/export-targets.txt) > $H/solution-$E.export ) || { echo "build/export failed (E=$E)"; exit 2; }
  echo "=== 10^$E ($((E+1)) digits): official lean 4.33.1 build + official lean4export ok ($(wc -c < $H/solution-$E.export) bytes)"
  FV=1 sh $H/flows.sh $H/challenge.export $H/solution-$E.export 2>&1 | grep -E 'OFFICIAL=|unsupported|too long|Your solution|allof|with-kernel'
  rm -rf $W
done
# ordinary-source variant (no metaprogramming): ordinary/Main.lean states 2^230000 = <its 69,237-digit value> := rfl
# (set_option exponentiation.threshold), used in riemannHypothesis's proof.
W=$(mktemp -d /tmp/x08f.XXXXXX); cp $H/ordinary/Main.lean $W/
( cd $W && PATH=$T33/bin:$PATH lean -o Main.olean Main.lean >/dev/null 2>&1 && \
  LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:$PATH $EXP Main -- $(cat $H/export-targets.txt) > $H/ordinary/solution.export ) || { echo "build/export failed (ordinary)"; exit 2; }
echo "=== ordinary source (2^230000 = <69,237 digits> := rfl): official build + export ok ($(wc -c < $H/ordinary/solution.export) bytes)"
FV=1 sh $H/flows.sh $H/challenge.export $H/ordinary/solution.export 2>&1 | grep -E 'OFFICIAL=|unsupported|too long|Your solution|allof|with-kernel'
rm -rf $W

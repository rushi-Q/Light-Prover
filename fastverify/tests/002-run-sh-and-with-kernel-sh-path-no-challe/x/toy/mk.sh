#!/bin/bash
# mk.sh DIR : compile DIR/Challenge.lean and DIR/Main.lean with official Lean 4.33.1, export with official lean4export v4.33.0
set -eu
D=$(realpath "$1")
T33=$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
TG="Quot Quot.mk Quot.lift Quot.ind ${THMS:-riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive} ${AXS:-propext Quot.sound Classical.choice} Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam ${DEFS:-}"
export PATH=$T33/bin:$PATH
mkdir -p $D/build
for m in Challenge Main; do
  [ -f $D/$m.lean ] || continue
  (cd $D && LEAN_PATH=$T33/lib/lean:$D/build $T33/bin/lean -o build/$m.olean $m.lean)
  (cd $D && LEAN_PATH=$T33/lib/lean:$D/build $EXP $m -- $TG > $( [ $m = Main ] && echo solution.export || echo challenge.export ))
done
ls -la $D/*.export

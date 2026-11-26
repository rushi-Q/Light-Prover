#!/bin/bash
# mkexp.sh MOD THEOREM... : compile MOD.lean with official Lean 4.33.1 and export (official lean4export v4.33.0)
# the same targets the official `lake comparator` exports: builtin Quot*, theorems, permitted axioms, 26 primitives
set -eu
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
export PATH=$T33/bin:$PATH
m=$1; shift
lean -o $m.olean $m.lean
LEAN_PATH=$PWD:$T33/lib/lean $EXP $m -- Quot Quot.mk Quot.lift Quot.ind "$@" propext Quot.sound Classical.choice \
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft \
  Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam > $m.export

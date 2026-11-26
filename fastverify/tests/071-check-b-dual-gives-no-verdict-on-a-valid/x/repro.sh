#!/bin/sh
# 071: a VALID Lean project whose proof uses a definition with N nested binders whose body refers to the OUTERMOST one
# (innermost bound-variable index N-1). Official Lean 4.33.1 build + official lean4export v4.33.0, then the SAME export judged
# by the official lake comparator 4.36 (Lean kernel + nanoda), fast A (pchk) and fast B dual/single (flows.sh).
# nl-fast (check B's second kernel) keeps the loose-bvar count in 15 bits (term/expr.rs:224-226 Meta = u16, NLB_MASK = 2^15-1)
# and its importer declines any bvar index >= BVAR_LIMIT = 32,766 (import/importer.rs:16,532 / import/par.rs:47,378):
# 'unsupported: bound variable index too large' (exit 2) -> allof.sh exit 2 -> check B dual exit 2 (no verdict).
#  case A (Main.lean, run_cmd addDecl): deepF := fun x0 .. x(N-1) => x0 ; N = 32,766 control, N = 32,768 (nl-fast declines);
#   N = 65,535: gruszka declines too ('a term has 65535 or more loose bound variables', src/env.rs:56,398,1095; tc.rs:4827)
#   -> check B SINGLE exit 2 as well.
#  case B (gen2.py, ordinary source, no meta code): noncomputable def deepF (x0 x1 ... x(N-1) : Nat) : Nat := x0 - OPT-IN
#   (NS_B=32768): Lean's elaboration of N binders is quadratic (2,048: 11 s, 4,096: 41 s, 8,192: 163 s -> 32,768 ~45 min).
# Any x86-64 host, ~4 min. Usage: sh repro.sh   (NS_A / NS_B override the N lists)
set -u
H=$(dirname "$(readlink -f "$0")")
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
# exports go under the finding dir: flows.sh runs the fast checkers in krun, whose /tmp is private
O=$H/out.$$; mkdir -p $O
one() { # case N
  W=$(mktemp -d /tmp/x08b071.XXXXXX)
  if [ "$1" = A ]; then sed "s/^def bvN : Nat := 32768/def bvN : Nat := $2/" $H/Main.lean > $W/Main.lean
  else python3 -I $H/gen2.py $2 > $W/Main.lean; fi
  ( cd $W && PATH=$T33/bin:$PATH lean -o Main.olean Main.lean > $W/build.log 2>&1 && \
    LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:$PATH $EXP Main -- $(cat $H/export-targets.txt) > $O/sol-$1-$2.export ) || { echo "build/export failed (case $1 N=$2)"; head -c 1500 $W/build.log; rm -rf $W; return; }
  echo "=== case $1, N=$2 binders (innermost bvar index $(($2-1))): official lean 4.33.1 build + official lean4export ok ($(wc -c < $O/sol-$1-$2.export) bytes)"
  FV=1 sh $H/flows.sh $H/challenge.export $O/sol-$1-$2.export 2>&1 | grep -E 'OFFICIAL=|panicked|too large|unsupported|declined|Your solution|allof|with-kernel|overflow' | cut -c1-300
  rm -rf $W
}
for N in ${NS_A:-32766 32768 65535}; do one A $N; done
for N in ${NS_B:-}; do one B $N; done
rm -rf $O

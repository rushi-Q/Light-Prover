#!/bin/sh
# A VALID Lean project (Main.lean): a helper theorem with N = 65,536 universe parameters (created with run_cmd addDecl; its
# type Nonempty PUnit.{u_last+1} uses the last one), instantiated at Level.zero (65,536 universe arguments) in the proof of
# riemannHypothesis. Official Lean 4.33.1 build + official lean4export v4.33.0, then the SAME export judged by the official
# lake comparator 4.36 (Lean kernel + nanoda), fast A (pchk) and fast B dual/single (flows.sh).
# nl-fast (check B's second kernel) packs a constant's universe list length into 16 bits and asserts <= 65535:
# panic 'too many universe levels' (exit 101) -> allof.sh exit 2 -> check B dual exit 2 (no verdict) on a project the official
# flow ACCEPTS. Control: N = 65,535 -> every checker accepts.
set -u
H=$(dirname "$(readlink -f "$0")")
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
for N in 65535 65536; do
  W=$(mktemp -d /tmp/x08f.XXXXXX)
  sed "s/^def lpsN : Nat := 65536/def lpsN : Nat := $N/" $H/Main.lean > $W/Main.lean
  ( cd $W && PATH=$T33/bin:$PATH lean -o Main.olean Main.lean >/dev/null 2>&1 && \
    LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:$PATH $EXP Main -- $(cat $H/export-targets.txt) > $H/solution-$N.export ) || { echo "build/export failed (N=$N)"; exit 2; }
  echo "=== N=$N universe parameters: official lean 4.33.1 build + official lean4export ok ($(wc -c < $H/solution-$N.export) bytes)"
  FV=1 sh $H/flows.sh $H/challenge.export $H/solution-$N.export 2>&1 | grep -E 'OFFICIAL=|panicked|too many|Your solution|allof|with-kernel'
  rm -rf $W
done

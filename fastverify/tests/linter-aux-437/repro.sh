#!/bin/bash
# auxnum.sh: which untrusted build item changes the auxiliary-lemma numbering seen by expdiff
# (cache-built vs from-sources exports)? Recompile one affected module of the community main with the official 4.37 lean
# on a complete built tree (copy of a cache-restored tree), variants: none / -Ddebug.skipKernelTC=true / -Dlinter.all=false,
# in bwrap; compare the .olean.private parts with the cache's (official) one.
P=${FV_RHC_TREE:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/rh437/proj}; T=$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1; WS=${FV_RHC_WS:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/ws/ml-v4.37.0-rc1}/.lake/packages
O=${FV_WORK:-${TMPDIR:-/tmp}}/auxnum; rm -rf $O; mkdir -p $O
M=${1:-Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem}
LP=$(for p in $(ls $WS); do printf "%s:" $P/.lake/packages/$p/.lake/build/lib/lean; done)$P/.lake/build/lib/lean:$T/lib/lean
B=(); for p in $(ls $WS); do B+=(--ro-bind "$WS/$p" "$P/.lake/packages/$p"); done
OPTS=(-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true -DmaxHeartbeats=4000000)
run() { # tag extra...
  local tag=$1; shift; mkdir -p $O/$tag
  /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /tmp --ro-bind "$T" "$T" "${B[@]}" --bind $O $O --dev /dev --proc /proc \
    --clearenv --setenv PATH "$T/bin:/usr/bin:/bin" --setenv LEAN_PATH "$LP" --unshare-all --die-with-parent --chdir "$P" -- \
    "$T/bin/lean" --tstack=400000 "${OPTS[@]}" "$@" src/$M.lean -o $O/$tag/m.olean > $O/$tag/log 2>&1
  echo "$tag rc=$?"
}
run plain; run skipktc -Ddebug.skipKernelTC=true; run linteroff -Dlinter.all=false; run both -Ddebug.skipKernelTC=true -Dlinter.all=false
for t in plain skipktc linteroff both; do
  for part in olean olean.server olean.private; do
    cmp -s $O/$t/m.$part $P/.lake/build/lib/lean/$M.$part && r=same || r=DIFF; printf "%s %s vs cache: %s\n" $t $part $r
  done
done
for t in plain skipktc linteroff both; do echo "$t: $(strings $O/$t/m.olean.private | grep -E -o '_simp_1_[0-9]+|_proof_[0-9]+' | sort -u | tr '\n' ' ')"; done

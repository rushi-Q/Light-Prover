#!/bin/bash
# repro for: deployed gruszka (dualkernel ae81d8d) misses 018b0d6 and 4ad120b.
# Inputs (in this dir): Challenge.lean/Main.lean (theorem main_thm : True), exported by ./mkexp.sh (official Lean 4.33.1 +
# official lean4export v4.33.0 with the comparator's target list); sol_*.export = Main.export + the 4.36-bad
# inductive tests appended by ./merge.py (K04-nested-nonuniform-param-all2-bad.ndjson, nested-prefix-ctor-bad.ndjson;
# regenerate: python3 merge.py Main.export K04-...-all2-bad.ndjson sol_nonuniform.export, same for the other).
D=$(cd "$(dirname "$0")" && pwd); T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
echo "== git: the deployed checker commit does not contain the fixes"
for c in 018b0d6 4ad120b; do git -C /scratch/fastverify/checkers/dualkernel merge-base --is-ancestor $c HEAD 2>/dev/null && echo "$c in HEAD" || echo "$c NOT in /scratch/fastverify/checkers/dualkernel HEAD ($(git -C /scratch/fastverify/checkers/dualkernel log --oneline -1))"; done
for f in sol_nonuniform.export sol_nestedprefix.export; do
  echo "== official leanchecker 4.36 (LEAN_ABORT_ON_PANIC=1) on $f"; LEAN_ABORT_ON_PANIC=1 $T36/bin/leanchecker --from-export $D/$f 2>&1 | tail -2
  bash $D/run3.sh $D/$f
done
# (b) nano-lean: the deployed vendored nano-lean (k/k08-nano-lean 4ac98c7) lacks the commits 89323a9/10b28d2 (4.36 conformance:
# first inductive type's parameters read syntactically). The suitex test K05-ind-type-head-beta-redex-params (Eq renamed
# K05Eq so it can be appended to Main.export) is accepted by nl-fast, rejected by official 4.36 and by gruszka.
S=/scratch/fastverify/checkers/dualkernel
echo "== official leanchecker 4.36 on sol_headredex.export"; LEAN_ABORT_ON_PANIC=1 $T36/bin/leanchecker --from-export $D/sol_headredex.export 2>&1 | tail -2
bash $D/run3.sh $D/sol_headredex.export
${FV_KRUN:-krun} "KC_THEOREMS=main_thm /bin/sh $S/kcompare/with-kernel.sh $S/target/release/kcompare $D/Challenge.export $D/sol_headredex.export 4 -- $S/target/release/nl-fast -q -j 16 $D/sol_headredex.export > /tmp/o 2>&1; echo \"FAST nano-lean+kcompare (team K's K0650 config) exit=\$? : \$(grep -v '^ok' /tmp/o | tr '\n' ' ')\""

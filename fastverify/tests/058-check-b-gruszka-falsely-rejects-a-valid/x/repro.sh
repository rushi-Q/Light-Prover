#!/bin/bash
# repro for 058: valid project `inductive T | c0 : List (Nat → T) → T` (reflexive field inside a nested occurrence), used
# in main_thm's proof. Official Lean 4.33.1 build + official lean4export v4.33.0 (comparator target list), then
#   OFFICIAL: unmodified Lean 4.36 `lake comparator` (Lean kernel replay + nanoda), cfg.json
#   FAST B single (gruszka + kcompare) and FAST B dual (gruszka AND nano-lean + kcompare): exact harness lines (run3.sh)
# + variants (official leanchecker | gruszka ae81d8d | gruszka 4ad120b | nl-fast): R2 Option (Bool → T), R3 Two Nat (Fin 3 → T),
#   R4 Prod Nat (Nat → T), R5 Box (Nat → T) -> falsely rejected; controls C1 (Nat → T) (reflexive, not nested) and
#   C2 List (List T) (nested, not reflexive) -> accepted by all.
set -u
D=$(cd "$(dirname "$0")" && pwd); cd "$D"
T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0; X=${FV_REPRO_DIR:-$LIGHT_LEAN/repro}
echo "== build + export with official Lean 4.33.1 / lean4export v4.33.0"
bash mkexp.sh Challenge main_thm >/dev/null 2>&1; bash mkexp.sh Main main_thm 2>&1 | grep -i error; ls -l Challenge.export Main.export | awk '{print $5, $9}'
echo "exported flags of T: $(grep -o '"isRec":[a-z]*,"isReflexive":[a-z]*,"isUnsafe":false,"levelParams":\[\],"name":[0-9]*,"numIndices":0,"numNested":1' Main.export | head -1)"
bash run3.sh Main.export
echo "== variants"
for v in R2 R3 R4 R5 C1 C2; do
  d=$(mktemp -d /tmp/r058.XXXXXX); cp variants/$v.lean mkexp.sh $d/; ( cd $d && bash mkexp.sh $v main_thm T >/dev/null 2>&1 )
  cp $d/$v.export variants/$v.export; rm -rf $d
  lc=$(LEAN_ABORT_ON_PANIC=1 $T36/bin/leanchecker --from-export $D/variants/$v.export 2>&1 | tail -1 | cut -c1-40)
  r=$(${FV_KRUN:-krun} "$X/bin/susz pack --no-index $D/variants/$v.export /tmp/p.susz >/dev/null 2>&1; $X/bin/gruszka /tmp/p.susz 2 2>&1 | tail -1; $X/bin/gruszka-4ad120b /tmp/p.susz 2 2>&1 | tail -1; /scratch/fastverify/checkers/dualkernel/target/release/nl-fast -q -j 2 $D/variants/$v.export 2>&1 | tail -1" 2>&1 | tr '\n' '|')
  echo "$v ($(grep -m1 '| c0' variants/$v.lean | sed 's/^ *//')): $lc | $r"
done

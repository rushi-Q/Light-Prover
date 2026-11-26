#!/bin/bash
# repro for 055: valid project with `structure Foo3 where raw : BaseFoo Box Foo3` (BaseFoo takes a type-constructor
# parameter t : Type u -> Type v; nested occurrence of Foo3 through BaseFoo and, inside BaseFoo's constructor `t α`,
# through Box). Official Lean 4.33.1 build + official lean4export v4.33.0 (comparator target list), then
#   OFFICIAL: unmodified Lean 4.36 `lake comparator` (Lean kernel replay + nanoda)
#   FAST B single (gruszka + kcompare) and FAST B dual (gruszka AND nano-lean + kcompare), exact harness run lines (run3.sh).
# Runs on any x86-64 host (~1 min). Uses the deployed gruszka if it runs on this CPU, else a portable build of the same
# commit (gruszka ae81d8d; see test 001).
set -u
D=$(cd "$(dirname "$0")" && pwd); cd "$D"
T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0; X=${FV_REPRO_DIR:-$LIGHT_LEAN/repro}
echo "== build + export with official Lean 4.33.1 / lean4export v4.33.0"
bash mkexp.sh Challenge main_thm >/dev/null 2>&1; bash mkexp.sh Main main_thm 2>&1 | grep -i error; ls -l Challenge.export Main.export | awk '{print $5, $9}'
bash run3.sh Main.export
echo "== variants (official leanchecker 4.36 | gruszka ae81d8d | gruszka 4ad120b (latest nested fixes) | nl-fast)"
for v in V1 V2 V3 V7 G1 G2 G3; do
  d=$(mktemp -d /tmp/r055.XXXXXX); cp variants/$v.lean mkexp.sh $d/; ( cd $d && bash mkexp.sh $v main_thm >/dev/null 2>&1 )
  lc=$(LEAN_ABORT_ON_PANIC=1 $T36/bin/leanchecker --from-export $d/$v.export 2>&1 | tail -1 | cut -c1-60)
  cp $d/$v.export variants/$v.export; rm -rf $d
  r=$(${FV_KRUN:-krun} "$X/bin/susz pack --no-index $D/variants/$v.export /tmp/p.susz >/dev/null 2>&1; $X/bin/gruszka /tmp/p.susz 2 2>&1 | tail -1; $X/bin/gruszka-4ad120b /tmp/p.susz 2 2>&1 | tail -1; /scratch/fastverify/checkers/dualkernel/target/release/nl-fast -q -j 2 $D/variants/$v.export 2>&1 | tail -1" 2>&1 | tr '\n' '|')
  echo "$v ($(grep -m1 -E 'inductive V|\| c0' variants/$v.lean | sed 's/^ *//')): $lc | $r"
done
echo "== (b) end to end: variants/G1 (inductive T | c0 : List (Nat → List T) → T | c1 : T) through the official comparator and check B"
bash run3.sh variants/G1.export

#!/bin/bash
# repro for 056: valid project, `inductive I4 : Nat → Type | mk (x : Nat) : I4 (x + 1)`, `def I4.get (v : I4 n) : Nat := v.1`
# (numeric projection on an INDEXED inductive family; Lean >= 4.2x elaborates it to Expr.proj and the 4.36 kernel accepts it),
# used in main_thm's proof. Official Lean 4.33.1 build + official lean4export v4.33.0 (comparator target list), then
#   OFFICIAL: unmodified Lean 4.36 `lake comparator` (Lean kernel replay + nanoda), cfg.json
#   FAST B single (gruszka + kcompare) and FAST B dual (gruszka AND nano-lean + kcompare): exact harness lines (run3.sh)
#   + each kernel alone (official leanchecker, official nanoda 4c544ed, C07 nanoda (pchk), gruszka, nl-fast).
set -u
D=$(cd "$(dirname "$0")" && pwd); cd "$D"
T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0; X=${FV_REPRO_DIR:-$LIGHT_LEAN/repro}
echo "== build + export with official Lean 4.33.1 / lean4export v4.33.0"
bash mkexp.sh Challenge main_thm >/dev/null 2>&1; bash mkexp.sh Main main_thm 2>&1 | grep -i error; ls -l Challenge.export Main.export | awk '{print $5, $9}'
bash run3.sh Main.export
echo "== kernels alone on Main.export"
echo "official leanchecker 4.36: $(LEAN_ABORT_ON_PANIC=1 $T36/bin/leanchecker --from-export $D/Main.export 2>&1 | tail -1) (exit ${PIPESTATUS[0]})"
printf '{"use_stdin":false,"export_file_path":"%s","permitted_axioms":["propext","Quot.sound","Classical.choice"],"unpermitted_axiom_hard_error":false,"num_threads":1,"nat_extension":true,"string_extension":true}' $D/Main.export > $D/nanoda1.json
${FV_KRUN:-krun} "
$T36/bin/nanoda_bin $D/nanoda1.json > /tmp/a 2>&1; echo \"official nanoda 4c544ed: exit=\$? \$(grep panicked -A1 /tmp/a | tr '\n' ' ')\"
/scratch/fastverify/checkers/pchk/target/release/nanoda_bin $D/nanoda1.json > /tmp/b 2>&1; echo \"C07 nanoda (pchk): exit=\$? \$(grep panicked -A1 /tmp/b | tr '\n' ' ')\"
$X/bin/susz pack --no-index $D/Main.export /tmp/p.susz >/dev/null 2>&1; $X/bin/gruszka /tmp/p.susz 2 > /tmp/c 2>&1; echo \"gruszka (ae81d8d portable): exit=\$? \$(tail -1 /tmp/c)\"
/scratch/fastverify/checkers/dualkernel/target/release/nl-fast -q -j 2 $D/Main.export > /tmp/d 2>&1; echo \"nl-fast (deployed): exit=\$? \$(tr '\n' ' ' < /tmp/d)\""

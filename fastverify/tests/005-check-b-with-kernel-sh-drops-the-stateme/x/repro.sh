#!/bin/bash
# 005 repro: FAST CHECK B (with-kernel.sh + allof.sh: gruszka AND nano-lean AND kcompare, the fast flow's dual run line)
# ACCEPTS a solution whose theorem statement differs from the challenge as soon as the solution's PATH contains
# "/arena/suite/" (or "/inputs/suitex/"). Official Lean 4.36 `lake comparator` rejects it.
# Run:   bash repro.sh      (inputs: Challenge.export/Main.export made by ./mkexp.sh from the .lean)
D=$(cd "$(dirname "$0")" && pwd); TB=${FV_SANDBOX_BIN:-$LIGHT_LEAN/bin}
T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
S=/scratch/fastverify/checkers/dualkernel
# The deployed gruszka was built with target-cpu=native on the AMD box and dies with SIGILL on Intel hosts
# (separate issue); use the same commit ae81d8d rebuilt with target-cpu=x86-64-v3 (+ the repo's PGO profile) if so.
G=$S/target/release/gruszka
$TB/krun "$S/target/release/susz pack --no-index $D/Main.export /tmp/m.susz >/dev/null 2>&1; $G /tmp/m.susz 1 >/dev/null 2>&1; test \$? -ne 132" || G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka
echo "== OFFICIAL: Lean 4.36 lake comparator (config: theorem main_thm, standard axioms, nanoda)"
d=$(mktemp -d /tmp/r005.XXXXXX); cp $D/cfg.json $d/comparator.json
( cd $d && PATH=$T36/bin:$PATH lake comparator --challenge-from-export $D/Challenge.export --solution-from-export $D/Main.export 2>&1 | tail -3 )
( cd $d && PATH=$T36/bin:$PATH lake comparator --challenge-from-export $D/Challenge.export --solution-from-export $D/Main.export >/dev/null 2>&1 ); echo "OFFICIAL exit=$?"
rm -rf $d
echo "== FAST CHECK B (dual), same files"
$TB/krun "run() { KC_THEOREMS=main_thm /bin/sh $S/kcompare/with-kernel.sh $S/target/release/kcompare $D/Challenge.export \$1 4 -- /bin/sh $S/kcompare/allof.sh -- env K02_THP=1 SUSZ=$S/target/release/susz GRUSZKA=$G /bin/sh $S/scripts/arena-run \$1 16 :: $S/target/release/nl-fast -q -j 16 \$1; echo \"FAST-B exit=\$? (\$1)\"; }
echo '-- solution at its own path'; run $D/Main.export
mkdir -p /tmp/p/arena/suite /tmp/q/inputs/suitex; cp $D/Main.export /tmp/p/arena/suite/; cp $D/Main.export /tmp/q/inputs/suitex/
echo '-- the SAME bytes under a directory named arena/suite'; run /tmp/p/arena/suite/Main.export
echo '-- the SAME bytes under a directory named inputs/suitex'; run /tmp/q/inputs/suitex/Main.export"

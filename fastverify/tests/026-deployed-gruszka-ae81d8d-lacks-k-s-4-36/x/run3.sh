#!/bin/bash
# run3.sh SOL : official lake comparator vs fast check B single (gruszka+kcompare) vs dual (gruszka AND nano-lean AND kcompare)
D=$(cd "$(dirname "$0")" && pwd); TB=${FV_SANDBOX_BIN:-$LIGHT_LEAN/bin}
T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0; S=/scratch/fastverify/checkers/dualkernel
SOL=$(realpath "$1"); CH=$D/Challenge.export
G=$S/target/release/gruszka
$TB/krun "$S/target/release/susz pack --no-index $D/Main.export /tmp/m.susz >/dev/null 2>&1; $G /tmp/m.susz 1 >/dev/null 2>&1; test \$? -ne 132" || G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka
echo "== $(basename $SOL)"
d=$(mktemp -d /tmp/r3.XXXXXX); cp $D/cfg.json $d/comparator.json
( cd $d && PATH=$T36/bin:$PATH lake comparator --challenge-from-export $CH --solution-from-export $SOL > out.txt 2>&1; echo "OFFICIAL lake comparator exit=$? : $(grep -m1 -i 'error\|okay' out.txt)" )
rm -rf $d
$TB/krun "S=$S; G=$G
KC_THEOREMS=main_thm /bin/sh \$S/kcompare/with-kernel.sh \$S/target/release/kcompare $CH $SOL 4 -- env SUSZ=\$S/target/release/susz GRUSZKA=\$G /bin/sh \$S/scripts/arena-run $SOL 16 >/tmp/o1 2>&1; echo \"FAST-B single (gruszka+kcompare) exit=\$? : \$(grep -v '^ok\|allof' /tmp/o1 | tr '\n' ' ')\"
KC_THEOREMS=main_thm /bin/sh \$S/kcompare/with-kernel.sh \$S/target/release/kcompare $CH $SOL 4 -- /bin/sh \$S/kcompare/allof.sh -- env SUSZ=\$S/target/release/susz GRUSZKA=\$G /bin/sh \$S/scripts/arena-run $SOL 16 :: \$S/target/release/nl-fast -q -j 16 $SOL >/tmp/o2 2>&1; echo \"FAST-B dual (gruszka AND nano-lean + kcompare) exit=\$? : \$(grep -v '^ok' /tmp/o2 | tr '\n' ' ' | cut -c1-300)\""

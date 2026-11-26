#!/bin/sh
# flows.sh CHALLENGE SOLUTION : OFFICIAL lake comparator (4.36, sandboxed) vs fast A (pchk run.sh) vs fast B dual/single
# (with-kernel.sh kcompare + allof(gruszka,nl-fast) / gruszka) on the same export files. Prints exit codes.
H=${FV_REPRO_DIR:-$LIGHT_LEAN/repro}
C=$(readlink -f "$1"); S=$(readlink -f "$2")
T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
D=/scratch/fastverify/checkers/dualkernel; P=/scratch/fastverify/checkers/pchk
G=${GR:-${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka-v3}
W=$(mktemp -d /tmp/x08flows.XXXXXX); cp $LIGHT_LEAN/fastverify/tests/024-check-b-lacks-the-nanoda-leg-export-with/x/comparator.json $W/
( cd $W && PATH=$T36/bin:/usr/bin:/bin timeout 600 lake comparator --config $W/comparator.json --challenge-from-export "$C" --solution-from-export "$S" ) > $W/off.log 2>&1; ro=$?
[ -n "$FV" ] && { echo "--- official comparator"; tail -6 $W/off.log; }
rm -rf $W
${FV_KRUN:-krun} "
cd /tmp
CCMP_LEANCHECKER=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k sh $P/run.sh $P $S 8 $C > /tmp/a.log 2>&1; ra=\$?
sh $D/kcompare/with-kernel.sh $D/target/release/kcompare $C $S 4 -- sh $D/kcompare/allof.sh -- env SUSZ=$D/target/release/susz GRUSZKA=$G sh $D/scripts/arena-run $S 4 :: $D/target/release/nl-fast -q -j 4 $S > /tmp/b.log 2>&1; rb=\$?
sh $D/kcompare/with-kernel.sh $D/target/release/kcompare $C $S 4 -- env SUSZ=$D/target/release/susz GRUSZKA=$G sh $D/scripts/arena-run $S 4 > /tmp/b1.log 2>&1; rb1=\$?
echo \"OFFICIAL=$ro  FAST-A(pchk)=\$ra  FAST-B-dual=\$rb  FAST-B-single=\$rb1   $(basename $S)\"
[ -n \"$FV\" ] && { echo '--- A'; tail -5 /tmp/a.log; echo '--- B dual'; tail -6 /tmp/b.log; echo '--- B single'; tail -4 /tmp/b1.log; }
"

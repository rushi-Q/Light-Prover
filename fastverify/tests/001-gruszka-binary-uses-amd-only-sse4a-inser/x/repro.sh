#!/bin/sh
# Finding 001: the deployed gruszka binary (/scratch/fastverify/checkers/dualkernel/target/release/gruszka) was built
# with -C target-cpu=native on the AMD node and contains the AMD-only SSE4a instruction INSERTQ
# (in <gruszka::env::Loader as susz::read::Visit>::decl). On Intel hosts it dies with SIGILL on
# every export that has declarations to load, so fast check B (single: gruszka+kcompare; dual: gruszka AND nano-lean)
# can never accept there, while the official checker accepts.
# Runs on an Intel host (uses the krun sandbox).
D=/scratch/fastverify/checkers/dualkernel
LC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0/bin/leanchecker
IN=/scratch/bench-inputs/arena/suite/good/init-prelude.ndjson   # a GOOD export (Init prelude), official accepts
K=${FV_KRUN:-krun}
H=$(dirname "$(readlink -f "$0")")
grep -m1 'model name' /proc/cpuinfo
echo "insertq occurrences in gruszka: $(objdump -d --no-show-raw-insn $D/target/release/gruszka | grep -c insertq)"
$K "
LEAN_ABORT_ON_PANIC=1 $LC --silent --from-export $IN; echo \"OFFICIAL leanchecker exit=\$?\"
SUSZ=$D/target/release/susz GRUSZKA=$D/target/release/gruszka /bin/sh $D/scripts/arena-run $IN 4; echo \"FAST single-kernel (arena-run: susz+gruszka) exit=\$?\"
/bin/sh $D/kcompare/with-kernel.sh $D/target/release/kcompare '' $IN 4 -- /bin/sh $D/kcompare/allof.sh -- env SUSZ=$D/target/release/susz GRUSZKA=$D/target/release/gruszka /bin/sh $D/scripts/arena-run $IN 4 :: $D/target/release/nl-fast -q -j 4 $IN; echo \"FAST dual (with-kernel/allof gruszka AND nl-fast) exit=\$?\"
$D/target/release/susz pack --no-index $IN /tmp/x.susz >/dev/null 2>&1
LD_PRELOAD=$H/sigill.so $D/target/release/gruszka /tmp/x.susz 1
"

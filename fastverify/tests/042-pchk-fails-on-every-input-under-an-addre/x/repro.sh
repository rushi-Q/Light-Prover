#!/bin/bash
# 0xx repro: run the official comparator and the fast checks under the SAME address-space limit (ulimit -v, RLIMIT_AS),
# as set by many batch systems / shared hosts. Input: toy/good (honest 5-theorem toy project, 1 MB export; official
# Lean 4.33.1 build + official lean4export). VLIMITS (KB) default "16000000 64000000 256000000".
set -u
H=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
KRUN=${FV_KRUN:-krun}
PCHK=/scratch/fastverify/checkers/pchk; DK=/scratch/fastverify/checkers/dualkernel
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi
G=${GRUSZKA:-$DK/target/release/gruszka}
CH=$H/toy/good/challenge.export; SOL=$H/toy/good/solution.export
$KRUN "SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 2" >/dev/null 2>&1; [ $? -eq 132 ] && G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka-v3
echo "host: $(hostname), $(nproc) CPUs in affinity mask; pleanchecker-k=$PLC"
W=$(mktemp -d /tmp/x04-as.XXXXXX); trap 'rm -rf "$W"' EXIT; cd $W
cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "external_kernels": {"nanoda": ["nanoda_bin"]}}
JSON
for v in ${VLIMITS:-16000000 64000000 256000000}; do
  echo "### ulimit -v $v KB ($((v/1000000)) GB address space)"
  (ulimit -v $v; PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL > o.log 2>&1; echo "OFFICIAL lake comparator (+nanoda):         exit $?  $(grep -m1 -E 'okay|^error' o.log)")
  (ulimit -v $v; $KRUN "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $SOL 32 $CH" > f.log 2>&1; echo "FAST A pchk run.sh T=32:                     exit $?  $(grep -m2 -E 'okay|^error|failed to create' f.log | tr '\n' ' ' | cut -c1-150)")
  (ulimit -v $v; timeout -k 5 ${BLIMIT:-300} $KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 16 -- sh $DK/kcompare/allof.sh -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 16 :: $DK/target/release/nl-fast -q -j 16 $SOL" > b.log 2>&1; r=$?; echo "FAST B kcompare + (gruszka AND nl-fast) x16: exit $r$( [ $r = 124 ] && echo " = TIMEOUT after ${BLIMIT:-300}s (hang)")  $(grep -m1 'with-kernel' b.log)")
done

#!/bin/bash
# 0xx repro: valid project whose riemannHypothesis is `Nat.shiftRight 5 (2^64) = 0 := by decide` (official Lean 4.33.1
# build + official lean4export v4.33.0, toy/mk.sh). Each checker gets a wall-clock limit of LIMIT seconds (default 300).
set -u
H=$(cd "$(dirname "$0")" && pwd); LIMIT=${LIMIT:-300}
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk
DK=/scratch/fastverify/checkers/dualkernel
KRUN=${FV_KRUN:-krun}
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi
G=${GRUSZKA:-$DK/target/release/gruszka}
$KRUN "SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $H/toy/shr/solution.export 2" >/dev/null 2>&1
[ $? -eq 132 ] && G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka-v3
echo "binaries: pleanchecker-k=$PLC gruszka=$G; limit ${LIMIT}s per checker"
CH=$H/toy/shr/challenge.export; SOL=$H/toy/shr/solution.export
W=$(mktemp -d /tmp/x04-shr.XXXXXX); trap 'rm -rf "$W"' EXIT; cd $W
cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
JSON
sed 's/}$/, "external_kernels": {"nanoda": ["nanoda_bin"]}}/' comparator.json > comparator.nanoda.json
t() { local s=$(date +%s); timeout -k 5 $LIMIT "$@" > out.log 2>&1; local r=$?; echo "exit $r ($(( $(date +%s) - s )) s)$( [ $r = 124 ] && echo ' = TIMEOUT, no verdict')  $(grep -m1 -E 'okay|^error|with-kernel' out.log | cut -c1-90)"; }
echo "OFFICIAL lake comparator 4.36, Lean kernel only     : $(PATH=$TC/bin:$PATH t $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL)"
echo "OFFICIAL lake comparator 4.36, nanoda + Lean kernel : $(PATH=$TC/bin:$PATH t $TC/bin/lake comparator --config comparator.nanoda.json --challenge-from-export $CH --solution-from-export $SOL)"
echo "FAST A  pchk run.sh (pchk's nanoda + pleanchecker-k)   : $(t $KRUN "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $SOL 8 $CH")"
echo "FAST B  kcompare + (gruszka AND nl-fast)            : $(t $KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- sh $DK/kcompare/allof.sh -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 4 :: $DK/target/release/nl-fast -q -j 4 $SOL")"
echo "FAST B1 kcompare + gruszka                          : $(t $KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 4")"

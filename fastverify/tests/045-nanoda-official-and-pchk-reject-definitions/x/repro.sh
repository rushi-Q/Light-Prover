#!/bin/bash
# 045 repro: valid project = 65540 generated definitions c(i) := c(i-1) (+ the 5 RH-named theorems, riemannHypothesis's
# proof mentions c65539). Official Lean 4.33.1 builds it and the official lean4export writes "hints":{"regular":65541}.
# toy/height/solution.export is that export (regenerate: cd toy/height && python3 gen.py && cd .. && ./mk.sh height).
set -u
H=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk; DK=/scratch/fastverify/checkers/dualkernel
KRUN=${FV_KRUN:-krun}
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi
CH=$H/toy/height/challenge.export; SOL=$H/toy/height/solution.export
G=${GRUSZKA:-$DK/target/release/gruszka}
$KRUN "SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 2" >/dev/null 2>&1; [ $? -eq 132 ] && G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka-v3
echo "max reducibility height in the export: $(grep -o '"regular":[0-9]*' $SOL | cut -d: -f2 | sort -n | tail -1)"
W=$(mktemp -d /tmp/x04-045.XXXXXX); trap 'rm -rf "$W"' EXIT; cd $W
cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
JSON
sed 's/}$/, "external_kernels": {"nanoda": ["nanoda_bin"]}}/' comparator.json > comparator.nanoda.json
PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL > o1.log 2>&1
echo "OFFICIAL lake comparator 4.36, Lean kernel only:     exit $?  $(grep -m1 -E 'okay|^error' o1.log)"
PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.nanoda.json --challenge-from-export $CH --solution-from-export $SOL > o2.log 2>&1
echo "OFFICIAL lake comparator 4.36, nanoda + Lean kernel: exit $?  $(grep -m1 -E 'okay|^error' o2.log)  [nanoda: $(grep -m1 -E 'invalid value|expected u16' o2.log | cut -c1-80)]"
$KRUN "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $SOL 8 $CH" > a.log 2>&1
echo "FAST A  pchk run.sh:                                 exit $?  $(grep -m1 -E 'okay|^error' a.log)"
$KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- sh $DK/kcompare/allof.sh -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 4 :: $DK/target/release/nl-fast -q -j 4 $SOL" > b.log 2>&1
echo "FAST B  kcompare + (gruszka AND nl-fast):            exit $?  $(grep -m1 'with-kernel' b.log)"
$KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 4" > c.log 2>&1
echo "FAST B1 kcompare + gruszka:                          exit $?  $(grep -m1 'with-kernel' c.log)"

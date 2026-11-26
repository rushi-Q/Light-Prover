#!/bin/bash
# 010 repro: a VALID Lean 4.33.1 project (5 RH-named theorems about string literals, each `by decide`), built with the
# official Lean 4.33.1 and exported with the official lean4export v4.33.0 (toy/mk.sh). The official 4.36 comparator
# REJECTS it (Lean/Replay.lean replays in NameSet order with only syntactic deps; the kernel's string-literal expansion
# needs String.ofList/Char.ofNat which are not yet replayed -> type mismatch). Fast check B (kcompare + gruszka AND
# nl-fast, and the single-kernel variant gruszka + kcompare) ACCEPTS it. pchk (fast check A) replicates the official
# walk order and rejects like the official.
set -u
H=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk
DK=/scratch/fastverify/checkers/dualkernel
KRUN=${FV_KRUN:-krun}
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi   # a local rebuild of pchk d876802 (build_k.sh)
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=$PCHK/.lake/build/bin/pleanchecker; fi
# deployed gruszka SIGILLs on the Intel hosts (finding 001): default to a portable rebuild of the same commit ae81d8d
G=${GRUSZKA:-$DK/target/release/gruszka}
$KRUN "SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $H/toy/str/solution.export 2" >/dev/null 2>&1
[ $? -eq 132 ] && G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka-v3
echo "binaries: pleanchecker=$PLC gruszka=$G"
CH=$H/toy/str/challenge.export; SOL=$H/toy/str/solution.export
W=$(mktemp -d /tmp/x04-010.XXXXXX); trap 'rm -rf "$W"' EXIT; cd $W
cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
JSON
sed 's/}$/, "external_kernels": {"nanoda": ["nanoda_bin"]}}/' comparator.json > comparator.nanoda.json
echo "--- source (toy/str/Main.lean):"; cat $H/toy/str/Main.lean
PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL > o1.log 2>&1
echo "OFFICIAL lake comparator 4.36 (Lean kernel):            exit $?  $(grep -m1 -E 'okay|error' o1.log | cut -c1-120)"
PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.nanoda.json --challenge-from-export $CH --solution-from-export $SOL > o2.log 2>&1
echo "OFFICIAL lake comparator 4.36 (nanoda + Lean kernel):   exit $?  $(grep -m1 -E 'okay|error' o2.log | cut -c1-120)"
$KRUN "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $SOL 8 $CH" > a.log 2>&1
echo "FAST A  pchk run.sh:                                    exit $?  $(grep -m1 -E 'okay|^error' a.log | cut -c1-120)"
$KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- sh $DK/kcompare/allof.sh -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 4 :: $DK/target/release/nl-fast -q -j 4 $SOL" > b.log 2>&1
echo "FAST B  kcompare + (gruszka AND nl-fast):               exit $?  $(grep -m1 'with-kernel' b.log)"
$KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 4" > c.log 2>&1
echo "FAST B1 kcompare + gruszka (single external kernel):    exit $?  $(grep -m1 'with-kernel' c.log)"

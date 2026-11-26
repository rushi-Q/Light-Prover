#!/bin/bash
# 002 repro: pchk run.sh (fast check A) and kcompare/with-kernel.sh (fast check B) drop the statement/axiom comparison
# (and, for run.sh, also nanoda) when no challenge is given OR when the export path contains /suitex/ or /arena/suite/.
# Inputs: toy/{axiom,wrongstmt}/{challenge,solution}.export (built by toy/mk.sh with official Lean 4.33.1 + official
# lean4export v4.33.0 from the .lean files next to them).
# Kernels run under the krun sandbox.
set -u
H=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk
DK=/scratch/fastverify/checkers/dualkernel
KRUN=${FV_KRUN:-krun}
# The deployed pleanchecker-k needs GLIBC 2.38 (not on hosts with glibc 2.35); fall back to the official-kernel
# pleanchecker built from the same pchk commit (same Par.lean replay) unless PLC is given (e.g. a local rebuild of -k).
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi   # a local rebuild of pchk d876802 (build_k.sh)
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=$PCHK/.lake/build/bin/pleanchecker; fi
echo "pchk Lean-kernel replay binary used: $PLC"
W=$(mktemp -d $H/run.XXXXXX)   # visible (read-only) inside krun
trap 'rm -rf "$W"' EXIT
for case in axiom wrongstmt; do
  CH=$H/toy/$case/challenge.export; SOL=$H/toy/$case/solution.export
  mkdir -p $W/$case/plain $W/$case/x/suitex $W/$case/x/arena/suite/bad $W/$case/y/inputs/suitex
  for d in plain x/suitex x/arena/suite/bad y/inputs/suitex; do cp $SOL $W/$case/$d/solution.export; done
  cd $W/$case
  cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
 "external_kernels": {"nanoda": ["nanoda_bin"]}}
JSON
  echo "################ case $case: $(head -c 300 $H/toy/$case/Main.lean | head -2 | tr '\n' ' ')"
  PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $W/$case/plain/solution.export > off.log 2>&1
  echo "OFFICIAL lake comparator 4.36 (Lean kernel + nanoda):  exit $?   $(grep -m1 -E '^error' off.log)"
  for d in plain x/suitex x/arena/suite/bad; do
    $KRUN "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $W/$case/$d/solution.export 8 $CH" > f.log 2>&1
    echo "FAST A  run.sh  SRC EXPORT 8 CHALLENGE  (EXPORT under .../$d/):  exit $?   $(grep -m1 -E '^error|okay|accepts' f.log)"
  done
  $KRUN "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $W/$case/plain/solution.export 8" > f.log 2>&1
  echo "FAST A  run.sh  SRC EXPORT 8            (no challenge):            exit $?   $(grep -m1 -E '^error|okay|accepts' f.log)"
  # fast check B wrapper (gruszka SIGILLs on Intel hosts, finding 001: the second kernel here is nl-fast only)
  for d in plain y/inputs/suitex x/arena/suite/bad; do
    $KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $W/$case/$d/solution.export 4 -- $DK/target/release/nl-fast -q -j 4 $W/$case/$d/solution.export" > b.log 2>&1
    echo "FAST B  with-kernel.sh kcompare CH EXPORT -- nl-fast (EXPORT under .../$d/): exit $?   $(grep -m1 -iE 'error|mismatch|illegal|not match' b.log | cut -c1-120)"
  done
done

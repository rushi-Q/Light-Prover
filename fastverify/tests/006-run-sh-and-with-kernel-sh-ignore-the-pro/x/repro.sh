#!/bin/bash
# 003 repro: the fast wrappers ignore the project's comparator configuration.
#  case constr: project config permits only [propext, Quot.sound] (a constructive challenge); the solution uses
#               Classical.em (-> Classical.choice). Official: reject. Fast A/B: accept (they hard-code the RH axiom list).
#  case names:  a correct solution of a project whose theorem is not one of the 5 RH names. Official: accept.
#               Fast A: reject (hard-coded RH names -> "Const not found"); fast B: reject.
# Inputs: toy/*/{challenge,solution}.export (toy/mk.sh: official Lean 4.33.1 + official lean4export v4.33.0).
set -u
H=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk
DK=/scratch/fastverify/checkers/dualkernel
KRUN=${FV_KRUN:-krun}
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi   # a local rebuild of pchk d876802 (build_k.sh)
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=$PCHK/.lake/build/bin/pleanchecker; fi
echo "pchk Lean-kernel replay binary used: $PLC"
W=$(mktemp -d /tmp/x04-003.XXXXXX); trap 'rm -rf "$W"' EXIT; cd $W
for case in constr names; do
  CH=$H/toy/$case/challenge.export; SOL=$H/toy/$case/solution.export
  if [ $case = constr ]; then
    TH='"riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"'
    AX='"propext", "Quot.sound"'
  else
    TH='"fermatLittle_two"'; AX='"propext", "Quot.sound", "Classical.choice"'
  fi
  cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main", "theorem_names": [$TH],
 "definition_names": [], "permitted_axioms": [$AX], "external_kernels": {"nanoda": ["nanoda_bin"]}}
JSON
  echo "################ case $case: project comparator.json = $(tr -d '\n' < comparator.json)"
  PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL > off.log 2>&1
  echo "OFFICIAL lake comparator 4.36 (project config):        exit $?   $(grep -m1 -E '^error|okay' off.log)"
  $KRUN "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $SOL 8 $CH" > f.log 2>&1
  echo "FAST A  run.sh SRC EXPORT 8 CHALLENGE (no way to pass the config): exit $?   $(grep -m1 -E '^error|okay' f.log)"
  $KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- $DK/target/release/nl-fast -q -j 4 $SOL" > b.log 2>&1
  echo "FAST B  with-kernel.sh kcompare CH EXPORT -- nl-fast (defaults):  exit $?   $(grep -m1 -iE 'kcompare' b.log | cut -c1-140)"
done

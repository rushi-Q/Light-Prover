#!/bin/bash
# 013 repro: verdict-relevant settings come from the caller's environment (the official comparator runs every kernel
# with a CLEARED environment: env -i bwrap --clearenv, only LEAN_ABORT_ON_PANIC=1 and HOME).
set -u
H=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk
DK=/scratch/fastverify/checkers/dualkernel
KRUN=${FV_KRUN:-krun}
W=$(mktemp -d /tmp/x04-013.XXXXXX); trap 'rm -rf "$W"' EXIT; cd $W
cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "external_kernels": {"nanoda": ["nanoda_bin"]}}
JSON
CH=$H/toy/partial/challenge.export; SOL=$H/toy/partial/solution.export
echo "### 1. toy/partial (riemannHypothesis proved from 'axiom cheat : False'), caller has KC_THEOREMS in its environment"
PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL > o.log 2>&1
echo "OFFICIAL lake comparator 4.36:                                          exit $?  $(grep -m1 -E 'okay|^error' o.log)"
$KRUN "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- $DK/target/release/nl-fast -q -j 4 $SOL" > b0.log 2>&1
echo "FAST B with-kernel.sh (kcompare + nl-fast), clean env:                  exit $?  $(grep -m1 'kcompare' b0.log)"
$KRUN "export KC_THEOREMS=riemannZeta_eq_zero_re; sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- $DK/target/release/nl-fast -q -j 4 $SOL" > b.log 2>&1
echo "FAST B with-kernel.sh, env KC_THEOREMS=riemannZeta_eq_zero_re:          exit $?  $(grep -m1 'kcompare' b.log)"
CH=$H/toy/sorry/challenge.export; SOL=$H/toy/sorry/solution.export
echo "### 1b. toy/sorry (solution = the challenge itself, every proof is 'sorry'), caller has KC_AXIOMS in its environment"
PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL > o.log 2>&1
echo "OFFICIAL lake comparator 4.36:                                          exit $?  $(grep -m1 -E 'okay|^error' o.log)"
$KRUN "export KC_AXIOMS=propext,Quot.sound,Classical.choice,sorryAx; sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- $DK/target/release/nl-fast -q -j 4 $SOL" > b2.log 2>&1
echo "FAST B with-kernel.sh, env KC_AXIOMS=propext,Quot.sound,Classical.choice,sorryAx: exit $?  $(grep -m1 'kcompare' b2.log)"
echo "### 2. pchk: CCMP_LEANCHECKER from the environment replaces the Lean kernel (run.sh: \${CCMP_LEANCHECKER:-...})"
CH=$H/toy/str/challenge.export; SOL=$H/toy/str/solution.export
PATH=$TC/bin:$PATH $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL > o.log 2>&1
echo "OFFICIAL lake comparator 4.36 (toy/str, Lean kernel rejects, see 012): exit $?  $(grep -m1 -E 'okay|^error' o.log)"
$KRUN "export CCMP_LEANCHECKER=/bin/true; sh $PCHK/run.sh $PCHK $SOL 8 $CH" > a.log 2>&1
echo "FAST A run.sh, env CCMP_LEANCHECKER=/bin/true:                         exit $?  $(grep -m1 -E 'okay|^error' a.log)"
$KRUN "export PCHK_NICE='0 /bin/true #'; sh $PCHK/run.sh $PCHK $SOL 8 $CH" > a2.log 2>&1
echo "FAST A run.sh, env PCHK_NICE='0 /bin/true #' (spliced into a generated wrapper script): exit $?  $(grep -m1 -E 'okay|^error' a2.log)"

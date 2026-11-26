#!/bin/bash
# Regression test of the duplicate-theorem consolidation pipeline: a 4-module core-Lean project with
#  - DdB.b_one = DdA.a_one (same statement, other proof, target visible)          -> ALIAS (alias mode)
#  - DdC.c_two = DdA.a_two (target not imported; topologically later module)       -> IMPORT (+ `import Dd.A`)
#  - DdB.b_imp ~ DdA.a_imp (same type up to binder info: explicit vs implicit n)   -> proof mode
# Pipeline: lake build -> dupscan scan (bwrap) -> dupanalyze -> dupscan cmp -> imports.py -> dupplan -> dedup_edits
# (auto, core-Lean alias form) -> apply_edits -> lake build of the edited project; then a REDIRECT round (b_one deleted,
# its full-name use in b_use rewritten by a subst edit). PASS iff every step works, both edited projects build, the
# expected forms are present and the edited theorems keep their statements.
# Needs: Lean 4.33.1 toolchain ($ELAN_HOME or ~/.elan), bwrap. Builds dupscan once into $DUPSCAN_DIR (default /tmp).
set -u
T=$(cd "$(dirname "$0")/.." && pwd); P=$T/test/proj
W=$(mktemp -d /tmp/dedup-test.XXXXXX); trap 'rm -rf $W' EXIT
TC=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1; export PATH=$TC/bin:$PATH
fail() { echo "FAIL: $*"; exit 1; }
DS=${DUPSCAN_DIR:-/tmp/dedup-dupscan-$USER}
if [ ! -x $DS/.lake/build/bin/dupscan ] || [ $T/dupscan/Main.lean -nt $DS/.lake/build/bin/dupscan ]; then
  mkdir -p $DS && cp $T/dupscan/{Main.lean,lakefile.toml,lean-toolchain,lake-manifest.json} $DS/ && (cd $DS && lake build >/dev/null 2>&1) || fail "dupscan build"
fi
export DUPSCAN=$DS/.lake/build/bin/dupscan
cp -r $P $W/proj && rm -rf $W/proj/.lake && (cd $W/proj && lake build >/dev/null 2>&1) || fail "base build"
L=$W/proj/.lake/build/lib/lean
for m in A B C Main; do printf 'Dd.%s\t%s/Dd/%s.olean\n' $m $L $m; done > $W/list
bash $T/run_scan.sh $W/list $W/scan $W 1 >/dev/null || fail "scan"
python3 $T/dupanalyze.py $W/scan/out $W/ana >/dev/null || fail "dupanalyze"
awk -F'\t' -v OFS='\t' -v L=$L '{p=$2; gsub(/\./,"/",p); print $1, $2, L "/" p ".olean", $4}' $W/ana/groups.tsv > $W/cmplist
bash $T/run_cmp.sh $W/cmplist $W/cmp $W 1 >/dev/null || fail "cmp"
python3 $T/imports.py $W/proj $W/imports.json >/dev/null || fail "imports"
python3 $T/dupplan.py $W/scan/out $W/cmp $W/proj $W/imports.json $W/plan 1000000 >/dev/null || fail "dupplan"
python3 $T/dedup_edits.py $W/plan/plan.tsv $W/proj $W/edits.tsv --actions ALIAS,IMPORT --mode auto --alias-form typeof --scan $W/scan/out --protect main_thm,main_thm2 > $W/edits.json || fail "dedup_edits"
python3 $T/apply_edits.py $P $W/out $W/edits.tsv --srcdir . --copy > $W/apply.json || fail "apply_edits"
rm -rf $W/out/.lake; (cd $W/out && lake build > $W/build2.log 2>&1) || { cat $W/build2.log; fail "edited project does not build"; }
grep -q 'theorem b_one : type_of% @_root_.DdA.a_one := @_root_.DdA.a_one' $W/out/Dd/B.lean || fail "b_one not aliased"
grep -q '^import Dd.A' $W/out/Dd/C.lean || fail "C did not get import Dd.A"
grep -q 'theorem c_two : type_of% @_root_.DdA.a_two := @_root_.DdA.a_two' $W/out/Dd/C.lean || fail "c_two not aliased"
grep -q 'theorem b_imp (n : Nat) : n \* 1 = n := by first | exact _root_.DdA.a_imp' $W/out/Dd/B.lean || fail "b_imp not in proof mode"
grep -q 'theorem a_one' $W/out/Dd/A.lean || fail "canonical a_one lost"
cat > $W/Check.lean <<'EOC'
import Dd.Main
example : ∀ n : Nat, n + 0 = n := DdB.b_one
example : ∀ k : Nat, 0 + k = k := DdC.c_two
example : ∀ n : Nat, n * 1 = n := DdB.b_imp
example : ∀ n : Nat, n + 0 + 0 = n := main_thm
EOC
cp $W/Check.lean $W/out/Dd/Check.lean; (cd $W/out && lake env lean Dd/Check.lean > $W/check.log 2>&1) || { cat $W/check.log; fail "statements changed"; }
# redirect round: b_one / c_two are used by full name only -> deleted, uses rewritten
python3 $T/redirect_check.py $W/scan/out $W/plan/plan.tsv $W/proj $W/redirect.tsv > /dev/null || fail "redirect_check"
grep -q $'^DdB.b_one\t.*\tOK$' $W/redirect.tsv || { cat $W/redirect.tsv; fail "b_one not redirectable"; }
python3 $T/dedup_edits.py $W/plan/plan.tsv $W/proj $W/edits-r.tsv --actions ALIAS,IMPORT --mode auto --alias-form typeof --scan $W/scan/out --redirect $W/redirect.tsv --protect main_thm,main_thm2 > $W/edits-r.json || fail "dedup_edits redirect"
python3 $T/apply_edits.py $P $W/outr $W/edits-r.tsv --srcdir . --copy > $W/apply-r.json || fail "apply_edits redirect"
rm -rf $W/outr/.lake; (cd $W/outr && lake build > $W/build3.log 2>&1) || { cat $W/build3.log; fail "redirected project does not build"; }
grep -q 'theorem b_one' $W/outr/Dd/B.lean && fail "b_one not deleted"
grep -q 'DdA.a_one (m + 0)' $W/outr/Dd/B.lean || fail "b_use not rewritten"
sed -i '/DdB.b_one/d; /DdC.c_two/d' $W/Check.lean; cp $W/Check.lean $W/outr/Dd/Check.lean
(cd $W/outr && lake env lean Dd/Check.lean > $W/check3.log 2>&1) || { cat $W/check3.log; fail "statements changed (redirect)"; }
echo "PASS ($(python3 -c "import json; d=json.load(open('$W/edits.json')); r=json.load(open('$W/edits-r.json')); print(d.get('edited',0), 'edited,', d.get('import_lines_added',0), 'import; redirect round:', r.get('redirected',0), 'deleted')"))"

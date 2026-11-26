#!/bin/bash
# Regression tests of the composite-scheme repairs. No Lean needed (~2 s).
#  1. apply_edits.py subst rewrites references written `_root_.OLD` (full-RH C1 build: 'Unknown identifier `_root_.M`')
#     and still leaves longer dotted names `X.OLD` alone.
#  2. normalize.py NCS keeps `noncomputable section` when the module has an `example` (examples are compiled: C1 build
#     'failed to compile definition, consider marking it as noncomputable').
#  3. dedup_filter.py drops: an IMPORT member + the added import (--no-import), a redirect whose member is used by its
#     SHORT name, an alias whose short name heads an application with a NAMED argument, a redirect mentioned by a module
#     without a subst edit; keeps a clean redirect and a clean alias; a dropped member keeps its original declaration.
set -u
T=$(cd "$(dirname "$0")/.." && pwd); W=$(mktemp -d /tmp/d17-scheme-test.XXXXXX); trap 'rm -rf $W' EXIT
fail() { echo "FAIL: $*"; exit 1; }
n=0; ok() { n=$((n+1)); }
# --- 1
mkdir -p $W/p/src/M
printf 'theorem a : True := _root_.Foo.bar\ntheorem b : True := Foo.bar\ntheorem c : True := X.Foo.bar\ntheorem d : True := @_root_.Foo.bar\n' > $W/p/src/M/A.lean
printf 'M.A\t0\t0\tsubst\tP03-dedup\tFoo.bar Baz.qux\n' > $W/e1.tsv
python3 -I $T/../dedup/apply_edits.py $W/p $W/o1 $W/e1.tsv --srcdir src > /dev/null || fail "apply_edits"
grep -q '^theorem a : True := _root_.Baz.qux$' $W/o1/src/M/A.lean || fail "_root_.OLD not rewritten"; ok
grep -q '^theorem b : True := Baz.qux$' $W/o1/src/M/A.lean || fail "OLD not rewritten"; ok
grep -q '^theorem c : True := X.Foo.bar$' $W/o1/src/M/A.lean || fail "X.OLD rewritten"; ok
grep -q '^theorem d : True := @_root_.Baz.qux$' $W/o1/src/M/A.lean || fail "@_root_.OLD not rewritten"; ok
printf 'M.A\t0\t0\tsubst\tP03-dedup\tFoo.bar _root_.Baz.qux\n' > $W/e1b.tsv
python3 -I $T/../dedup/apply_edits.py $W/p $W/o1b $W/e1b.tsv --srcdir src > /dev/null || fail "apply_edits (rooted NEW)"
grep -q '^theorem a : True := _root_.Baz.qux$' $W/o1b/src/M/A.lean || fail "_root_.OLD -> rooted NEW doubled or missing"; ok
grep -q '^theorem b : True := _root_.Baz.qux$' $W/o1b/src/M/A.lean || fail "OLD -> rooted NEW"; ok
grep -q '^theorem c : True := X.Foo.bar$' $W/o1b/src/M/A.lean || fail "X.OLD rewritten (rooted NEW)"; ok
# --- 2
python3 -I - $T/../normalize <<'PY' || fail "NCS"
import sys; sys.path.insert(0, sys.argv[1]); import normalize as N
ex = ['import Mathlib', 'noncomputable section', 'example : CommGroup G := inferInstance', 'end']
th = ['import Mathlib', 'noncomputable section', 'theorem t : True := trivial', 'end']
assert N.ncs_edits(ex) == [], N.ncs_edits(ex)
assert N.ncs_edits(th) != [], 'NCS no longer removes a theorem-only section'
PY
ok; ok
# --- 3
mkdir -p $W/q/src/Q
cat > $W/q/src/Q/A.lean <<'L'
namespace NA
theorem tgt1 : True := trivial
theorem tgt2 (x : Nat) : x = x := rfl
theorem tgt3 : True := trivial
theorem tgt4 : True := trivial
end NA
L
cat > $W/q/src/Q/B.lean <<'L'
import Q.A
namespace NB
theorem red_ok : True := trivial
theorem red_short : True := trivial
theorem use1 : True := red_short
theorem al_named (y : Nat) : y = y := rfl
theorem use2 : 1 = 1 := al_named (y := 1)
theorem al_ok : True := trivial
theorem imp_m : True := trivial
theorem red_nosub : True := trivial
private theorem red_priv : True := trivial
theorem use3 : True := red_priv
end NB
L
printf 'import Q.B\ntheorem u : True := NB.red_ok\ntheorem v : True := NB.red_nosub\n' > $W/q/src/Q/C.lean
H='group\taction\tname\tmodule\ttarget\ttarget_module\tstmt_lines\tproof_lines\tin_closure\tindegree\tprivate\tline1\tline2'
{ printf "$H\n"
  printf '1\tALIAS\tNB.red_ok\tQ.B\tNA.tgt1\tQ.A\t1\t1\t0\t1\t0\t3\t3\n'
  printf '2\tALIAS\tNB.red_short\tQ.B\tNA.tgt3\tQ.A\t1\t1\t0\t1\t0\t4\t4\n'
  printf '3\tALIAS\tNB.al_named\tQ.B\tNA.tgt2\tQ.A\t1\t1\t0\t1\t0\t6\t6\n'
  printf '4\tALIAS\tNB.al_ok\tQ.B\tNA.tgt1\tQ.A\t1\t1\t0\t1\t0\t8\t8\n'
  printf '5\tIMPORT\tNB.imp_m\tQ.B\tNA.tgt4\tQ.A\t1\t1\t0\t1\t0\t9\t9\n'
  printf '6\tALIAS\tNB.red_nosub\tQ.B\tNA.tgt4\tQ.A\t1\t1\t0\t1\t0\t10\t10\n'
  printf '7\tALIAS\t_private.Q.B.0.NB.red_priv\tQ.B\tNA.tgt4\tQ.A\t1\t1\t0\t1\t1\t11\t11\n'; } > $W/plan.tsv
{ printf 'Q.B\t3\t3\tdelete\tP03-dedup\t\n'; printf 'Q.B\t3\t3\tsubst\tP03-dedup\tNB.red_ok NA.tgt1\n'; printf 'Q.C\t0\t0\tsubst\tP03-dedup\tNB.red_ok NA.tgt1\n'
  printf 'Q.B\t4\t4\tdelete\tP03-dedup\t\n'; printf 'Q.B\t4\t4\tsubst\tP03-dedup\tNB.red_short NA.tgt3\n'
  printf 'Q.B\t6\t6\treplace\tP03-dedup\talias al_named := _root_.NA.tgt2\n'
  printf 'Q.B\t8\t8\treplace\tP03-dedup\talias al_ok := _root_.NA.tgt1\n'
  printf 'Q.B\t2\t1\tinsert_before\tP03-dedup\timport Q.Z\n'; printf 'Q.B\t9\t9\treplace\tP03-dedup\talias imp_m := _root_.NA.tgt4\n'
  printf 'Q.B\t10\t10\tdelete\tP03-dedup\t\n'; printf 'Q.B\t10\t10\tsubst\tP03-dedup\tNB.red_nosub NA.tgt4\n'
  printf 'Q.B\t11\t11\tdelete\tP03-dedup\t\n'; printf 'Q.B\t11\t11\tsubst\tP03-dedup\tNB.red_priv NA.tgt4\n'; } > $W/e3.tsv
python3 -I $T/dedup_filter.py $W/plan.tsv $W/e3.tsv $W/q/src $W/f3.tsv --no-import --jobs 2 > $W/f3.log || { cat $W/f3.log; fail "dedup_filter"; }
D=$W/f3.tsv.dropped.tsv
grep -q $'^NB.imp_m\talias\tIMPORT\tIMPORT$' $D || { cat $D; fail "IMPORT member kept"; }; ok
grep -q $'^NB.red_short\tredirect\tALIAS\tSHORT$' $D || { cat $D; fail "short-name redirect kept"; }; ok
grep -q $'^NB.al_named\talias\tALIAS\tNAMED$' $D || { cat $D; fail "named-arg alias kept"; }; ok
grep -q $'^NB.red_nosub\tredirect\tALIAS\tNOSUBST$' $D || { cat $D; fail "redirect without subst in a user kept"; }; ok
! grep -q 'insert_before' $W/f3.tsv || fail "added import kept"; ok
grep -q $'^Q.B\t3\t3\tdelete' $W/f3.tsv && grep -q $'^Q.C\t0\t0\tsubst\tP03-dedup\tNB.red_ok _root_.NA.tgt1' $W/f3.tsv || fail "clean redirect dropped"; ok
grep -q 'alias al_ok' $W/f3.tsv || fail "clean alias dropped"; ok
! grep -q 'red_short NA.tgt3' $W/f3.tsv && ! grep -q $'^Q.B\t4\t4\tdelete' $W/f3.tsv || fail "dropped member edits left"; ok
grep -q $'^NB.red_priv\tredirect\tALIAS\tSHORT$' $D || { cat $D; fail "private short-used redirect kept"; }; ok
! grep -q 'NB.red_priv NA.tgt4' $W/f3.tsv && ! grep -q $'^Q.B\t11\t11' $W/f3.tsv || fail "private member: subst/delete left (plan name != source name)"; ok
# --- 4. insert_guard: a docstring anchored in a deleted declaration is dropped, one before a kept one stays
printf 'Q.B\t3\t2\tinsert_before\tD18-docs\t/-- doc of red_ok -/\nQ.B\t6\t5\tinsert_before\tD18-docs\t/-- doc of al_named -/\n' > $W/docs.tsv
printf 'Q.B\t3\t3\tdelete\tP01\t\n' > $W/del.tsv
python3 -I $T/insert_guard.py $W/docs.tsv $W/docs.out $W/del.tsv > /dev/null || fail "insert_guard"
! grep -q 'doc of red_ok' $W/docs.out || fail "docstring anchored in deleted code kept"; ok
grep -q 'doc of al_named' $W/docs.out || fail "docstring of a kept declaration dropped"; ok
# --- 5. decl_exclude: an automation edit in a declaration that also has a DHE edit is dropped
printf '#module\tstart\tend\tkind\tlive\tdeleted\tnames\nQ.B\t3\t3\ttheorem\t1\t0\tNB.red_ok\nQ.B\t6\t6\ttheorem\t1\t0\tNB.al_named\n' > $W/decls.tsv
printf 'Q.B\t3\t3\treplace\tP06\ttheorem red_ok : True := by simp\nQ.B\t6\t6\treplace\tP06\ttheorem al_named (y : Nat) : y = y := by simp\n' > $W/auto.tsv
printf 'Q.B\t3\t3\treplace\tP05-dhe\ttheorem red_ok : True := trivial\n' > $W/dhe.tsv
python3 -I $T/decl_exclude.py $W/auto.tsv $W/dhe.tsv $W/decls.tsv $W/auto.out > /dev/null || fail "decl_exclude"
[ "$(wc -l < $W/auto.out)" = 1 ] && grep -q 'al_named' $W/auto.out || fail "decl_exclude kept/dropped the wrong edit"; ok
# --- 6. newlist_guard: a list joining after the prune rounds may not name a declaration they delete
mkdir -p $W/ng/src/Q
printf 'namespace NB\ntheorem keep1 : True := trivial\ntheorem gone : True := trivial\ntheorem keep2 : True := by\n  exact keep1\nend NB\n' > $W/ng/src/Q/N.lean
printf '#module\tstart\tend\tkind\tlive\tdeleted\tnames\nQ.N\t2\t2\ttheorem\t1\t0\tNB.keep1\nQ.N\t3\t3\ttheorem\t1\t0\tNB.gone\nQ.N\t4\t5\ttheorem\t1\t0\tNB.keep2\n' > $W/ng/decls.tsv
printf 'Q.N\t3\t3\tdelete\tP01\t\nQ.Gone\t0\t0\tdeletefile\tP01\t\n' > $W/ng/del.tsv
{ printf 'Q.N\t5\t5\treplace\tGS3\t  exact gone\n'; printf 'Q.N\t4\t4\treplace\tGS3\ttheorem keep2 : True := by\n'
  printf 'Q.N\t2\t2\treplace\tGS3\ttheorem keep1 : True := by trivial\n'; printf 'Q.N\t2\t1\tinsert_before\tGS3\t/-- unlike `gone` -/\n'
  printf 'Q.N\t1\t0\tinsert_before\tGS3\timport Q.Gone\n'; } > $W/ng/new.tsv
python3 -I $T/newlist_guard.py $W/ng/decls.tsv $W/ng/new.tsv $W/ng/out.tsv --deleted $W/ng/del.tsv --src $W/ng/src > /dev/null || fail "newlist_guard"
! grep -q 'exact gone' $W/ng/out.tsv || fail "edit naming a deleted declaration kept"; ok
! grep -q 'theorem keep2' $W/ng/out.tsv || fail "coupled edit of the same declaration kept"; ok
grep -q 'by trivial' $W/ng/out.tsv && grep -q 'unlike `gone`' $W/ng/out.tsv || fail "clean edit / docstring dropped"; ok
! grep -q 'import Q.Gone' $W/ng/out.tsv || fail "import of a deleted module kept"; ok
printf 'Q.N\t5\t5\treplace\tGS3\t  exact (keep1)\n' > $W/ng/new2.tsv
python3 -I $T/newlist_guard.py $W/ng/decls.tsv $W/ng/new2.tsv $W/ng/out2.tsv --deleted $W/ng/del.tsv --src $W/ng/src > /dev/null && [ "$(wc -l < $W/ng/out2.tsv)" = 1 ] || fail "token of the original declaration flagged"; ok
printf 'Q.N\t5\t5\treplace\tGS3\t  exact _root_.NB.gone\n' > $W/ng/new3.tsv
python3 -I $T/newlist_guard.py $W/ng/decls.tsv $W/ng/new3.tsv $W/ng/out3.tsv --deleted $W/ng/del.tsv --src $W/ng/src > /dev/null && [ ! -s $W/ng/out3.tsv ] || fail "_root_-qualified mention of a deleted declaration kept (D13 17:44Z)"; ok
# --- 7. dedup_delta: groups of a new dedup plan that are consistent with the base deletions
DD=$W/dd; mkdir -p $DD
printf '#module\tstart\tend\tkind\tlive\tdeleted\tnames\nM.A\t5\t6\ttheorem\t1\t0\tNS.dupA\nM.A\t8\t9\ttheorem\t1\t0\tNS.dupB\nM.B\t5\t6\ttheorem\t1\t0\tNS.dupC\nM.T\t2\t3\ttheorem\t1\t0\tNS.tgt\nM.T\t4\t5\ttheorem\t1\t0\tNS.tgtGone\nM.C\t3\t4\ttheorem\t1\t0\tNS.dupD\nM.U\t3\t4\ttheorem\t1\t0\tNS.user\n' > $DD/decls.tsv
printf 'M.X\t1\t1\tdelete\tP03-dedup\t\n' > $DD/base.tsv
printf 'M.T\t4\t5\tdelete\tP01\t\n' > $DD/p01.tsv
{ printf 'M.X\t1\t1\tdelete\tP03-dedup\t\n'
  printf 'M.A\t5\t6\treplace\tP03-dedup\talias dupA := _root_.NS.tgt\n'; printf 'M.A\t8\t9\treplace\tP03-dedup\talias dupB := _root_.NS.tgtGone\n'
  printf 'M.A\t2\t1\tinsert_before\tP03-dedup\timport M.T\n'
  printf 'M.B\t5\t6\treplace\tP03-dedup\talias dupC := _root_.NS.tgt\n'; printf 'M.B\t2\t1\tinsert_before\tP03-dedup\timport M.T\n'
  printf 'M.C\t3\t4\tdelete\tP03-dedup\t\n'; printf 'M.U\t0\t0\tsubst\tP03-dedup\tNS.dupD _root_.NS.tgt\n'; } > $DD/new.tsv
printf 'M.U\t3\t4\treplace\tP06\ttheorem user : True := by exact dupD\n' > $DD/texts.tsv
python3 -I $T/dedup_delta.py $DD/base.tsv $DD/new.tsv $DD/decls.tsv $DD/out.tsv --base $DD/p01.tsv --texts $DD/texts.tsv > $DD/log || { cat $DD/log; fail "dedup_delta"; }
grep -q 'alias dupC' $DD/out.tsv && grep -q $'^M.B\t2\t1\tinsert_before' $DD/out.tsv || fail "clean alias group with its import dropped"; ok
! grep -q 'alias dupB' $DD/out.tsv || fail "alias to a deleted target kept"; ok
! grep -q 'alias dupA' $DD/out.tsv && ! grep -q $'^M.A\t2\t1' $DD/out.tsv || fail "group coupled through a module import kept"; ok
! grep -q 'NS.dupD' $DD/out.tsv || fail "redirect of a duplicate still named by another list kept"; ok
! grep -q $'^M.X' $DD/out.tsv && [ "$(cut -f5 $DD/out.tsv | sort -u)" = P03-dedup-v2 ] || fail "base rows / owner key"; ok
echo "PASS ($n checks)"

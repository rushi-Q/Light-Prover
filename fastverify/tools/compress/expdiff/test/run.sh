#!/bin/bash
# Regression tests for expdiff: crafted exports with known differences / dead binders.
# usage: test/run.sh [EXPDIFF_BINARY]      (default: build with ../build.sh)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
X=${1:-}
if [ -z "$X" ]; then X=$("$HERE/../build.sh" | tail -1); fi
T=$(mktemp -d /tmp/expdiff-test.XXXXXX)
trap 'rm -rf "$T"' EXIT
python3 -I "$HERE/mkexport.py" old "$T/old.export"
python3 -I "$HERE/mkexport.py" new "$T/new.export"
fail=0
check() { # desc, pattern, file
  if grep -qP -- "$2" "$3"; then echo "PASS $1"; else echo "FAIL $1 (pattern: $2)"; fail=1; fi
}
TG="t1,t2,t3,t4,t5,t6,d1,N.t8,M.t8,t7,top"
"$X" diff -j 2 --targets t1,t2,t3,t4,t5,t6,d1,N.t8,top "$T/old.export" "$T/new.export" --tsv "$T/d.tsv" > "$T/d.out" 2>&1
# whole exports (no targets): rename and add are visible
"$X" diff -j 2 "$T/old.export" "$T/new.export" --tsv "$T/d2.tsv" > "$T/d2.out" 2>&1
# per-side target lists
"$X" diff -j 2 --targets t1,t2,N.t8 --targets-new t1,t2,M.t8,t7 "$T/old.export" "$T/new.export" --tsv "$T/d4.tsv" > "$T/d4.out" 2>&1
check "diff: identical t1/t6/d1 + axioms counted" '^status\tidentical\t' "$T/d.out"
check "diff: t2 alpha-equal" '^alpha-equal[^\t]*\tt2\t' "$T/d.tsv"
check "diff: t3 value-changed, statement equal" '^value-changed, statement equal\tt3\t' "$T/d.tsv"
check "diff: t4 STATEMENT-CHANGED" '^STATEMENT-CHANGED\tt4\t' "$T/d.tsv"
check "diff: t5 removed" '^removed\tt5\t' "$T/d.tsv"
check "diff: N.t8 renamed to M.t8" '^removed\tN\.t8\t.*\tM\.t8$' "$T/d2.tsv"
check "diff: t7 added" '^added\tt7\t' "$T/d2.tsv"
check "diff: renamed count 1" '^status\trenamed[^\t]*\t1$' "$T/d2.out"
check "diff --targets-new: rename across target lists" '^removed\tN\.t8\t.*\tM\.t8$' "$T/d4.tsv"
check "diff: RESULT says statements changed" '^RESULT\tstatements changed' "$T/d.out"
check "diff: statement_changed lists t4" '^statement_changed\tt4$' "$T/d.out"
check "diff: explain t4 points at the binder type" '^explain\tSTATEMENT-CHANGED\tt4\ttype\.type\told: Q\tnew: P' "$T/d.out"
check "diff: explain t2 binder name" '^explain\talpha-equal[^\t]*\tt2\ttype\told: \(∀ \(h : P\), P\)\tnew: \(∀ \(k : P\), P\)' "$T/d.out"
check "diff: explain t3 dead let" '^explain\tvalue-changed, statement equal\tt3\tvalue\told: \(let x : ' "$T/d.out"
"$X" diff -j 2 --dead-lets --targets t1,t2,t3,t4,t5,t6,d1,N.t8,top "$T/old.export" "$T/new.export" --tsv "$T/d5.tsv" > "$T/d5.out" 2>&1
check "diff --dead-lets: t3 equal modulo dead lets" '^value-equal modulo dead lets\tt3\t' "$T/d5.tsv"
check "diff --dead-lets: t3 yes, top (t4 q -> t4 p) no" '^dead_lets_check\t2 value-changed pairs, 1 equal modulo dead lets' "$T/d5.out"
"$X" diff -j 2 --targets t1,t6,d1 "$T/old.export" "$T/new.export" > "$T/d3.out" 2>&1
check "diff: unchanged closure -> no statement changed" '^RESULT\tno statement changed' "$T/d3.out"
check "diff: unchanged closure -> 0 added" '^status\tadded\t0$' "$T/d3.out"
"$X" dead -j 2 --tsv "$T/dead.tsv" "$T/old.export" > "$T/dead.out" 2>&1
check "dead: t3 dead let x" '^t3\tproject\tthm\tlet\tx\t' "$T/dead.tsv"
check "dead: t4 unused hypothesis h" '^t4\tproject\tthm\thyp\th\tdefault\t0\t' "$T/dead.tsv"
check "dead: t5 dead beta z" '^t5\tproject\tthm\tbeta\tz\t' "$T/dead.tsv"
if grep -qP '^t6\t' "$T/dead.tsv"; then echo "FAIL dead: t6 used beta reported"; fail=1; else echo "PASS dead: t6 (used beta) not reported"; fi
if grep -qP '^t2\t' "$T/dead.tsv"; then echo "FAIL dead: t2 used hyp reported"; fail=1; else echo "PASS dead: t2 (used hyp) not reported"; fi
"$X" stats -j 2 --targets top --tsv "$T/s.tsv" "$T/old.export" > "$T/s.out" 2>&1
check "stats: closure of top = top,t2,t4,P,Q,q,p (7)" '^stats\.closure_decls\t7$' "$T/s.out"
check "stats: identical content t1/t6? (t1 = p, t6 = beta) none in closure" '^identical_content_other_name\t0\t' "$T/s.out"
"$X" stats -j 2 --tsv "$T/s2.tsv" "$T/old.export" > "$T/s2.out" 2>&1
check "stats(all): same-statement theorem group (t1,t3,t5,t6,N.t8,top : P)" '^same_statement_thm_groups\t1\t\(members 6\)' "$T/s2.out"
check "stats(all): t2 indeg 2 (N.t8, top)" '^t2\tthm\tproject\tuser\t1\t[^\t]*\t[^\t]*\t[^\t]*\t[^\t]*\t[^\t]*\t[^\t]*\t[^\t]*\t2\t' "$T/s2.tsv"
python3 -I "$HERE/mkexport.py" privold "$T/po.export"; python3 -I "$HERE/mkexport.py" privnew "$T/pn.export"
"$X" diff -j 2 --targets q1 "$T/po.export" "$T/pn.export" > "$T/p1.out" 2>&1
check "private names renamed by a merge: without --private-modulo q1 changes" '^status\tvalue-changed, statement equal\t1$' "$T/p1.out"
"$X" diff -j 2 --private-modulo --targets q1,_private.Mod.B.0.p2 --targets-new q1,_private.Mod.M.0.p2 "$T/po.export" "$T/pn.export" > "$T/p2.out" 2>&1
check "--private-modulo: everything identical" '^status\tidentical\t5$' "$T/p2.out"
check "--private-modulo: nothing removed" '^status\tremoved\t0$|^RESULT\tno statement changed' "$T/p2.out"
"$X" show "$T/old.export" t3 > "$T/show.out" 2>&1
check "show: pretty-prints the let" 'value: \(let x : \(∀ \(y : Q\), Q\) := \(fun \(y : Q\) => y\); p\)' "$T/show.out"
if [ $fail = 0 ]; then echo "ALL PASS"; else echo "SOME FAILED"; fi
exit $fail

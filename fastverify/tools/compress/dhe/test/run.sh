#!/bin/bash
# dhe regression tests (core Lean only, no Mathlib): DeadLetCheck verdicts on crafted modules + dhe.py edit rules.
set -u
H=$(cd "$(dirname "$0")/.." && pwd)
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
T=$(mktemp -d /tmp/dhe-test.XXXXXX); trap 'rm -rf "$T"' EXIT
fail=0
ok() { echo "PASS $1"; }; ko() { echo "FAIL $1"; fail=1; }
mk() { printf '%s\n' "$2" > "$T/$1.lean"; ( cd "$T" && LEAN_PATH=$TC/lib/lean "$TC/bin/lean" "$1.lean" -o "$1.olean" > "$1.out" 2>&1 ) || { cat "$T/$1.out"; ko "compile $1"; }; }
mk A 'theorem t (n : Nat) : n + 0 = n := by
  have h : 1 = 1 := rfl
  have k : n = n := rfl
  simp
theorem u : True := trivial'
mk B 'theorem t (n : Nat) : n + 0 = n := by
  have k : n = n := rfl
  simp
theorem u : True := trivial'
mk C 'theorem t (n : Nat) : 0 + n = n := by
  simp
theorem u : True := trivial'
mk D 'theorem t (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
theorem u : True := trivial'
dlc() { LEAN_PATH=$TC/lib/lean "$TC/bin/lean" --run "$H/DeadLetCheck.lean" "$@"; }
dlc "$T/A.olean" "$T/B.olean" > "$T/ab.txt"; r=$?
grep -q "moddead t" "$T/ab.txt" && grep -q "different=0 onlyA=0 onlyB=0" "$T/ab.txt" && [ $r = 0 ] && ok "dead have removed -> moddead, exit 0" || { cat "$T/ab.txt"; ko "A vs B"; }
dlc "$T/A.olean" "$T/C.olean" > "$T/ac.txt"; r=$?
grep -q "different-statement t" "$T/ac.txt" && [ $r = 1 ] && ok "statement change -> different-statement, exit 1" || { cat "$T/ac.txt"; ko "A vs C"; }
dlc "$T/B.olean" "$T/D.olean" > "$T/bd.txt"; r=$?
grep -q "different-value t" "$T/bd.txt" && [ $r = 1 ] && ok "other proof -> different-value, exit 1" || { cat "$T/bd.txt"; ko "B vs D"; }
printf 'x %s %s\ny %s %s\n' "$T/A.olean" "$T/A.olean" "$T/A.olean" "$T/B.olean" > "$T/list"
dlc --list "$T/list" > "$T/l.txt"
grep -q "^x SUMMARY same=2 " "$T/l.txt" && grep -q "^y SUMMARY .*moddead=1" "$T/l.txt" && ok "batch mode" || { cat "$T/l.txt"; ko "batch"; }
# dhe.py rules on a fake source tree
mkdir -p "$T/src/M"
cat > "$T/src/M/X.lean" <<'L'
theorem a1 : True := by
  have h1 : 1 = 1 := rfl
  have h2 : 2 = 2 := by
    rfl
  set y := 3 with hy
  have h3 : 3 = 3 := rfl
  simp [h3]
  trivial
theorem a2 : True := by
  have h1 : 1 = 1 := rfl
  have h1 : 1 = 1 := rfl
  trivial
L
printf 'module\tname\tkw\tline\tlines\nM.X\ta1\ttheorem\t1\t8\nM.X\ta2\ttheorem\t9\t4\n' > "$T/decls.tsv"
printf 'decl\torigin\tdecl_kind\tdead_kind\tbinder\tbinder_info\tposition\tdead_value_dag\tdecl_value_dag\tnondep\n' > "$T/dead.tsv"
for b in h1 h2 hy h3; do printf 'a1\tproject\tthm\tlet\t%s\t-\t0\t1\t10\t0\n' $b >> "$T/dead.tsv"; done
printf 'a2\tproject\tthm\tlet\th1\t-\t0\t1\t10\t0\n' >> "$T/dead.tsv"
python3 -I "$H/dhe.py" "$T/dead.tsv" "$T/decls.tsv" "$T/src" "$T/edits.tsv" > "$T/dhe.json"
grep -qP '^M\.X\t2\t2\tdelete\tP05-dhe\t$' "$T/edits.tsv" && ok "dhe: one-line have deleted" || { cat "$T/edits.tsv"; ko "h1"; }
grep -qP '^M\.X\t3\t4\tdelete\tP05-dhe\t$' "$T/edits.tsv" && ok "dhe: multi-line have block deleted" || ko "h2"
grep -qP '^M\.X\t5\t5\treplace\tP05-dhe\t  set y := 3$' "$T/edits.tsv" && ok "dhe: set ... with hy -> set" || ko "hy"
grep -qP '^M\.X\t6\t' "$T/edits.tsv" && ko "dhe: h3 mentioned in simp [h3] must be kept" || ok "dhe: mentioned name kept"
grep -qP '^M\.X\t1[01]\t' "$T/edits.tsv" && ko "dhe: ambiguous a2.h1 must be kept" || ok "dhe: ambiguous have kept"
# v6 order matching: a3 has two `have h` lines; kernel order says the FIRST is dead (shadowed before any use)
cat > "$T/src/M/Y.lean" <<'L'
theorem a3 : True := by
  have h : 1 = 1 := rfl
  have h : 2 = 2 := rfl
  exact (fun _ => trivial) h
L
printf 'module\tname\tkw\tline\tlines\nM.Y\ta3\ttheorem\t1\t4\n' > "$T/decls2.tsv"
printf 'decl\torigin\tdecl_kind\tdead_kind\tbinder\tbinder_info\tposition\tdead_value_dag\tdecl_value_dag\tnondep\na3\tproject\tthm\tlet\th\t-\t0\t1\t10\t0\n' > "$T/dead2.tsv"
printf 'decl\tordinal\tbinder\tdead\na3\t0\th\t1\na3\t1\th\t0\n' > "$T/lets2.tsv"
python3 -I "$H/dhe.py" "$T/dead2.tsv" "$T/decls2.tsv" "$T/src" "$T/edits2.tsv" > /dev/null
[ -s "$T/edits2.tsv" ] && ko "dhe: without --lets the ambiguous name must be kept" || ok "dhe: ambiguous kept without --lets"
python3 -I "$H/dhe.py" "$T/dead2.tsv" "$T/decls2.tsv" "$T/src" "$T/edits3.tsv" --lets "$T/lets2.tsv" > /dev/null
grep -qP '^M\.Y\t2\t2\tdelete\tP05-dhe\t$' "$T/edits3.tsv" && [ $(wc -l < "$T/edits3.tsv") = 1 ] && ok "dhe --lets: first (dead) have h deleted by position" || { cat "$T/edits3.tsv"; ko "order"; }
python3 -I "$H/apply_inplace.py" "$T/src" "$T/edits.tsv" > /dev/null
printf 'theorem a1 : True := by\n  set y := 3\n  have h3 : 3 = 3 := rfl\n  simp [h3]\n  trivial\n' > "$T/expect_a1"
head -5 "$T/src/M/X.lean" | cmp -s - "$T/expect_a1" && ok "apply_inplace: edited text as expected" || { head -6 "$T/src/M/X.lean"; ko "apply_inplace"; }
[ $fail = 0 ] && echo "ALL PASS" || echo "SOME FAILED"; exit $fail

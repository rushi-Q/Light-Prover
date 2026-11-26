#!/bin/bash
# Regression test for tools/compress/defdedup/defdedup_guard.py (stage-3 guards P5 & P7):
#   1. Cross-module `rw [cT, h1]` importer break (C4 v2 PsiScal.cT class) -> dropped by RW_UNFOLD
#   2. Cross-module `open DdB hiding hiddenDef` importer break (RkVolSeam class) -> dropped by OPEN_CLAUSE_REF
#   3. Binder-info mismatch (`{n}` vs `(n)`) -> dropped by BINFO_MISMATCH
#   4. Clean `safeAbbrev` & `safeDef` -> KEPT, edited cleanly, and 3/3 modules build in bwrap Lean 4.33.1!
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
T=${DEFDEDUP_DIR:-$(cd "$HERE/.." && pwd)}
DEDUP=${DEDUP_DIR:-$(cd "$T/../dedup" && pwd)}
GUARD=${DEFDEDUP_GUARD:-$T/defdedup_guard.py}
W=$(mktemp -d /tmp/d13-defdedup-p5.XXXXXX); trap 'rm -rf "$W"' EXIT

mkdir -p "$W/proj/Dd" "$W/scan"
cat > "$W/proj/lean-toolchain" <<'EOF'
leanprover/lean4:v4.33.1
EOF
cat > "$W/proj/lakefile.toml" <<'EOF'
name = "ddp5"
defaultTargets = ["Dd"]
[[lean_lib]]
name = "Dd"
EOF
cat > "$W/proj/Dd.lean" <<'EOF'
import Dd.A
import Dd.B
import Dd.C
EOF
cat > "$W/proj/Dd/A.lean" <<'EOF'
namespace DdA
abbrev cT (n : Nat) : Nat := n + 1
abbrev MyTy := Nat
def addOne (n : Nat) : Nat := n + 1
def addTwo (n : Nat) : Nat := n + 2
def addThree {n : Nat} : Nat := n + 3
end DdA
EOF
cat > "$W/proj/Dd/B.lean" <<'EOF'
import Dd.A
namespace DdB
abbrev cT (n : Nat) : Nat := n + 1
abbrev safeAbbrev := Nat
def okTy : safeAbbrev := 0
def hiddenDef (n : Nat) : Nat := n + 1
def safeDef (n : Nat) : Nat := n + 2
def badBinfo (n : Nat) : Nat := n + 3
theorem useSafe (n : Nat) : safeDef n = n + 2 := rfl
theorem useBinfo (n : Nat) : badBinfo n = n + 3 := rfl
end DdB
EOF
cat > "$W/proj/Dd/C.lean" <<'EOF'
import Dd.B
open DdB hiding hiddenDef
theorem use_cT (n m : Nat) (h1 : n + 1 = m) : cT n = m := by
  rw [cT, h1]
theorem use_safe : DdB.okTy = 0 := rfl
EOF
cat > "$W/comparator.json" <<'EOF'
{"theorem_names": ["use_cT", "use_safe"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
EOF
cat > "$W/decls.tsv" <<'EOF'
idx	name	kind	lvl_h	type_hk	type_hs	value_hk	extra	new_nodes	new_bytes	value_tsize
1	DdA.cT	def	L0	T_FN	T_FN	V_ADD1	"abbrev" safe	1	10	1
2	DdA.MyTy	def	L0	T_TY	T_TY	V_NAT	"abbrev" safe	1	10	1
3	DdA.addOne	def	L0	T_FN	T_FN	V_ADD1	{"regular":1} safe	1	10	1
4	DdA.addTwo	def	L0	T_FN	T_FN	V_ADD2	{"regular":1} safe	1	10	1
5	DdA.addThree	def	L0	T_FN	T_FN	V_ADD3	{"regular":1} safe	1	10	1
6	DdB.cT	def	L0	T_FN	T_FN	V_ADD1	"abbrev" safe	1	10	1
7	DdB.safeAbbrev	def	L0	T_TY	T_TY	V_NAT	"abbrev" safe	1	10	1
8	DdB.hiddenDef	def	L0	T_FN	T_FN	V_ADD1	{"regular":1} safe	1	10	1
9	DdB.safeDef	def	L0	T_FN	T_FN	V_ADD2	{"regular":1} safe	1	10	1
10	DdB.badBinfo	def	L0	T_FN	T_FN	V_ADD3	{"regular":1} safe	1	10	1
EOF
cat > "$W/srcmap.tsv" <<'EOF'
name	module	kw	start	end	nlines	cols
DdA.cT	Dd.A	abbrev	2	2	1	1
DdA.MyTy	Dd.A	abbrev	3	3	1	1
DdA.addOne	Dd.A	def	4	4	1	1
DdA.addTwo	Dd.A	def	5	5	1	1
DdA.addThree	Dd.A	def	6	6	1	1
DdB.cT	Dd.B	abbrev	3	3	1	1
DdB.safeAbbrev	Dd.B	abbrev	4	4	1	1
DdB.hiddenDef	Dd.B	def	6	6	1	1
DdB.safeDef	Dd.B	def	7	7	1	1
DdB.badBinfo	Dd.B	def	8	8	1	1
EOF
cat > "$W/scan/c0.tsv" <<'EOF'
K	Dd.A	d	DdA.cT	0	0	0	0	2	2		Nat	d
K	Dd.A	d	DdA.MyTy	0	0	0	0	3	3		Nat	
K	Dd.A	d	DdA.addOne	0	0	0	0	4	4		Nat	d
K	Dd.A	d	DdA.addTwo	0	0	0	0	5	5		Nat	d
K	Dd.A	d	DdA.addThree	0	0	0	0	6	6		Nat	i
K	Dd.B	d	DdB.cT	0	0	0	0	3	3		Nat	d
K	Dd.B	d	DdB.safeAbbrev	0	0	0	0	4	4		Nat	
K	Dd.B	d	DdB.hiddenDef	0	0	0	0	6	6		Nat	d
K	Dd.B	d	DdB.safeDef	0	0	0	0	7	7		Nat	d
K	Dd.B	d	DdB.badBinfo	0	0	0	0	8	8		Nat	d
K	Dd.C	t	use_cT	0	0	0	0	3	4	DdB.cT	Nat	dd
EOF

python3 -I "$DEDUP/imports.py" "$W/proj" "$W/imports.json" >/dev/null
python3 -I "$T/defdedup_plan.py" "$W/decls.tsv" "$W/srcmap.tsv" "$W/imports.json" "$W/proj" "$W/plan" \
  --protect-from "$W/comparator.json" >/dev/null
python3 -I "$T/defdedup_edits.py" "$W/plan/defplan.tsv" "$W/proj" "$W/edits_raw.tsv" \
  --mode hybrid --actions VISIBLE,IMPORT_CP --protect-from "$W/comparator.json" >/dev/null

python3 -I "$DEDUP/apply_edits.py" "$W/proj" "$W/out_raw" "$W/edits_raw.tsv" --srcdir . --copy >/dev/null
if "$DEDUP/sandbox_ro.sh" "$W/out_raw" "$W/out_raw" -- bash -c "cd '$W/out_raw' && lake build" > "$W/raw.log" 2>&1; then
  echo "FAIL: unguarded hybrid unexpectedly built"; exit 1
fi

python3 -I "$GUARD" "$W/plan/defplan.tsv" "$W/edits_raw.tsv" "$W/proj" "$W/scan" "$W/imports.json" "$W/edits_guarded.tsv" \
  --protect-from "$W/comparator.json" --jobs 4 >/dev/null
grep -q $'DdB.cT\tRW_UNFOLD' "$W/edits_guarded.tsv.dropped.tsv" || { cat "$W/edits_guarded.tsv.dropped.tsv"; echo "FAIL: DdB.cT not dropped by RW_UNFOLD"; exit 1; }
grep -q $'DdB.hiddenDef\tOPEN_CLAUSE_REF' "$W/edits_guarded.tsv.dropped.tsv" || { cat "$W/edits_guarded.tsv.dropped.tsv"; echo "FAIL: DdB.hiddenDef not dropped by OPEN_CLAUSE_REF"; exit 1; }
grep -q $'DdB.badBinfo\tBINFO_MISMATCH' "$W/edits_guarded.tsv.dropped.tsv" || { cat "$W/edits_guarded.tsv.dropped.tsv"; echo "FAIL: DdB.badBinfo not dropped by BINFO_MISMATCH"; exit 1; }

python3 -I "$DEDUP/apply_edits.py" "$W/proj" "$W/out_guarded" "$W/edits_guarded.tsv" --srcdir . --copy >/dev/null
"$DEDUP/sandbox_ro.sh" "$W/out_guarded" "$W/out_guarded" -- bash -c "cd '$W/out_guarded' && lake build" > "$W/guarded.log" 2>&1 || { cat "$W/guarded.log"; echo "FAIL: guarded hybrid failed to build"; exit 1; }
grep -q 'abbrev safeAbbrev := @_root_.DdA.MyTy' "$W/out_guarded/Dd/B.lean" || { echo "FAIL: safeAbbrev not aliased"; exit 1; }
grep -q '_root_.DdA.addTwo' "$W/out_guarded/Dd/B.lean" || { echo "FAIL: safeDef not redirected"; exit 1; }
grep -q 'abbrev cT (n : Nat) : Nat := n + 1' "$W/out_guarded/Dd/B.lean" || { echo "FAIL: cT was not preserved"; exit 1; }
grep -q 'def hiddenDef (n : Nat) : Nat := n + 1' "$W/out_guarded/Dd/B.lean" || { echo "FAIL: hiddenDef was not preserved"; exit 1; }

echo "PASS (defdedup_guard P5: RW_UNFOLD + OPEN_CLAUSE_REF + BINFO_MISMATCH all caught, safeAbbrev+safeDef kept, 3/3 build OK)"

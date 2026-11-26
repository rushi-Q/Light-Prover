#!/bin/bash
# Regression test for tools/compress/defdedup:
# Builds a 2-module core-Lean 4.33.1 project in bwrap with:
#  - duplicate abbrev (A.MyTy and B.DupTy, used via reducibility)
#  - duplicate def (A.addOne and B.plusOne, used via `rw [plusOne]`)
#  - protected challenge def (B.chalDef, listed in comparator.json -> MUST NOT be touched)
# Verifies:
#  1. `def` mode breaks reducibility on DupTy;
#  2. `matchkw` mode breaks `rw [plusOne]` (unfolds to addOne instead of n + 1);
#  3. `hybrid` mode (abbrev -> alias, def -> redirect) BUILDS CLEANLY in Lean 4.33.1 and preserves chalDef!
set -euo pipefail
T=$(cd "$(dirname "$0")/.." && pwd)
DEDUP=$(cd "$T/../dedup" && pwd)
TC=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1
W=$(mktemp -d /tmp/defdedup-test.XXXXXX); trap 'rm -rf "$W"' EXIT

mkdir -p "$W/proj/Dd"
cat > "$W/proj/lean-toolchain" <<'EOF'
leanprover/lean4:v4.33.1
EOF
cat > "$W/proj/lakefile.toml" <<'EOF'
name = "ddtest"
defaultTargets = ["Dd"]
[[lean_lib]]
name = "Dd"
EOF
cat > "$W/proj/Dd.lean" <<'EOF'
import Dd.A
import Dd.B
EOF
cat > "$W/proj/Dd/A.lean" <<'EOF'
namespace DdA
abbrev MyTy := Nat
def addOne (n : Nat) : Nat := n + 1
end DdA
EOF
cat > "$W/proj/Dd/B.lean" <<'EOF'
import Dd.A
namespace DdB
class MyTag (α : Type) where
instance : MyTag Nat where
abbrev DupTy := Nat
def useTy : MyTag DupTy := inferInstance
def plusOne (n : Nat) : Nat := n + 1
theorem useRw (n : Nat) : plusOne n = n + 1 := by rw [plusOne]
def chalDef (n : Nat) : Nat := n + 1
end DdB
EOF
cat > "$W/comparator.json" <<'EOF'
{"theorem_names": ["DdB.useRw"], "definition_names": ["DdB.chalDef"], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
EOF

# Synthetic decls.tsv, srcmap.tsv, imports.json matching the 2-module fixture
cat > "$W/decls.tsv" <<'EOF'
idx	name	kind	lvl_h	type_hk	type_hs	value_hk	extra	new_nodes	new_bytes	value_tsize
1	DdA.MyTy	def	L0	T_TY	T_TY	V_NAT	"abbrev" safe	1	10	1
2	DdA.addOne	def	L0	T_FN	T_FN	V_ADD1	{"regular":1} safe	1	10	1
3	DdB.DupTy	def	L0	T_TY	T_TY	V_NAT	"abbrev" safe	1	10	1
4	DdB.plusOne	def	L0	T_FN	T_FN	V_ADD1	{"regular":1} safe	1	10	1
5	DdB.chalDef	def	L0	T_FN	T_FN	V_ADD1	{"regular":1} safe	1	10	1
EOF
cat > "$W/srcmap.tsv" <<'EOF'
name	module	kw	start	end	nlines	cols
DdA.MyTy	Dd.A	abbrev	2	2	1	1
DdA.addOne	Dd.A	def	3	3	1	1
DdB.DupTy	Dd.B	abbrev	5	5	1	1
DdB.plusOne	Dd.B	def	7	7	1	1
DdB.chalDef	Dd.B	def	9	9	1	1
EOF
python3 "$DEDUP/imports.py" "$W/proj" "$W/imports.json" >/dev/null

# Plan
python3 "$T/defdedup_plan.py" "$W/decls.tsv" "$W/srcmap.tsv" "$W/imports.json" "$W/proj" "$W/plan" \
  --protect-from "$W/comparator.json" >/dev/null
grep -q $'KEEP_PROT\tDdB.chalDef' "$W/plan/defplan.tsv" || { echo "FAIL: chalDef not protected"; exit 1; }

build_mode() {
  local mode=$1
  python3 "$T/defdedup_edits.py" "$W/plan/defplan.tsv" "$W/proj" "$W/edits_$mode.tsv" \
    --mode "$mode" --actions VISIBLE,IMPORT_CP --protect-from "$W/comparator.json" >/dev/null
  python3 "$DEDUP/apply_edits.py" "$W/proj" "$W/out_$mode" "$W/edits_$mode.tsv" --srcdir . --copy >/dev/null
  "$DEDUP/sandbox_ro.sh" "$W/out_$mode" "$W/out_$mode" -- bash -c "cd '$W/out_$mode' && lake build" > "$W/build_$mode.log" 2>&1
}

# 1. `def` mode should FAIL with failed to synthesize (DupTy becomes semireducible def -> MyTag DupTy fails!)
if build_mode def; then echo "FAIL: def mode unexpectedly built"; exit 1; fi
grep -q 'failed to synthesize' "$W/build_def.log" || { cat "$W/build_def.log"; echo "FAIL: def mode failed for wrong reason"; exit 1; }
# 2. `matchkw` mode should FAIL on rw/unfold (`rw [plusOne]` unfolds plusOne to _root_.DdA.addOne, leaving unsolved goal)
if build_mode matchkw; then echo "FAIL: matchkw mode unexpectedly built"; exit 1; fi
grep -qE 'unsolved goals|did not find instance|tactic .* failed' "$W/build_matchkw.log" || { cat "$W/build_matchkw.log"; echo "FAIL: matchkw mode failed for wrong reason"; exit 1; }
# 3. `hybrid` mode should SUCCEED (`abbrev DupTy := @_root_.DdA.MyTy` + redirect `plusOne -> _root_.DdA.addOne`)
if ! build_mode hybrid; then cat "$W/build_hybrid.log"; echo "FAIL: hybrid mode failed to build"; exit 1; fi
grep -q 'abbrev DupTy := @_root_.DdA.MyTy' "$W/out_hybrid/Dd/B.lean" || { echo "FAIL: DupTy not aliased"; exit 1; }
grep -q 'rw \[_root_.DdA.addOne\]' "$W/out_hybrid/Dd/B.lean" || { echo "FAIL: plusOne not redirected"; exit 1; }
grep -q 'def chalDef (n : Nat) : Nat := n + 1' "$W/out_hybrid/Dd/B.lean" || { echo "FAIL: chalDef modified"; exit 1; }

echo "PASS (defdedup: def-mode reducibility fail confirmed, matchkw rw-unfold fail confirmed, hybrid PASS, chalDef protected)"

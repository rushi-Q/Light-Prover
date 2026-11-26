#!/bin/bash
# Regression test for tools/compress/scheme/dedup_filter_v2.py (Stage-3 DEDUP.c1r_v2 guards):
# Verifies in a real Lean 4.33.1 bwrap project:
#   1. OPEN_CLAUSE_REF (`open ND hiding hidden_redir`) -> redirect dropped
#   2. TRANSITIVE AMBIGUOUS_IMPORT (`M.TgtAmbig` -> `M.AmbigLeaf` defines `NS2.relab` colliding with `NS1.relab`) -> dropped + orphan import pruned
#   3. TRANSITIVE ALREADY_DECLARED_IMPORT (`M.TgtDup` -> `M.DupLeaf` defines `DupNS.clash`) -> dropped + orphan import pruned
#   4. Auto-generated `.eq_1` across 2 modules does NOT trigger ALREADY_DECLARED_IMPORT false positive
#   5. Clean IMPORT redirect + clean IMPORT alias KEPT, subst targets `_root_.`-rooted, and `lake build` PASSES!
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
FILT=${DEDUP_FILTER_V2:-$(cd "$HERE/.." && pwd)/dedup_filter_v2.py}
DEDUP=${DEDUP_DIR:-$(cd "$HERE/../.." && pwd)/dedup}
W=$(mktemp -d /tmp/d13-dedup-v2-reg.XXXXXX); trap 'rm -rf "$W"' EXIT

mkdir -p "$W/proj/M" "$W/scan"
cat > "$W/proj/lean-toolchain" <<'EOF'
leanprover/lean4:v4.33.1
EOF
cat > "$W/proj/lakefile.toml" <<'EOF'
name = "df2"
defaultTargets = ["M"]
[[lean_lib]]
name = "M"
EOF
cat > "$W/proj/M.lean" <<'EOF'
import M.TgtClean
import M.TgtAmbig
import M.AmbigLeaf
import M.DupLeaf
import M.TgtDup
import M.Dups
import M.User
EOF
cat > "$W/proj/M/TgtClean.lean" <<'EOF'
namespace NT
theorem tgt_redir : True := trivial
theorem tgt_alias : True := trivial
end NT
EOF
cat > "$W/proj/M/AmbigLeaf.lean" <<'EOF'
namespace NS2
def relab : Nat := 2
def own_clash : Nat := 9
end NS2
EOF
cat > "$W/proj/M/TgtAmbig.lean" <<'EOF'
import M.AmbigLeaf
namespace NT
theorem tgt_ambig : True := trivial
theorem tgt_own : True := trivial
end NT
EOF
cat > "$W/proj/M/DupLeaf.lean" <<'EOF'
namespace DupNS
theorem clash : True := trivial
end DupNS
EOF
cat > "$W/proj/M/TgtDup.lean" <<'EOF'
import M.DupLeaf
namespace NT
theorem tgt_dup : True := trivial
end NT
EOF
cat > "$W/proj/M/Dups.lean" <<'EOF'
namespace NS1
def relab : Nat := 1
end NS1
namespace NS2
def other : Nat := 0
end NS2
namespace ND
theorem clean_redir : True := by
  have h : True := trivial
  exact h
theorem clean_alias : True := by
  have h : True := trivial
  exact h
theorem hidden_redir : True := by
  have h : True := trivial
  exact h
theorem ambig_alias : True := by
  have h : True := trivial
  exact h
theorem dup_alias : True := by
  have h : True := trivial
  exact h
theorem exported_redir : True := by
  have h : True := trivial
  exact h
theorem own_ambig_alias : True := by
  have h : True := trivial
  exact h
end ND
EOF
cat > "$W/proj/M/User.lean" <<'EOF'
import M.Dups
open NS1 NS2
open ND hiding hidden_redir
export ND (exported_redir)
namespace DupNS
theorem clash : True := trivial
end DupNS
private def own_clash : Nat := 1
theorem u1 : True := ND.clean_redir
def u2 : Nat := relab + own_clash
theorem u3 : True := ND.ambig_alias
theorem u4 : True := ND.dup_alias
theorem u5 : True := ND.own_ambig_alias
EOF

cat > "$W/comparator.json" <<'EOF'
{"theorem_names": ["u1", "u3", "u4", "u5"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
EOF
python3 -I "$DEDUP/imports.py" "$W/proj" "$W/imports.json" >/dev/null

cat > "$W/scan/c0.tsv" <<'EOF'
K	M.TgtClean	t	NT.tgt_redir	0	0	0	0	2	2		True	
K	M.TgtClean	t	NT.tgt_alias	0	0	0	0	3	3		True	
K	M.TgtClean	t	SharedAuto.f.eq_1	0	0	0	0	0	0		True	
K	M.Dups	t	SharedAuto.f.eq_1	0	0	0	0	0	0		True	
K	M.Dups	d	NS1.relab	0	0	0	0	2	2		Nat	
K	M.AmbigLeaf	d	NS2.relab	0	0	0	0	2	2		Nat	
K	M.AmbigLeaf	d	NS2.own_clash	0	0	0	0	3	3		Nat	
K	M.DupLeaf	t	DupNS.clash	0	0	0	0	2	2		True	
K	M.User	t	DupNS.clash	0	0	0	0	5	5		True	
K	M.TgtAmbig	t	NT.tgt_ambig	0	0	0	0	3	3		True	
K	M.TgtAmbig	t	NT.tgt_own	0	0	0	0	4	4		True	
K	M.TgtDup	t	NT.tgt_dup	0	0	0	0	3	3		True	
EOF

cat > "$W/plan.tsv" <<'EOF'
group	action	name	module	target	target_module	stmt_lines	proof_lines	in_closure	indegree	private	line1	line2
1	IMPORT	ND.clean_redir	M.Dups	NT.tgt_redir	M.TgtClean	1	3	1	1	0	8	10
2	IMPORT	ND.clean_alias	M.Dups	NT.tgt_alias	M.TgtClean	1	3	1	0	0	11	13
3	IMPORT	ND.hidden_redir	M.Dups	NT.tgt_redir	M.TgtClean	1	3	1	0	0	14	16
4	IMPORT	ND.ambig_alias	M.Dups	NT.tgt_ambig	M.TgtAmbig	1	3	1	1	0	17	19
5	IMPORT	ND.dup_alias	M.Dups	NT.tgt_dup	M.TgtDup	1	3	1	1	0	20	22
6	IMPORT	ND.exported_redir	M.Dups	NT.tgt_redir	M.TgtClean	1	3	1	0	0	23	25
7	IMPORT	ND.own_ambig_alias	M.Dups	NT.tgt_own	M.TgtAmbig	1	3	1	1	0	26	28
EOF

cat > "$W/edits_raw.tsv" <<'EOF'
M.Dups	8	10	delete	P03-dedup	
M.Dups	8	10	subst	P03-dedup	ND.clean_redir NT.tgt_redir
M.User	0	0	subst	P03-dedup	ND.clean_redir NT.tgt_redir
M.User	2	1	insert_before	P03-dedup	import M.TgtClean
M.Dups	11	13	replace	P03-dedup	theorem clean_alias : True := _root_.NT.tgt_alias
M.Dups	14	16	delete	P03-dedup	
M.Dups	14	16	subst	P03-dedup	ND.hidden_redir NT.tgt_redir
M.Dups	17	19	replace	P03-dedup	theorem ambig_alias : True := _root_.NT.tgt_ambig
M.Dups	20	22	replace	P03-dedup	theorem dup_alias : True := _root_.NT.tgt_dup
M.Dups	23	25	delete	P03-dedup	
M.Dups	23	25	subst	P03-dedup	ND.exported_redir NT.tgt_redir
M.Dups	26	28	replace	P03-dedup	theorem own_ambig_alias : True := _root_.NT.tgt_own
M.Dups	1	0	insert_before	P03-dedup	import M.TgtClean\nimport M.TgtAmbig\nimport M.TgtDup
EOF

python3 -I "$FILT" "$W/plan.tsv" "$W/edits_raw.tsv" "$W/proj" "$W/scan" "$W/imports.json" "$W/edits_out.tsv" \
  --protect-from "$W/comparator.json" --jobs 2 > "$W/filt.log"

D="$W/edits_out.tsv.dropped.tsv"
grep -q $'^ND.hidden_redir\tredirect\tIMPORT\tOPEN_CLAUSE_REF$' "$D" || { cat "$D"; echo "FAIL: OPEN_CLAUSE_REF"; exit 1; }
grep -q $'^ND.exported_redir\tredirect\tIMPORT\tOPEN_CLAUSE_REF$' "$D" || { cat "$D"; echo "FAIL: export OPEN_CLAUSE_REF"; exit 1; }
grep -q $'^ND.ambig_alias\talias\tIMPORT\tAMBIGUOUS_IMPORT$' "$D" || { cat "$D"; echo "FAIL: transitive AMBIGUOUS_IMPORT"; exit 1; }
grep -q $'^ND.own_ambig_alias\talias\tIMPORT\tAMBIGUOUS_IMPORT$' "$D" || { cat "$D"; echo "FAIL: own_decl_shorts AMBIGUOUS_IMPORT"; exit 1; }
grep -q $'^ND.dup_alias\talias\tIMPORT\tALREADY_DECLARED_IMPORT$' "$D" || { cat "$D"; echo "FAIL: transitive ALREADY_DECLARED_IMPORT"; exit 1; }
grep -q $'^M.Dups\t8\t10\tdelete' "$W/edits_out.tsv" || { cat "$W/edits_out.tsv"; echo "FAIL: clean_redir dropped"; exit 1; }
grep -q $'^M.Dups\t11\t13\treplace' "$W/edits_out.tsv" || { cat "$W/edits_out.tsv"; echo "FAIL: clean_alias dropped"; exit 1; }
if grep -qE 'import M\.TgtAmbig|import M\.TgtDup' "$W/edits_out.tsv"; then
  cat "$W/edits_out.tsv"; echo "FAIL: orphan imports not pruned"; exit 1
fi
python3 -I "$DEDUP/apply_edits.py" "$W/proj" "$W/out" "$W/edits_out.tsv" --srcdir . --copy >/dev/null
"$DEDUP/sandbox_ro.sh" "$W/out" "$W/out" -- bash -c "cd '$W/out' && lake build" > "$W/build.log" 2>&1 || { cat "$W/build.log"; echo "FAIL: filtered tree failed lake build"; exit 1; }
grep -q '_root_.NT.tgt_redir' "$W/out/M/User.lean" || { echo "FAIL: subst target not rooted"; exit 1; }

echo "PASS (dedup_filter_v2: open/export OPEN_CLAUSE_REF + transitive/own-decl AMBIGUOUS_IMPORT + transitive ALREADY_DECLARED_IMPORT + auto-eq_1 non-FP + orphan import pruning + Lean 4.33.1 build OK)"

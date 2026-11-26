#!/bin/bash
# Unit test for autoshorten/filter_collisions.py:
# Verifies that when two sibling modules declare the same theorem full name `NS.dupThm`
# and both receive `grind` edits, filter_collisions.py keeps the higher-gain module's edit
# and drops the other, while preserving non-grind edits and unique-named grind edits.
set -euo pipefail
T=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d /tmp/filter-coll-test.XXXXXX); trap 'rm -rf "$W"' EXIT

mkdir -p "$W/src/Pkg"
cat > "$W/src/Pkg/A.lean" <<'EOF'
namespace NS
theorem dupThm : True := by
  have h1 : True := trivial
  have h2 : True := trivial
  exact h2
theorem uniqA : True := by
  have h : True := trivial
  exact h
end NS
EOF
cat > "$W/src/Pkg/B.lean" <<'EOF'
namespace NS
theorem dupThm : True := by
  have h : True := trivial
  exact h
theorem dupSimp : True := by
  have h : True := trivial
  exact h
end NS
EOF
cat > "$W/src/Pkg/C.lean" <<'EOF'
namespace NS
theorem dupSimp : True := by
  have h : True := trivial
  exact h
end NS
EOF

# A.dupThm saves 2 lines (3->1), B.dupThm saves 1 line (2->1) -> A kept, B dropped!
# A.uniqA is unique -> kept! B.dupSimp & C.dupSimp use simp (not grind) -> both kept!
cat > "$W/edits_in.tsv" <<'EOF'
Pkg.A	3	5	replace	P06	  grind
Pkg.A	7	8	replace	P06	  grind
Pkg.B	3	4	replace	P06	  grind
Pkg.B	6	7	replace	P06	  simp
Pkg.C	3	4	replace	P06	  simp
EOF

python3 "$T/filter_collisions.py" "$W/edits_in.tsv" "$W/edits_out.tsv" \
  --src-root "$W/src" --report "$W/rep.json"

[ "$(wc -l < "$W/edits_out.tsv")" -eq 4 ] || { echo "FAIL: expected 4 kept edits"; cat "$W/edits_out.tsv"; exit 1; }
grep -q $'^Pkg.A\t3\t5\t' "$W/edits_out.tsv" || { echo "FAIL: higher-gain Pkg.A dupThm dropped"; exit 1; }
if grep -q $'^Pkg.B\t3\t4\t' "$W/edits_out.tsv"; then echo "FAIL: colliding Pkg.B dupThm not dropped"; exit 1; fi
grep -q $'^Pkg.B\t6\t7\t' "$W/edits_out.tsv" || { echo "FAIL: non-grind dupSimp dropped"; exit 1; }
python3 -c "import json; r=json.load(open('$W/rep.json')); assert r['kept_edits']==4 and r['dropped_collisions']==1, r"
echo "PASS (filter_collisions: colliding sibling grind edit dropped, higher-gain winner & non-grind/unique edits preserved)"

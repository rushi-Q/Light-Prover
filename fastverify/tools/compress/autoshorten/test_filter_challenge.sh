#!/bin/bash
# Unit test for autoshorten/filter_challenge.py:
# Verifies both NDJSON lean4export v3.1.0 and comparator.json statement-closure filtering,
# auxiliary `_proof_*` base matching, headerless apply_edits.tsv format, and --exclude-modules.
set -euo pipefail
T=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d /tmp/filter-chal-test.XXXXXX); trap 'rm -rf "$W"' EXIT

mkdir -p "$W/src/Pkg"
cat > "$W/src/Pkg/A.lean" <<'EOF'
namespace Foo
public theorem pinnedThm : True := by
  trivial
theorem targetThm : True := by
  trivial
theorem freeThm : True := by
  trivial
end Foo
EOF
cat > "$W/src/Pkg/B.lean" <<'EOF'
theorem collideThm : True := by
  trivial
EOF

# Synthetic NDJSON challenge.export containing Foo.pinnedThm._proof_1 and targetThm (axiom in challenge)
cat > "$W/challenge.export" <<'EOF'
{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"Foo"}}
{"in":2,"str":{"pre":1,"str":"pinnedThm"}}
{"in":3,"str":{"pre":2,"str":"_proof_1"}}
{"in":4,"str":{"pre":1,"str":"targetThm"}}
{"thm":{"name":3,"levelParams":[],"type":0,"value":0}}
{"axiom":{"name":4,"levelParams":[],"type":0}}
EOF
cat > "$W/comparator.json" <<'EOF'
{"theorem_names": ["Foo.targetThm"], "definition_names": []}
EOF

# Headerless apply_edits.tsv with 4 edits: pinnedThm (dropped), targetThm (kept!), freeThm (kept), collideThm (dropped by module)
cat > "$W/edits_in.tsv" <<'EOF'
Pkg.A	2	3	replace	P06	  trivial
Pkg.A	4	5	replace	P06	  trivial
Pkg.A	6	7	replace	P06	  trivial
Pkg.B	1	2	replace	P06	  trivial
EOF

python3 "$T/filter_challenge.py" "$W/edits_in.tsv" "$W/edits_out.tsv" \
  --challenge-export "$W/challenge.export" \
  --comparator-json "$W/comparator.json" \
  --src-root "$W/src" \
  --exclude-modules Pkg.B \
  --report "$W/rep.json"

[ "$(wc -l < "$W/edits_out.tsv")" -eq 2 ] || { echo "FAIL: expected 2 kept edits"; cat "$W/edits_out.tsv"; exit 1; }
grep -q $'^Pkg.A\t4\t5\t' "$W/edits_out.tsv" || { echo "FAIL: targetThm wrongly dropped"; cat "$W/edits_out.tsv"; exit 1; }
grep -q $'^Pkg.A\t6\t7\t' "$W/edits_out.tsv" || { echo "FAIL: freeThm wrongly dropped"; cat "$W/edits_out.tsv"; exit 1; }
python3 -c "import json; r=json.load(open('$W/rep.json')); assert r['kept_edits']==2 and r['dropped_by_challenge_pin']==1 and r['dropped_by_module']==1, r"
echo "PASS (filter_challenge: public theorem NDJSON aux-proof pin drop, targetThm preserved, module collision drop)"

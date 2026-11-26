#!/bin/bash
# toctou/test.sh [N] : regression test of the TOCTOU defect (TOCTOU between the independent reads of the export). The univ
# base's export is turned into two same-size files A (official statement, ill-typed proof) and B (statement True); writer.py
# rewrites the differing line of F in place (A <-> B, mtime restored) while the package under test judges F N times with
# (a) check-sound.sh with default arguments (F under /tmp: hard-link path) and (b) bin/fastverify --from-export --preset sound.
# Any ACCEPTED = the finding is OPEN (exit 1); otherwise FIXED (exit 0). Neither A nor B is a proof of the statement.
set -u
. "$(dirname "$(readlink -f "$0")")/../common.sh"
N=${1:-20}; base_inputs univ || { echo "toctou: base univ missing (run setup.sh)"; exit 2; }
T=$(mktemp -d /tmp/fv-toctou.XXXXXX); trap 'kill $WP 2>/dev/null; rm -rf "$T"' EXIT
python3 -I "$H/toctou/mkab.py" "$SOL" "$CFG" "$T" > /dev/null || exit 2
cp "$T/A.ndjson" "$T/F.ndjson"; C=$T/chal; mkdir -p "$C"; cp "$CH" "$C/challenge.export"; cp "$CFG" "$C/comparator.json"
CSHA=$(sha256sum "$C/challenge.export" | cut -d' ' -f1); CFGSHA=$(sha256sum "$C/comparator.json" | cut -d' ' -f1)   # pin pair
python3 -I "$H/toctou/writer.py" "$T/F.ndjson" "$T/ab.json" 100000 > /dev/null 2>&1 & WP=$!
for k in $(seq "$N"); do
  v=$("$FV/check/sound/check-sound.sh" "$T/F.ndjson" "$CH" "$CFG" --threads 2 --hints none 2>/dev/null | tail -1 | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read() or "{}").get("verdict","NONE"))')
  echo "check-sound.sh $v"
  rm -rf "$T/out"; "$FV/bin/fastverify" - "$C" "$T/out" --from-export "$T/F.ndjson" --preset sound --threads 2 --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" > /dev/null 2>&1
  v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$T/out/result.json" 2>/dev/null || echo NONE)
  echo "export-in $v"
done > "$T/rows"
sort "$T/rows" | uniq -c
if grep -q ' ACCEPTED$' "$T/rows"; then echo "TOCTOU OPEN: an export that is never a proof was ACCEPTED while being rewritten"; exit 1; fi
echo "TOCTOU FIXED: no accept in $N x 2 runs"; exit 0

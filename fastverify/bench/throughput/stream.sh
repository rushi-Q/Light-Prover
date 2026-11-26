#!/bin/bash
# stream.sh STREAMDIR OUT PSET SHA [batchverify args...] : verify a mkstream.py stream batch by batch with tools/batchverify.py
# (sequentially, one header snapshot cache), then tally every attempt's verdict against its label.
# Prints 'STREAM attempts N wall S attempts/hour H ...' and 'MISMATCH ...' lines; exit 1 iff an attempt labelled REJECTED was ACCEPTED.
set -u
S=$1; O=$2; PSET=$3; SHA=$4; shift 4
FV=${FV_ROOT:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
mkdir -p "$O"
t0=$(date +%s.%N)
for b in "$S"/batch-*/; do
  n=$(basename "$b")
  python3 -I "$FV/tools/batchverify.py" --pset "$PSET" --attempts "$b" --out "$O/$n" --challenge-sha256 "$SHA" \
      --fv "$FV" --snapshot-cache "$O/snap" "$@" > "$O/$n.log" 2>&1
  echo "$n $(tail -1 "$O/$n.log")"
done
t1=$(date +%s.%N)
python3 -I - "$S/labels.json" "$O" "$t0" "$t1" <<'PY'
import json, os, sys
labels = json.load(open(sys.argv[1])); O = sys.argv[2]; wall = float(sys.argv[4]) - float(sys.argv[3])
tot = crit = mism = 0; checks = 0; by = {}
for b, lab in sorted(labels.items()):
    try:
        r = json.load(open(os.path.join(O, b, "batch.json")))
    except (OSError, ValueError):
        r = {"attempts": {}}
    checks += r.get("n_checks", 0)
    for name, (kind, exp) in lab.items():
        got = (r["attempts"].get(name) or {}).get("verdict")
        tot += 1
        by.setdefault((kind, got), 0); by[(kind, got)] += 1
        if got != exp:
            mism += 1
            if got == "ACCEPTED":
                crit += 1
            print("MISMATCH", b, name, kind, "expected", exp, "got", got, (r["attempts"].get(name) or {}).get("why", "")[:120])
print("STREAM attempts %d wall %.1f s attempts/hour %.0f checks %d mismatches %d critical %d" % (tot, wall, tot * 3600 / wall, checks, mism, crit))
print("STREAM kind x verdict:", {f"{k}->{v}": n for (k, v), n in sorted(by.items(), key=str)})
sys.exit(1 if crit else 0)
PY

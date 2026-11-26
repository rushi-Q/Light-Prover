#!/bin/bash
# standin-official.sh PROJECT CHALLENGE_DIR OUT [--check X] [--threads N]
# Harness self-test only: a stand-in for bin/fastverify that simply runs the OFFICIAL flow (lib/officialflow.sh) and writes
# OUT/result.json in the package's schema. With FV_BIN=<this file> every regression test must report PASS (the "fast" flow
# IS the official flow); a FAIL there is a bug or a nondeterminism of the test itself, not of the package.
{ # whole script parsed before it runs (safe against edits while running)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
P=$1; C=$2; O=$3
rm -rf "$O"; mkdir -p "$O"; O=$(readlink -f "$O")
t0=$(date +%s)
bash "$H/officialflow.sh" "$P" "$O/official" "$C" > "$O/official.log" 2>&1; rc=$?
t1=$(date +%s)
cat "$O/official.log"
E=$O/official/solution.export
python3 -I - "$O" "$rc" "$E" "$((t1-t0))" <<'EOF'
import hashlib, json, os, sys
o, rc, e, secs = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
r = {"verdict": "ACCEPTED" if rc == 0 else "REJECTED", "standin": "official flow (tests/lib/standin-official.sh)",
     "checks": {"official": {"exit": 0 if rc == 0 else 1}}, "times": {"total_s": secs}}
if os.path.isfile(e) and os.path.getsize(e) > 0:
    h = hashlib.sha256(open(e, "rb").read()).hexdigest()
    r["export"] = {"path": e, "sha256": h, "size": os.path.getsize(e)}
json.dump(r, open(os.path.join(o, "result.json"), "w"), indent=1)
EOF
exit $rc
exit $?
}

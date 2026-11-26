#!/bin/bash
# multi-claims/x/check.sh [WORK] : tools/claims.py - many comparator claims of one project, one build.
# Project = the core batch bC of bench/smallproofs (24 theorems, the package's default toolchain); three claims on it:
#   c1 = {dc07, dc08} (first claim: the build, --keep-work)  -> ACCEPTED
#   c2 = {om05, om06, om07} (export from the kept tree + export-in sound check) -> ACCEPTED
#   c3 = {dc07} with the CHALLENGE statement changed (Fin 64 -> Fin 62) -> REJECTED ('statement do not match')
# plus: the pinned challenge export of c1 is byte-identical to the one a --preset reference run builds itself.
# Prints PASS/FAIL lines and RESULT PASS|FAIL.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)
W=${1:-${SCRATCH:-${TMPDIR:-/tmp}}/$USER-multi-claims}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-8}; WS=${FV_PACKAGES:-$(dirname "$H")/verify/challenge}
# bench/smallproofs/gen.py writes every problem's manifest from the trusted workspace's lake-manifest.json
if [ ! -f "$WS/lake-manifest.json" ]; then
  echo "SKIP multi-claims: no trusted packages workspace at $WS (set FV_PACKAGES or provide <repository root>/verify/challenge)"
  echo "RESULT SKIP"; exit 0
fi
FV_PACKAGES=$WS python3 -I "$H/bench/smallproofs/gen.py" "$W/corpus" > /dev/null || { echo "FAIL multi-claims gen.py"; echo "RESULT FAIL"; exit 1; }
mkdir -p "$W/ch"
for c in c1 c2 c3; do cp -a "$W/corpus/challenges/bC" "$W/ch/$c"; done
sed -i 's/theorem dc07 : ∀ n : Fin 64,/theorem dc07 : ∀ n : Fin 62,/' "$W/ch/c3/Challenge.lean"
python3 -I - "$W/ch" <<'PY'
import json, sys
for c, t in (("c1", ["dc07", "dc08"]), ("c2", ["om05", "om06", "om07"]), ("c3", ["dc07"])):
    p = f"{sys.argv[1]}/{c}/comparator.json"; j = json.load(open(p)); j["theorem_names"] = t; json.dump(j, open(p, "w"), indent=1)
PY
bad=0
python3 -I "$H/tools/claims.py" pin "$W/ch" "$WS" "$W/given" > "$W/pin.log" 2>&1 || { echo "FAIL multi-claims pin: $(tail -3 "$W/pin.log")"; bad=1; }
python3 -I "$H/tools/claims.py" verify "$W/corpus/projects/bC" "$W/given" "$WS" "$W/out" --threads "$T" --claims c1,c2,c3 > "$W/verify.log" 2>&1
for exp in "c1 ACCEPTED" "c2 ACCEPTED" "c3 REJECTED"; do
  set -- $exp
  got=$(awk -v c="$1" '$1==c {print $2}' "$W/out/claims.tsv" 2>/dev/null)
  if [ "$got" = "$2" ]; then echo "PASS multi-claims claim $1: $got"; else echo "FAIL multi-claims claim $1: expected $2, got '${got:-none}'"; bad=1; fi
done
grep -q "statement do not match" "$W/out/c3/log/check_sound.log" 2>/dev/null && echo "PASS multi-claims c3 rejected by compareAt (statement)" \
  || { echo "FAIL multi-claims c3: no statement mismatch in the trusted check's log"; bad=1; }
# the pin equals the challenge export a reference run builds (claim c1)
env -i HOME="$HOME" PATH=/usr/bin:/bin "$H/bin/fastverify" "$W/corpus/projects/bC" "$W/ch/c1" "$W/ref1" --preset reference \
  --threads "$T" --packages "$WS" > "$W/ref1.log" 2>&1
a=$(sha256sum "$W/ref1/challenge.export" 2>/dev/null | cut -d' ' -f1); b=$(cut -d' ' -f1 "$W/given/c1/challenge.export.sha256" 2>/dev/null)
if [ -n "$a" ] && [ "$a" = "$b" ]; then echo "PASS multi-claims pinned challenge export == reference run's (${a:0:16})"
else echo "FAIL multi-claims pinned challenge export ${b:-none} != reference run's ${a:-none}"; bad=1; fi
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

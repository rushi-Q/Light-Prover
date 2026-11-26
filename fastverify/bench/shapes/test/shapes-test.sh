#!/bin/bash
# shapes-test.sh [WORK] : regression test of the synthetic-shape benchmark.
# For each case: the official flow (--preset reference; the shared challenge is built officially by the first run and
# then pinned) and --preset sound (challenge export pinned with --challenge-sha256). PASS iff both verdicts equal the
# expected one; a sound ACCEPT of an expected-REJECTED case prints "FAIL CRITICAL". For accepted cases without merged
# groups the sound export must be byte-identical to the official one (PASS/FAIL export-identity line); merged cases
# (deep chains) only report it (merge renames module-qualified hygienic names - expected).
# Negatives: -sorry3 (sorry deep in a chain), -kfalse2 (a false `decide +kernel` theorem in the closure of a MERGED chain:
# the official build fails in the kernel; under the sound build's skip-kernel-tc the untrusted build passes and the
# trusted CS check must reject).
# Env: SHAPES_CASES, EVAL_THREADS (default 8), FASTVERIFY, PACKAGES_WS. Prints PASS/FAIL lines and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)
export FASTVERIFY=${FASTVERIFY:-$(cd "$H/../.." && pwd)}
export PACKAGES_WS=${PACKAGES_WS:-$(dirname "$FASTVERIFY")/verify/challenge}
W=${1:-${SCRATCH:-/scratch}/$USER-shapes-test}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-8}
CASES=${SHAPES_CASES:-core-wide-8-tiny core-deep-32-tiny core-layered-4x4-typeclass core-wide-4-kernel core-wide-4-inductive core-deep-8-tiny-sorry3 core-deep-8-tiny-kfalse2}
python3 -I "$H/gen.py" "$W" $CASES > /dev/null || { echo "FAIL gen.py"; echo "RESULT FAIL"; exit 1; }
bad=0
for c in $CASES; do
  exp=ACCEPTED; case "$c" in *-sorry*|*-kfalse*) exp=REJECTED;; esac
  python3 -I "$H/run.py" "$W" "$c" reference "$T" > /dev/null
  if [ ! -f "$W/challenge/challenge.export" ]; then   # pin the officially built shared challenge export
    ce=$(ls -d "$W"/runs/"$c"-reference-*/ 2>/dev/null | head -1)challenge.export
    [ -f "$ce" ] && cp "$ce" "$W/challenge/challenge.export" && sha256sum "$W/challenge/challenge.export" | cut -d' ' -f1 > "$W/challenge/challenge.export.sha256"
  fi
  python3 -I "$H/run.py" "$W" "$c" sound "$T" > /dev/null
  read -r vr vs sr ss mg <<< "$(python3 -I - "$W/results.jsonl" "$c" <<'PY'
import json, sys
last = {}
for l in open(sys.argv[1]):
    r = json.loads(l)
    if r["case"] == sys.argv[2]:
        last[r["preset"]] = r
g = lambda p, k: (last.get(p) or {}).get(k)
sh = lambda p: ((last.get(p) or {}).get("export") or {}).get("sha256") or "-"
mg = (((last.get("sound") or {}).get("sched") or {}).get("sched_start") or {}).get("merged_groups") or 0
print(g("reference", "verdict"), g("sound", "verdict"), sh("reference"), sh("sound"), mg)
PY
)"
  if [ "$exp" = REJECTED ] && [ "$vs" = ACCEPTED ]; then echo "FAIL CRITICAL $c: sound ACCEPTED an officially $exp case (official $vr)"; bad=1
  elif [ "$vr" = "$exp" ] && [ "$vs" = "$exp" ]; then echo "PASS $c expected=$exp official=$vr sound=$vs merged_groups=$mg"
  else echo "FAIL $c expected=$exp official=$vr sound=$vs"; bad=1; fi
  if [ "$exp" = ACCEPTED ]; then
    if [ "$mg" = 0 ]; then
      if [ "$sr" = "$ss" ] && [ "$sr" != - ]; then echo "PASS $c export identical to the official one (${sr:0:16})"
      else echo "FAIL $c export differs from the official one without merged groups ($sr vs $ss)"; bad=1; fi
    else echo "INFO $c merged ($mg groups): export identical=$([ "$sr" = "$ss" ] && echo yes || echo no)"; fi
  fi
done
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

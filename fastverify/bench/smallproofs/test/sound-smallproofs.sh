#!/bin/bash
# sound-smallproofs.sh [WORK] : regression test of the small-proof corpus. For each case: the official flow
# (--preset reference, challenge built officially) and --preset sound with the official challenge export pinned
# (--challenge-sha256). PASS iff both verdicts equal the expected one (cases.json); a sound ACCEPT of a case whose
# expected verdict is REJECTED prints "FAIL CRITICAL". The negatives xk01/xk02/xk04 (and xk03 with Mathlib) are false
# `decide +kernel` claims: under the sound build's skip-kernel-tc the UNTRUSTED build succeeds, the TRUSTED check must reject.
# xe06 / xe01 (Mathlib) are proofs that do not elaborate (expected REJECTED; the failed-build path).
# A failed build in sound mode must stop after the exact build B1 (attempts B3,B1).
# Env: SMALLPROOFS_CASES (default: core-only om05 dh02 dh05 ks20 gr02 in04 xk01 xk02 xk04 xe06 + nn01 xk03 xe01 when the Mathlib
# workspace exists), EVAL_THREADS (default 8). Prints 'PASS <case> ...' / 'FAIL ...' lines and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)
FASTVERIFY=${FASTVERIFY:-$(cd "$H/../.." && pwd)}; LIGHT_LEAN=${LIGHT_LEAN:-$(dirname "$FASTVERIFY")}
WS=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}
W=${1:-${SCRATCH:-/scratch}/$USER-smallproofs-test}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-8}
CASES=${SMALLPROOFS_CASES:-om05 dh02 dh05 ks20 gr02 in04 xk01 xk02 xk04 xe06}
[ -z "${SMALLPROOFS_CASES:-}" ] && [ -d "$WS/.lake/packages/mathlib" ] && CASES="$CASES nn01 xk03 xe01"
FV_PACKAGES=$WS python3 -I "$H/gen.py" "$W/corpus" > /dev/null || { echo "FAIL gen.py"; echo "RESULT FAIL"; exit 1; }
bad=0
for c in $CASES; do
  exp=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]].get("expected","ACCEPTED"))' "$W/corpus/cases.json" "$c")
  FASTVERIFY=$FASTVERIFY FV_PACKAGES=$WS "$H/run1.sh" "$W/corpus" "$c" reference "$W" "$T" src
  "$H/mkgiven.sh" "$W/corpus" "$W" "$c" > /dev/null 2>&1 || { echo "FAIL $c: no official challenge export"; bad=1; continue; }
  FASTVERIFY=$FASTVERIFY FV_PACKAGES=$WS "$H/run1.sh" "$W/corpus" "$c" sound "$W" "$T" given
  vr=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/runs/$c.reference/result.json" 2>/dev/null)
  vs=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r.get("verdict"), r.get("trust"))' "$W/runs/$c.sound/result.json" 2>/dev/null)
  if [ "$exp" = REJECTED ] && [ "${vs%% *}" = ACCEPTED ]; then echo "FAIL CRITICAL $c: sound ACCEPTED a $exp case (official $vr)"; bad=1
  elif [ "$vr" = "$exp" ] && [ "${vs%% *}" = "$exp" ]; then
    # in sound mode a failed build must end after the exact build B1 (no third, official build)
    att=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(",".join("%s:%s" % (a["option"], a["exit"]) for a in (r.get("build") or {}).get("attempts", [])))' "$W/runs/$c.sound/result.json" 2>/dev/null)
    case ",$att," in
      *,B1:1,B0:*) echo "FAIL $c expected=$exp sound=$vs but build attempts $att (official build after a failed exact B1)"; bad=1;;
      *) echo "PASS $c expected=$exp official=$vr sound=$vs attempts=$att";;
    esac
  else echo "FAIL $c expected=$exp official=$vr sound=$vs"; bad=1; fi
done
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit $bad

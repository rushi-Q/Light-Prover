#!/bin/bash
# test 067 (kind e2e, custom): the deployed pipeline.sh never cleared WORK: a re-run imported the previous run's .olean files
# and inherited its 'EXIT 0'. Fixed behaviour: bin/fastverify refuses a non-empty OUT (no verdict: ERROR) and a fresh OUT
# gives the official verdict. Cases (x/v1 honest; v2 = Helper.lean deleted; v3 = type error), OFFICIAL = x/officialflow.sh:
#   setup-v1-fresh  : v1 into a fresh OUT                 -> must equal official (ACCEPTED)
#   case-a-v2-reuse : v2 into v1's OUT (reused)           -> never ACCEPTED (refusal = ERROR expected)
#   case-b-v3-reuse : v3 into v1's OUT (reused)           -> never ACCEPTED
#   case-a-v2-fresh / case-b-v3-fresh : fresh OUT         -> must equal official (REJECTED)
{ # whole script parsed before it runs (safe against edits while running)
set -u
TD=$(cd "$(dirname "$0")" && pwd); X=$TD/x; H=$TD/../lib; FVB=${FV_BIN:-$TD/../../bin/fastverify}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/067.XXXXXX")}; mkdir -p "$(dirname "$W")"; W=$(readlink -f "$(dirname "$W")")/$(basename "$W"); L=$W.log
rm -rf "$W"; mkdir -p "$W"; cp -a "$X/challenge" "$W/challenge"; for v in v1 v2 v3; do cp -a "$X/$v" "$W/$v"; done
T=${EVAL_THREADS:-8}
fv() { # fv VERSION OUT -> fast rc from the package's EXIT CODE (a reused OUT holds the previous run's stale result.json):
  #        0 ACCEPTED, 1 REJECTED, anything else -> 4 (ERROR / refusal, never an accept)
  env -i HOME="$HOME" PATH=/usr/bin:/bin "$FVB" "$W/$1" "$W/challenge" "$2" ${FV_ARGS:---check C3,C0} --threads $T > "$2.fv.log" 2>&1; local rc=$?
  tail -3 "$2.fv.log" | sed 's/^/  fast: /' >> "$L"; echo "  fast: bin/fastverify exit $rc" >> "$L"
  case $rc in 0|1) echo $rc;; 2) echo 2;; *) echo 4;; esac; }   # 2 = refused/declined (no verdict)
: > "$L"
if [ ! -x "$FVB" ] || [ "${FV_FAST:-}" = deployed ]; then
  echo "=== RESULT case=all official=- fast=3" >> "$L"
else
  for v in v1 v2 v3; do bash "$X/officialflow.sh" "$W/$v" "$W/off-$v" "$W/challenge" > "$W/off-$v.log" 2>&1; eval "o_$v=$?"; done
  echo "##### setup-v1-fresh" >> "$L"; f=$(fv v1 "$W/shared"); echo "=== RESULT case=setup-v1-fresh official=$o_v1 fast=$f" >> "$L"
  echo "##### case-a-v2-reuse" >> "$L"; f=$(fv v2 "$W/shared"); echo "=== RESULT case=case-a-v2-reuse official=$o_v2 fast=$f" >> "$L"
  echo "##### case-b-v3-reuse" >> "$L"; f=$(fv v3 "$W/shared"); echo "=== RESULT case=case-b-v3-reuse official=$o_v3 fast=$f" >> "$L"
  echo "##### case-a-v2-fresh" >> "$L"; f=$(fv v2 "$W/fresh2"); echo "=== RESULT case=case-a-v2-fresh official=$o_v2 fast=$f" >> "$L"
  echo "##### case-b-v3-fresh" >> "$L"; f=$(fv v3 "$W/fresh3"); echo "=== RESULT case=case-b-v3-fresh official=$o_v3 fast=$f" >> "$L"
fi
python3 -I "$H/parse.py" 067 "$L" "$TD/EXPECT" | tee "$W.tsv"
[ -n "${KEEP_WORK:-}" ] || rm -rf "$W"
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}

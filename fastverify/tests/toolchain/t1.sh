#!/bin/bash
# tests/toolchain/t1.sh [WORK] -- test of the OPT-IN UNSAFE toolchain option T1 (patched / PGO toolchain).
# T1 is offered only as an explicitly unsafe speed option; this test documents WHY: it (1) verifies the pinned unofficial
# trees under /scratch/fastverify-next/tc (toolchains/unofficial/*.json; a tree that cannot start on this host must be
# refused: the PGO build needs glibc >= 2.38) and (2) runs the toolchain regression (regress_toolchain.sh) with
# the T1 tree that starts here as the candidate: the known divergences from the official release MUST still show up
# (findings 004 014 020 031 037 040 050 061 = OPEN by design for T1). PASS = verification behaves as specified AND the
# divergences are reproduced (if they ever disappeared the documentation would be wrong).
main() {
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd); TC="python3 -I $FV/lib/toolchain.py"
REGRESS=$H/regress_toolchain.sh   # package-local copy of the toolchain regression (inputs from tests/NNN-*/x)
B=${FV_TC_DIR:-/scratch/fastverify-next/tc}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/t1.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"
fails=0; cand=
for m in "$FV"/toolchains/unofficial/*.json; do
  n=$(basename "$m" .json)
  if [ ! -d "$B/$n" ]; then echo "INFO $n: not installed under $B on $(hostname)"; continue; fi
  $TC verify-unofficial "$B/$n" "$n" --json "$W/$n.json" > /dev/null 2> "$W/$n.err"; rc=$?
  starts=0; env -i PATH=/usr/bin:/bin "$B/$n/bin/lean" --version > /dev/null 2>&1 && starts=1
  if [ $starts = 1 ] && [ $rc = 0 ]; then echo "PASS $n: verified (unsafe=true) and starts on $(hostname)"; cand=${cand:-$B/$n}
  elif [ $starts = 0 ] && [ $rc = 2 ]; then echo "PASS $n: cannot start on $(hostname) -> refused (rc 2) as required"
  else echo "FAIL $n: verify rc=$rc, starts=$starts: $(head -c 300 "$W/$n.err")"; fails=$((fails+1)); fi
done
python3 -I - "$W" <<'PY' || { echo "FAIL unsafe flag missing in verify-unofficial JSON"; fails=$((fails+1)); }
import glob, json, sys
for f in glob.glob(sys.argv[1] + "/*.json"):
    r = json.load(open(f))
    if r.get("verified"): assert r.get("unsafe") is True and r.get("official") is False and r.get("findings"), f
PY
if [ -n "$cand" ] && [ -f "$REGRESS" ]; then
  bash "$REGRESS" "$cand" > "$W/regress.log" 2>&1
  nd=$(grep -c '^DIFFERENT' "$W/regress.log"); ns=$(grep -c '^SAME' "$W/regress.log")
  sed 's/^/  regress: /' "$W/regress.log"
  if [ "$nd" -ge 1 ]; then echo "PASS T1 divergences reproduced with $cand: $nd DIFFERENT, $ns SAME (T1 is NOT exact - opt-in unsafe only)"
  else echo "FAIL T1 showed no divergence ($ns SAME) - the documented findings for T1 need re-checking"; fails=$((fails+1)); fi
else echo "INFO no startable T1 tree on $(hostname); divergence part skipped"; fi
[ $fails = 0 ] && { echo "RESULT: PASS"; return 0; } || { echo "RESULT: FAIL ($fails)"; return 1; }
}
main "$@"; exit $?

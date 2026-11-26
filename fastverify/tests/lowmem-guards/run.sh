#!/bin/bash
# tests/lowmem-guards/run.sh [FV_ROOT]: the guards of the LOW-MEMORY sound checks
# (check/lowmem/check-sound-lowmem.sh and check-sound-ultralowmem.sh) that no installed test drives. Mutation testing of
# check-sound-lowmem.sh 50103d39 (598 mutants vs tests/lowmem-check + the crafted-export cases) left them all alive:
#   LW-0261 (the cross-version gate run only under --preflight: a 4.37 challenge whose definition is NOT sorried - the CRITICAL
#   cross-version class - is then ACCEPTED with the default pins; tests/lowmem-check tests that rule only with the 4.37 pins, whose own ccmp has it),
#   LW-0280 (an unadmitted release judged anyway), LW-0251/0254/0255/0260 (--challenge-sha256 / --comparator-sha256 mismatch
#   ignored: the private-copy pin window reopens), LW-0245..0250 (malformed pins accepted), LW-0075 (pinned binaries not sha-checked
#   without an integrity cache), LW-0301/0306/0309/0314 (a failing per-run or preflight self-test ignored).
# Cases, on BOTH judges (live pins unless stated; each judge run in its own private work dir):
#   control            self-test good export + both pins right                      -> exit 0 ACCEPTED
#   xv-437-nonsorried  4.37 challenge with a non-sorried definition (default pins)  -> exit 1 REJECTED 'not sorried'
#   xv-unadmitted      challenge whose header names Lean 4.99.0 (not admitted)      -> exit 2 DECLINED 'xversion'
#   pin-chal-mismatch  --challenge-sha256 of another file                           -> exit 2 DECLINED
#   pin-cfg-mismatch   --comparator-sha256 of another file                          -> exit 2 DECLINED
#   pin-malformed      upper-case / 63-digit pin                                    -> exit 2 DECLINED
#   cfg-S1-3           comparator.json permitting sorryAx                           -> exit 2 DECLINED
#   bin-tampered       package copy whose pins.env records a wrong sha256 for ccmp_lowmem -> exit 2 DECLINED 'sha256'
#   selftest-broken    package copy whose selftest_good pin is the bad export (sha re-pinned) -> exit 2 DECLINED 'self-test'
#   preflight-selftest-broken  the same copy, --preflight                         -> exit 2 (self-test refusal)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${1:-$(cd "$H/../.." && pwd)}
W=$(mktemp -d "${TMPDIR:-/tmp}/lowmem-guards.XXXXXX") || { echo "FAIL setup: mktemp"; echo "RESULT pass=0 fail=1"; exit 1; }
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
pass=0; fail=0
pinp() { awk -v n="$2" '$1=="PIN" && $2==n {print $4}' "$1"; }
P=$FV/check/lowmem/pins.env
GOOD=$(pinp "$P" selftest_good); BAD=$(pinp "$P" selftest_bad); CH=$(pinp "$P" selftest_challenge); CF=$(pinp "$P" selftest_comparator)
CHS=$(sha256sum "$CH" | cut -d' ' -f1); CFS=$(sha256sum "$CF" | cut -d' ' -f1)
FX437=/scratch/fastverify-next/fixtures/lean-4.37   # the 4.37 fixtures tests/lowmem-check uses
python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["permitted_axioms"]=list(c["permitted_axioms"])+["sorryAx"]; json.dump(c,open(sys.argv[2],"w"))' "$CF" "$W/cfg-sorry.json"
python3 -I - "$CH" "$W/chal-499.export" <<'PY'
import json, sys
src, dst = sys.argv[1:3]
with open(src, "rb") as f, open(dst, "wb") as g:
    m = json.loads(f.readline()); m["meta"]["lean"] = {"githash": "deadbeef" * 5, "version": "4.99.0"}
    g.write(json.dumps(m, separators=(",", ":")).encode() + b"\n"); g.write(f.read())
PY
mkpkg() {  # mkpkg NAME AWK_PROG -> private package copy whose check/lowmem/pins*.env are rewritten by AWK_PROG
  local Q=$W/pkg-$1
  rsync -a --exclude tests --exclude pipeline --exclude 'review-*' --exclude __pycache__ --exclude check/notary --exclude bench "$FV/" "$Q/"
  chmod -R u+w "$Q/check/lowmem"   # the copy must be writable even if the package is installed read-only
  for pf in pins.env pins-ultralowmem.env; do awk "$2" "$FV/check/lowmem/$pf" > "$Q/check/lowmem/$pf"; done
  echo "$Q"
}
TAMPER=$(mkpkg tamper '$1=="PIN" && $2=="ccmp_lowmem" {print "PIN ccmp_lowmem " "0000000000000000000000000000000000000000000000000000000000000000" " " $4; next} {print}')
BADS=$(sha256sum "$BAD" | cut -d' ' -f1)
STB=$(mkpkg stbroken '$1=="PIN" && $2=="selftest_good" {print "PIN selftest_good '"$BADS"' '"$BAD"'"; next} {print}')
run() {  # run LABEL PKG SCRIPT SOL CHAL CFG WANT_EXIT WANT_VERDICT WANT_SUBSTR [args...]
  local l=$1 pk=$2 js=$3 s=$4 c=$5 g=$6 we=$7 wv=$8 wr=$9; shift 9
  mkdir -p "$W/run-$l"
  TMPDIR=$W/run-$l "$pk/check/lowmem/$js" "$s" "$c" "$g" --threads 4 --json "$W/$l.json" "$@" > "$W/$l.out" 2>&1; local rc=$?
  local v; v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r.get("verdict"), int(sys.argv[2] in json.dumps(r)))' "$W/$l.json" "$wr" 2>/dev/null)
  set -- $v
  if [ "$rc" = "$we" ] && [ "${1:-}" = "$wv" ] && [ "${2:-}" = 1 ]; then echo "PASS $l: exit $rc $1"; pass=$((pass+1))
  else echo "FAIL $l: expected exit $we $wv (~ '$wr'), got exit $rc '$v' :: $(tail -c 300 "$W/$l.json" 2>/dev/null | tr '\n' ' ')"; fail=$((fail+1)); fi
}
for J in lowmem:check-sound-lowmem.sh ultralowmem:check-sound-ultralowmem.sh; do
  n=${J%%:*}; js=${J#*:}
  run "$n-control" "$FV" "$js" "$GOOD" "$CH" "$CF" 0 ACCEPTED "" --challenge-sha256 "$CHS" --comparator-sha256 "$CFS"
  if [ -f "$FX437/challenge.export" ]; then
    run "$n-xv-437-nonsorried" "$FV" "$js" "$FX437/good.export" "$FX437/challenge.export" "$FX437/comparator.json" 1 REJECTED "not sorried"
  else echo "SKIP $n-xv-437-nonsorried: $FX437 missing on this host"; fi
  run "$n-xv-unadmitted" "$FV" "$js" "$GOOD" "$W/chal-499.export" "$CF" 2 DECLINED "xversion"
  run "$n-pin-chal-mismatch" "$FV" "$js" "$GOOD" "$CH" "$CF" 2 DECLINED "challenge export sha256" --challenge-sha256 "$CFS"
  run "$n-pin-cfg-mismatch" "$FV" "$js" "$GOOD" "$CH" "$CF" 2 DECLINED "comparator config sha256" --comparator-sha256 "$CHS"
  run "$n-pin-malformed-upper" "$FV" "$js" "$GOOD" "$CH" "$CF" 2 DECLINED "64 lowercase hex" --challenge-sha256 "$(printf '%s' "$CHS" | tr a-f A-F)"
  run "$n-pin-malformed-short" "$FV" "$js" "$GOOD" "$CH" "$CF" 2 DECLINED "64 lowercase hex" --challenge-sha256 "${CHS:1}"
  run "$n-cfg-S1-3" "$FV" "$js" "$GOOD" "$CH" "$W/cfg-sorry.json" 2 DECLINED "S1(3)"
  run "$n-bin-tampered" "$TAMPER" "$js" "$GOOD" "$CH" "$CF" 2 DECLINED "sha256 mismatch"
  run "$n-selftest-broken" "$STB" "$js" "$GOOD" "$CH" "$CF" 2 DECLINED "self-test"
  # --preflight must run the self-test too (LW-0309: a preflight that skips it reports PREFLIGHT_OK with broken binaries)
  mkdir -p "$W/run-$n-pf"
  TMPDIR=$W/run-$n-pf "$STB/check/lowmem/$js" --preflight > "$W/$n-pf.out" 2>&1; rc=$?
  if [ "$rc" = 2 ] && grep -q "self-test" "$W/$n-pf.out"; then echo "PASS $n-preflight-selftest-broken: exit 2"; pass=$((pass+1))
  else echo "FAIL $n-preflight-selftest-broken: expected exit 2 + self-test refusal, got exit $rc :: $(tail -c 200 "$W/$n-pf.out" | tr '\n' ' ')"; fail=$((fail+1)); fi
done
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]

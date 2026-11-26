#!/bin/bash
# tests/check437/run.sh [PKG]  - regression test of the 4.37.0-rc1 trusted check:
#   check/sound/check-sound.sh --pins check/sound/pins-437.env (official 4.37 judge code + kernel) must
#   (1) pass --preflight (pins, toolchain manifest, self-test);
#   (2) give the known verdicts on the self-test pair;
#   (3) REJECT every attack export of tests/kernel-cves/craft_cves.py BY THE LEAN LEG ITSELF (the replay's record check /
#       the 4.37 kernel's loose-bvar check; reason 'Lean default exited with 1') and ACCEPT the 3 controls;
#   (4) if the 4.37 toy fixtures are installed (/scratch/fastverify-next/fixtures/lean-4.37): statement mismatch ->
#       REJECTED, non-sorried challenge definition -> REJECTED ('Challenge definition is not sorried'), = the official 4.37
#       comparator's verdicts;
#   (5) the default pins are untouched: the self-test pair through check-sound.sh WITHOUT --pins gives the 4.36 verdicts
#       and reports toolchain leanprover/lean4:v4.36.0.
# Prints PASS/FAIL per case and 'RESULT PASS n' / 'RESULT FAIL n'. Exit 0 iff all pass.
set -u
PKG=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
CS=$PKG/check/sound/check-sound.sh; P37=$PKG/check/sound/pins-437.env
ST=${SELFTEST_DIR:-/scratch/fastverify-next/selftest}
FX=${FIXTURES_437:-/scratch/fastverify-next/fixtures/lean-4.37}
W=$(mktemp -d "${TMPDIR:-/tmp}/check437.XXXXXX"); trap 'rm -rf "$W"' EXIT
pass=0; fail=0
jq() { /usr/bin/python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); v=j
for k in sys.argv[2].split("."): v=v.get(k) if isinstance(v,dict) else None
print("" if v is None else v)' "$1" "$2" 2>/dev/null; }
case_() {  # case_ NAME WANT_RC WANT_REASON_PREFIX|- [ARGS...]
  local name=$1 want=$2 why=$3; shift 3
  local j=$W/$name.json; "$CS" "$@" --threads 4 --json "$j" > "$W/$name.out" 2>&1; local rc=$?
  local reason; reason=$(jq "$j" reason)
  if [ "$rc" = "$want" ] && { [ "$why" = - ] || [ "${reason#"$why"}" != "$reason" ]; }; then
    pass=$((pass+1)); echo "PASS $name: rc=$rc $(jq "$j" verdict) ${reason:0:90}"
  else
    fail=$((fail+1)); echo "FAIL $name: rc=$rc (want $want${why:+, reason '$why*'}) $(jq "$j" verdict) ${reason:0:160}"
  fi
}
[ -f "$P37" ] || { echo "FAIL missing $P37"; echo "RESULT FAIL 1"; exit 1; }
# (1) preflight
if "$CS" --preflight --pins "$P37" > "$W/preflight.out" 2>&1; then pass=$((pass+1)); echo "PASS preflight-437"; else fail=$((fail+1)); echo "FAIL preflight-437: $(tail -1 "$W/preflight.out")"; fi
# (2) self-test pair through the 4.37 pins
case_ st437-good 0 "statements + axioms match" "$ST/good.export" "$ST/challenge.export" "$ST/comparator.json" --pins "$P37"
case_ st437-bad 1 "error: Illegal axiom detected" "$ST/bad.export" "$ST/challenge.export" "$ST/comparator.json" --pins "$P37"
j=$W/st437-good.json; [ "$(jq "$j" toolchain)" = leanprover/lean4:v4.37.0-rc1 ] && { pass=$((pass+1)); echo "PASS st437-toolchain-recorded"; } || { fail=$((fail+1)); echo "FAIL st437-toolchain-recorded: $(jq "$j" toolchain)"; }
[ "$(jq "$j" pins_sha256)" = "$(sha256sum "$P37" | cut -d' ' -f1)" ] && { pass=$((pass+1)); echo "PASS st437-pins-sha-recorded"; } || { fail=$((fail+1)); echo "FAIL st437-pins-sha-recorded"; }
# (3) the crafted kernel/replay cases of tests/kernel-cves: attacks rejected by the Lean leg, controls accepted
/usr/bin/python3 -I "$PKG/tests/kernel-cves/craft_cves.py" --selftest-dir "$ST" --out "$W/cves" > "$W/craft.log" 2>&1 || { fail=$((fail+1)); echo "FAIL craft_cves: $(tail -1 "$W/craft.log")"; }
for e in "$W"/cves/*.export; do
  n=$(basename "$e" .export); cfg=$ST/comparator.json; case $n in 15101_*) cfg=$W/cves/comparator_noquot.json;; esac
  case $n in
    00_*|*_control_*|*_baseline_*) case_ "cve437-$n" 0 "statements + axioms match" "$e" "$ST/challenge.export" "$cfg" --pins "$P37";;
    *) case_ "cve437-$n" 1 "error: Lean default exited with 1" "$e" "$ST/challenge.export" "$cfg" --pins "$P37";;
  esac
done
# (4) 4.37 toy fixtures (official 4.37 comparator verdicts recorded in fixtures/VERDICTS)
if [ -f "$FX/challenge.export" ]; then
  case_ toy437-defch 1 "error: Challenge and solution theorem statement do not match" "$FX/defch.export" "$FX/challenge.export" "$FX/comparator.json" --pins "$P37"
  case_ toy437-good-nonsorried-def 1 "error: Challenge definition is not sorried" "$FX/good.export" "$FX/challenge.export" "$FX/comparator.json" --pins "$P37"
else
  echo "SKIP toy437 fixtures ($FX not installed)"
fi
# (4b) the encapsulated replay (--hide) must give the same verdicts on the self-test pair and record the list
HL=$PKG/check/sound/hide/lean-4.37.0-rc1-no-expose.txt
if [ -f "$HL" ] && grep -q -- '--hide)' "$CS"; then
  case_ st437-hide-good 0 "statements + axioms match" "$ST/good.export" "$ST/challenge.export" "$ST/comparator.json" --pins "$P37" --hide "$HL"
  case_ st437-hide-bad 1 "error: Illegal axiom detected" "$ST/bad.export" "$ST/challenge.export" "$ST/comparator.json" --pins "$P37" --hide "$HL"
  [ "$(jq "$W/st437-hide-good.json" hide_sha256)" = "$(sha256sum "$HL" | cut -d' ' -f1)" ] && { pass=$((pass+1)); echo "PASS st437-hide-sha-recorded"; } || { fail=$((fail+1)); echo "FAIL st437-hide-sha-recorded"; }
  case_ cve437-hide-15100 1 "error: Lean default exited with 1" "$W/cves/15100_unsafe_ctor_forged_meta.export" "$ST/challenge.export" "$ST/comparator.json" --pins "$P37" --hide "$HL"
else
  echo "SKIP --hide cases (hide list or v2.2 wiring not present)"
fi
# (5) default path unchanged
case_ st436-good 0 "statements + axioms match" "$ST/good.export" "$ST/challenge.export" "$ST/comparator.json"
case_ st436-bad 1 "error: Illegal axiom detected" "$ST/bad.export" "$ST/challenge.export" "$ST/comparator.json"
[ "$(jq "$W/st436-good.json" toolchain)" = leanprover/lean4:v4.36.0 ] && { pass=$((pass+1)); echo "PASS st436-toolchain-recorded"; } || { fail=$((fail+1)); echo "FAIL st436-toolchain-recorded: $(jq "$W/st436-good.json" toolchain)"; }
if [ "$fail" = 0 ]; then echo "RESULT PASS $pass"; exit 0; else echo "RESULT FAIL $fail (pass $pass)"; exit 1; fi

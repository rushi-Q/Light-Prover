#!/bin/bash
# check/sound/test/preset.sh — regression test of SOUND mode in the orchestrator (bin/fastverify --preset sound / check CS):
# export-in mode on the pinned self-test exports (no build), so it runs in ~1 min on any host with the pinned binaries.
# Cases: good -> ACCEPTED + trust "sound" + soundness block; extra axiom -> REJECTED; kernel-invalid proof -> REJECTED;
# changed statement -> REJECTED; --challenge-sha256 matching -> ACCEPTED, mismatching or missing -> ERROR (refused, exit 2);
# a veto check (C3; formerly C1 = check A, now retired) selected beside CS that rejects -> REJECTED; result.json
# verdict/exit consistent.
# Prints 'PASS|FAIL <case>: ...' rows and 'RESULT pass=N fail=M'; exit 0 iff all PASS.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); FV=$(cd "$H/../.." && pwd)/bin/fastverify
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$H/pins.env"; }
GOOD=$(pin selftest_good); BAD=$(pin selftest_bad); CHALX=$(pin selftest_challenge); CFG=$(pin selftest_comparator)
mkdir -p "${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}" 2>/dev/null   # the parent of the work dir may not exist yet
W=$(mktemp -d "${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}/soundPreset-test.XXXXXX") || exit 2
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
mkdir -p "$W/chal"; cp "$CHALX" "$W/chal/challenge.export"; cp "$CFG" "$W/chal/comparator.json"
sha256sum "$W/chal/challenge.export" | sed 's#  .*#  challenge.export#' > "$W/chal/challenge.export.sha256"
CSHA=$(cut -d' ' -f1 "$W/chal/challenge.export.sha256")
sed 's/^{"app":{"arg":518,"fn":526},"ie":527}$/{"app":{"arg":512,"fn":526},"ie":527}/' "$GOOD" > "$W/kernel-bad.export"
sed 's/^{"ie":520,"natVal":"4"}$/{"ie":520,"natVal":"5"}/' "$GOOD" > "$W/stmt-bad.export"
fails=0; passes=0; n=0
run() {  # run NAME WANT_EXIT WANT_VERDICT EXPORT [ARGS...]
  local name=$1 want=$2 wv=$3 e=$4; shift 4; n=$((n+1))
  local out=$W/out$n
  "$FV" - "$W/chal" "$out" --from-export "$e" --preset sound --threads 4 "$@" > "$W/log$n" 2>&1; local got=$?
  local v; v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["verdict"], r.get("trust"), r.get("exit"), "soundness" in r)' "$out/result.json" 2>/dev/null)
  set -- $v
  if [ "$got" = "$want" ] && [ "${1:-}" = "$wv" ] && [ "${3:-}" = "$got" ] && { [ "$wv" = ERROR ] || { [ "${2:-}" = sound ] && [ "${4:-}" = True ]; }; }; then
    echo "PASS $name: exit $got verdict ${1:-} trust ${2:-}"; passes=$((passes+1))
  else
    echo "FAIL $name: expected exit $want verdict $wv, got exit $got / result '$v' :: $(tail -2 "$W/log$n" | tr '\n' ' ' | cut -c1-300)"; fails=$((fails+1))
  fi
}
CFGSHA=$(sha256sum "$W/chal/comparator.json" | cut -d' ' -f1)
P=(--challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA")   # the comparator pin is required with the challenge pin
run good-accepted 0 ACCEPTED "$GOOD" "${P[@]}"
# check-sound v2 (check/sound/README.md): the orchestrator asserts its private export (--private-inputs) and the check's structured leg status
# reaches result.json (checks.sound.stage.legs / private_inputs_asserted)
if python3 -I -c 'import json,sys; s=json.load(open(sys.argv[1]))["checks"]["sound"]["stage"]; sys.exit(0 if s.get("private_inputs_asserted")==1 and s["legs"]["lean"]["rc"]==0 and s["legs"]["k2"]["rc"]==0 and s["inputs"]["export"]["private"]=="copy" else 1)' "$W/out$n/result.json" 2>/dev/null; then
  echo "PASS v2-private-inputs-and-legs-in-result: checks.sound.stage has private_inputs_asserted=1, legs rc 0/0"; passes=$((passes+1))
else
  echo "FAIL v2-private-inputs-and-legs-in-result: $(python3 -I -c 'import json,sys; print(json.dumps(json.load(open(sys.argv[1]))["checks"]["sound"]["stage"])[:400])' "$W/out$n/result.json" 2>&1)"; fails=$((fails+1))
fi
run good-no-challenge-pin-refused 2 ERROR "$GOOD"
run challenge-pin-mismatch 2 ERROR "$GOOD" --challenge-sha256 0000000000000000000000000000000000000000000000000000000000000000 --comparator-sha256 "$CFGSHA"
run comparator-pin-missing-refused 2 ERROR "$GOOD" --challenge-sha256 "$CSHA"
run comparator-pin-mismatch 2 ERROR "$GOOD" --challenge-sha256 "$CSHA" --comparator-sha256 0000000000000000000000000000000000000000000000000000000000000000
run bad-axiom-rejected 1 REJECTED "$BAD" "${P[@]}"
run kernel-invalid-rejected 1 REJECTED "$W/kernel-bad.export" "${P[@]}"
run statement-changed-rejected 1 REJECTED "$W/stmt-bad.export" "${P[@]}"
# a second selected check can only veto: C3 (check B) beside CS on the axiom export -> REJECTED; on good -> ACCEPTED
# (C1 = check A, now retired)
run veto-check-bad 1 REJECTED "$BAD" --check CS,C3 "${P[@]}"
run veto-check-good 0 ACCEPTED "$GOOD" --check CS,C3 "${P[@]}"
echo "RESULT pass=$passes fail=$fails"
[ "$fails" = 0 ]

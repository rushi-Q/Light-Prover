#!/bin/bash
# orchestrator-toctou/test.sh [FV_ROOT] (a coverage gap of lib/fastverify.py verify_components_end):
# The orchestrator records the sha256 of every pinned component / stage script at the start and re-hashes them at the end
# (TOCTOU guard: a swap during a run -> verdict ERROR, exit 2). No package test exercised it: mutants that disable the guard
# (PY-0016 'if r.returncode != 0' -> False, PY-0020, PY-0024 'if h != c["sha256"]' -> False) survive check/sound/test/preset.sh.
# Case: export-in --preset sound on the pinned self-test good export, in a PRIVATE package copy; while the run is in its CS
# check, one line is appended to the copy's check/sound/check-sound.sh (the running bash already parsed it: the run itself is
# unaffected) -> the end-of-run guard must report it: verdict ERROR, exit 2, basis 'components changed during the run'.
# Control: the same run without the modification -> ACCEPTED.
set -u
FV=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
W=$(mktemp -d "${TMPDIR:-/tmp}/fv-toctou.XXXXXX"); trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$FV/check/sound/pins.env"; }
GOOD=$(pin selftest_good); mkdir -p "$W/chal"; cp "$(pin selftest_challenge)" "$W/chal/challenge.export"; cp "$(pin selftest_comparator)" "$W/chal/comparator.json"
CSHA=$(sha256sum "$W/chal/challenge.export" | cut -d' ' -f1)
CFGSHA=$(sha256sum "$W/chal/comparator.json" | cut -d' ' -f1)   # the comparator pin is required with the challenge pin
P=$W/pkg; rsync -a --exclude tests --exclude pipeline --exclude 'review-*' --exclude __pycache__ "$FV/" "$P/"
pass=0; fail=0
run() {  # run NAME MODIFY(0|1) WANT_EXIT WANT_VERDICT
  local out=$W/out-$1
  "$P/bin/fastverify" - "$W/chal" "$out" --from-export "$GOOD" --preset sound --threads 4 --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" > "$W/log-$1" 2>&1 &
  local pid=$!
  if [ "$2" = 1 ]; then   # wait until the CS check has started, then change the stage script of the copy
    for _ in $(seq 1 600); do grep -q 'check sound started' "$out/logs/run.log" "$W/log-$1" 2>/dev/null && break; sleep 0.1; done
    sleep 1; echo "# modified during the run" >> "$P/check/sound/check-sound.sh"
  fi
  wait "$pid"; local rc=$?
  local v; v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["verdict"], r["exit"], "changed during the run" in (r.get("verdict_basis") or ""))' "$out/result.json" 2>/dev/null)
  set -- "$1" "$2" "$3" "$4" $v
  if [ "$rc" = "$3" ] && [ "${5:-}" = "$4" ] && [ "${6:-}" = "$3" ] && { [ "$2" = 0 ] || [ "${7:-}" = True ]; }; then
    echo "PASS $1: exit $rc verdict ${5:-}"; pass=$((pass+1))
  else echo "FAIL $1: expected exit $3 verdict $4, got exit $rc / '$v'"; fail=$((fail+1)); fi
}
run control 0 0 ACCEPTED
run stage-script-modified-during-run 1 2 ERROR
# SIGTERM while the trusted check runs: the orchestrator must stop every stage and record no verdict (on_signal: verdict ERROR,
# exit 2, 'interrupted'); kills the on_signal mutants that keep/force another verdict or exit code (PY-0128..0135)
cp "$FV/check/sound/check-sound.sh" "$P/check/sound/check-sound.sh"   # undo the modification of the previous case
out=$W/out-sigterm
"$P/bin/fastverify" - "$W/chal" "$out" --from-export "$GOOD" --preset sound --threads 4 --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" > "$W/log-sigterm" 2>&1 &
pid=$!
for _ in $(seq 1 600); do grep -q 'check sound started' "$W/log-sigterm" 2>/dev/null && break; sleep 0.1; done
sleep 1; kill -TERM "$pid"; wait "$pid"; rc=$?
v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["verdict"], r["exit"], bool(r.get("interrupted")))' "$out/result.json" 2>/dev/null)
if [ "$rc" = 2 ] && [ "$v" = "ERROR 2 True" ]; then echo "PASS sigterm-during-check: exit 2, verdict ERROR, interrupted recorded"; pass=$((pass+1))
else echo "FAIL sigterm-during-check: expected exit 2 + 'ERROR 2 True', got exit $rc / '$v'"; fail=$((fail+1)); fi
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]

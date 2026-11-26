#!/bin/bash
# orchestrator-cs-decline/test.sh [FV_ROOT] (a coverage gap of lib/fastverify.py decide_sound):
# check/sound/test/preset.sh never makes the trusted check CS give NO verdict, so mutants of decide_sound that map a CS no-verdict
# to ACCEPTED (PY-0076: `v = "DECLINED"` -> `v = "ACCEPTED"`) or to REJECTED (PY-0068) survive it.
# Case: export-in --preset sound on the pinned self-test GOOD export, in a PRIVATE package copy whose pinned second kernel is a
# wrapper (sha256 re-pinned in the copy's pins.env, exactly like check/sound/test/run.sh's fake()) that behaves like gruszka on
# the self-test exports and exits 2 ("cannot decide") on the judged export -> check-sound.sh DECLINES -> the orchestrator must
# report no verdict: exit 2, verdict DECLINED (never ACCEPTED, never REJECTED).
# Control: the same copy with a wrapper that just runs gruszka -> ACCEPTED exit 0.
set -u
FV=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
W=$(mktemp -d "${TMPDIR:-/tmp}/fv-csdecl.XXXXXX"); trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$FV/check/sound/pins.env"; }
GOOD=$(pin selftest_good); mkdir -p "$W/chal"; cp "$(pin selftest_challenge)" "$W/chal/challenge.export"; cp "$(pin selftest_comparator)" "$W/chal/comparator.json"
CSHA=$(sha256sum "$W/chal/challenge.export" | cut -d' ' -f1)
CFGSHA=$(sha256sum "$W/chal/comparator.json" | cut -d' ' -f1)   # the comparator pin is required with the challenge pin
pass=0; fail=0
mk() {  # mk NAME CODE -> package copy whose gruszka pin exits CODE on the judged export (CODE=pass: runs gruszka)
  local P=$W/pkg-$1
  rsync -a --exclude tests --exclude pipeline --exclude 'review-*' --exclude __pycache__ "$FV/" "$P/"
  if [ "$2" = pass ]; then printf '#!/bin/sh\nexec "%s" "$@"\n' "$(pin gruszka)" > "$P/fake-k2"
  else printf '#!/bin/sh\ncase "$1" in */solution.export) echo "fake second kernel: exit %s" >&2; exit %s;; esac\nexec "%s" "$@"\n' "$2" "$2" "$(pin gruszka)" > "$P/fake-k2"; fi
  chmod 755 "$P/fake-k2"; local s; s=$(sha256sum "$P/fake-k2" | cut -d' ' -f1)
  awk -v p="$P/fake-k2" -v s="$s" '$1=="PIN" && $2=="gruszka" {print "PIN gruszka " s " " p; next} {print}' "$FV/check/sound/pins.env" > "$P/check/sound/pins.env"
  echo "$P"
}
run() {  # run NAME PKG WANT_EXIT WANT_VERDICT
  local out=$W/out-$1
  "$2/bin/fastverify" - "$W/chal" "$out" --from-export "$GOOD" --preset sound --threads 4 --challenge-sha256 "$CSHA" --comparator-sha256 "$CFGSHA" > "$W/log-$1" 2>&1; local rc=$?
  local v; v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["verdict"], r["exit"], r["checks"]["sound"]["verdict"])' "$out/result.json" 2>/dev/null)
  set -- "$1" "$2" "$3" "$4" $v
  if [ "$rc" = "$3" ] && [ "${5:-}" = "$4" ] && [ "${6:-}" = "$3" ]; then echo "PASS $1: exit $rc verdict ${5:-} (CS ${7:-})"; pass=$((pass+1))
  else echo "FAIL $1: expected exit $3 verdict $4, got exit $rc / '$v' :: $(tail -1 "$W/log-$1" | cut -c1-200)"; fail=$((fail+1)); fi
}
run control "$(mk ok pass)" 0 ACCEPTED
run cs-no-verdict "$(mk decl 2)" 2 DECLINED
# the trusted check script dies from a signal on the judged run (e.g. the OOM killer): exit 137, no JSON -> the orchestrator's
# check() maps it to ERROR and decide_sound to no verdict (kills PY-0038: rc not in 0/1/2 -> "ACCEPTED")
K=$(mk killed pass); mv "$K/check/sound/check-sound.sh" "$K/check/sound/check-sound.real.sh"
printf '#!/bin/bash\n# test stub: takes the identity pins like the real script (--challenge-sha256 / --comparator-sha256)\ncase " $* " in *" --preflight "*) exec "$(dirname "$(readlink -f "$0")")/check-sound.real.sh" "$@";; esac\nkill -9 $$\n' > "$K/check/sound/check-sound.sh"; chmod 755 "$K/check/sound/check-sound.sh"
run cs-killed-by-signal "$K" 2 ERROR   # a judge that did not finish = ERROR (was DECLINED); never a verdict
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]

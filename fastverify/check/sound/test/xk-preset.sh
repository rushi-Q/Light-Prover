#!/bin/bash
# check/sound/test/xk-preset.sh — orchestrator test of the extra veto kernels (check-sound v2.3-H):
# bin/fastverify --preset sound in export-in mode on the pinned self-test exports (no build, ~2 min on a many-core host).
# Cases: default -> ACCEPTED with both extra kernels 'off' (opt-in); --extra-kernel con-leche -> 'con-leche: accepted' (also in
# soundness.trusted.check);
# --require-kernel nanoda -> ACCEPTED with 'nanoda: accepted'; --skip-extra-kernel con-leche -> 'con-leche: off';
# kernel-invalid export with a required kernel -> REJECTED by the two-kernel judge (extra kernels 'not consulted');
# --require-kernel X --skip-extra-kernel X, --require-kernel with --modulo-frontier, --extra-kernel without CS -> refused.
# Prints 'PASS|FAIL <case>: ...' rows and 'RESULT pass=N fail=M'; exit 0 iff all PASS.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); FV=$(cd "$H/../.." && pwd)/bin/fastverify
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$H/pins.env"; }
GOOD=$(pin selftest_good); CHALX=$(pin selftest_challenge); CFG=$(pin selftest_comparator)
mkdir -p "${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}" 2>/dev/null   # the parent of the work dir may not exist yet
W=$(mktemp -d "${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}/xkPreset-test.XXXXXX") || exit 2
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
mkdir -p "$W/chal"; cp "$CHALX" "$W/chal/challenge.export"; cp "$CFG" "$W/chal/comparator.json"
sha256sum "$W/chal/challenge.export" | sed 's#  .*#  challenge.export#' > "$W/chal/challenge.export.sha256"
CSHA=$(cut -d' ' -f1 "$W/chal/challenge.export.sha256")
sed 's/^{"app":{"arg":518,"fn":526},"ie":527}$/{"app":{"arg":512,"fn":526},"ie":527}/' "$GOOD" > "$W/kernel-bad.export"
fails=0; passes=0; n=0
run() {  # run NAME WANT_EXIT WANT_VERDICT 'PYTHON CONDITION ON r (result.json) OR -' EXPORT [ARGS...]
  local name=$1 want=$2 wv=$3 cond=$4 e=$5; shift 5; n=$((n+1))
  local out=$W/out$n got chk
  "$FV" - "$W/chal" "$out" --from-export "$e" --preset sound --threads 4 "$@" > "$W/log$n" 2>&1; got=$?
  if [ "$wv" = ARGERROR ]; then
    if [ "$got" = 2 ] && [ ! -f "$out/result.json" ] && grep -q "error:" "$W/log$n"; then echo "PASS $name: refused (exit 2): $(grep -m1 'error:' "$W/log$n" | cut -c1-200)"; passes=$((passes+1))
    else echo "FAIL $name: expected an argument error, got exit $got :: $(tail -2 "$W/log$n" | tr '\n' ' ' | cut -c1-300)"; fails=$((fails+1)); fi
    return
  fi
  chk=$(python3 -I -c '
import json, sys
r = json.load(open(sys.argv[1])); cond = sys.argv[3]
ok = r["verdict"] == sys.argv[2] and r.get("exit") == int(sys.argv[4]) and r.get("trust") == "sound"
if cond != "-":
    ok = ok and bool(eval(cond, {"r": r}))
print(("OK " if ok else "BAD ") + r["verdict"] + " | " + str(r.get("extra_kernels")))' "$out/result.json" "$wv" "$cond" "$got" 2>&1)
  if [ "$got" = "$want" ] && [ "${chk%% *}" = OK ]; then echo "PASS $name: exit $got ${chk#OK }" | cut -c1-260; passes=$((passes+1))
  else echo "FAIL $name: expected exit $want $wv [$cond], got exit $got :: $chk :: $(tail -2 "$W/log$n" | tr '\n' ' ' | cut -c1-300)"; fails=$((fails+1)); fi
}
P=(--challenge-sha256 "$CSHA" --comparator-sha256 "$(sha256sum "$W/chal/comparator.json" | cut -d' ' -f1)")   # pin pair
run default-both-off 0 ACCEPTED 'r["extra_kernels"].startswith("con-leche: off") and r["checks"]["sound"]["stage"]["extra_kernels"]["nanoda"]["status"] == "off"' "$GOOD" "${P[@]}"
run extra-con-leche-accepted 0 ACCEPTED '"con-leche: accepted" in r["extra_kernels"] and r["soundness"]["trusted"]["check"]["extra_kernels"]["con-leche"]["status"] == "accepted" and r["checks"]["sound"]["stage"]["extra_kernels"]["con-leche"]["mode"] == "optional"' "$GOOD" "${P[@]}" --extra-kernel con-leche
run require-nanoda-accepted 0 ACCEPTED '"nanoda: accepted" in r["extra_kernels"] and r["checks"]["sound"]["stage"]["extra_kernels"]["nanoda"]["mode"] == "required"' "$GOOD" "${P[@]}" --require-kernel nanoda
run extra-nanoda-optional 0 ACCEPTED 'r["checks"]["sound"]["stage"]["extra_kernels"]["nanoda"]["mode"] == "optional"' "$GOOD" "${P[@]}" --extra-kernel nanoda
run skip-con-leche 0 ACCEPTED '"con-leche: off" in r["extra_kernels"]' "$GOOD" "${P[@]}" --skip-extra-kernel con-leche
run kernel-bad-required-rejected 1 REJECTED '"not consulted" in r["extra_kernels"]' "$W/kernel-bad.export" "${P[@]}" --require-kernel con-leche
run require-and-skip-refused 2 ARGERROR - "$GOOD" "${P[@]}" --require-kernel nanoda --skip-extra-kernel nanoda
run require-with-frontier-refused 2 ARGERROR - "$GOOD" "${P[@]}" --require-kernel con-leche --modulo-frontier
run extra-kernel-unknown-refused 2 ARGERROR - "$GOOD" "${P[@]}" --extra-kernel con-ron
# the orchestrator's CS preflight sees the extra-kernel options: a light package copy whose nanoda pin
# points to a missing file -> --require-kernel nanoda --preflight-only fails (exit 2) before any build; --extra-kernel passes
PK=$W/pkgcopy/fastverify; mkdir -p "$PK/check"; R0=$(cd "$H/../.." && pwd)
cp -r "$R0/bin" "$R0/lib" "$R0/config" "$R0/toolchains" "$PK/"; cp -r "$H" "$PK/check/sound"; [ -d "$R0/check/xversion" ] && cp -r "$R0/check/xversion" "$PK/check/"
sed -i "s#^PIN nanoda \([0-9a-f]*\) .*#PIN nanoda \1 $W/no-such-nanoda#" "$PK/check/sound/pins.env"
pf() {  # pf NAME WANT_EXIT GREP_TEXT ARGS...
  local name=$1 want=$2 txt=$3; shift 3; rm -rf "$W/pfout"
  "$PK/bin/fastverify" - "$W/chal" "$W/pfout" --from-export "$GOOD" --preset sound --threads 4 "${P[@]}" "$@" --preflight-only > "$W/pf.log" 2>&1; local got=$?
  if [ "$got" = "$want" ] && grep -q -- "$txt" "$W/pf.log"; then echo "PASS $name: exit $got"; passes=$((passes+1))
  else echo "FAIL $name: want exit $want and '$txt', got exit $got :: $(tail -3 "$W/pf.log" | tr '\n' ' ' | cut -c1-300)"; fails=$((fails+1)); fi
}
pf preflight-require-missing-nanoda-fails 2 "required extra kernel nanoda" --require-kernel nanoda
pf preflight-optional-missing-nanoda-ok 0 "preflight OK" --extra-kernel nanoda
echo "RESULT pass=$passes fail=$fails"
[ "$fails" = 0 ]

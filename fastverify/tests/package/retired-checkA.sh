#!/bin/bash
# tests/package/retired-checkA.sh [WORKDIR] -- the legacy judge check A (C1 = checkA, C2 = checkA_patched) was retired.
# Every name that selected it must be REFUSED (exit 2, nothing written to OUT) with a message that names the
# replacement (--preset sound / sound-auto), never silently mapped to another check: the presets fast-exact and default,
# a run without --preset and without --check (the old implicit 'default'), --check C1 / C2 / fast / both (also inside a
# list), --fast-checks, --fast-policy checkA and --unsafe nanoda-c07. Controls: the remaining presets and options still
# parse and reach the preflight. No Lean build; ~1 min (the controls run --preflight-only). Prints 'PASS|FAIL <case>: ...'
# rows and 'RESULT pass=N fail=M'; exit 0 iff all PASS.
set -u
T=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=$(cd "$T/../.." && pwd); FV=$PKG/bin/fastverify
base=${1:-${CHECK_SOUND_TEST_DIR:-${TMPDIR:-/tmp}}}; [ -w "$base" ] || base=${TMPDIR:-/tmp}   # no kernel runs in W
W=$(mktemp -d "$base/retired-checkA.XXXXXX") || exit 2
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$PKG/check/sound/pins.env"; }
CH=$W/chal; mkdir -p "$CH"; cp "$(pin selftest_challenge)" "$CH/challenge.export"; cp "$(pin selftest_comparator)" "$CH/comparator.json"
GOOD=$(pin selftest_good)
# the pin pair is required in sound / notary mode with a given challenge export (the comparator pin is mandatory)
PINS=(--challenge-sha256 "$(sha256sum "$CH/challenge.export" | cut -d' ' -f1)" --comparator-sha256 "$(sha256sum "$CH/comparator.json" | cut -d' ' -f1)")
passes=0; fails=0; n=0
refused() {  # refused NAME ARGS... : exit 2, no OUT, message says 'retired' and names --preset sound
  local name=$1; shift; n=$((n+1)); local out=$W/out$n
  "$FV" - "$CH" "$out" --from-export "$GOOD" --threads 2 "$@" > "$W/log$n" 2>&1; local rc=$?
  if [ $rc = 2 ] && [ ! -e "$out" ] && grep -q "retired in v0.1" "$W/log$n" && grep -q -- "--preset sound" "$W/log$n"; then
    echo "PASS $name: refused (exit 2, no OUT): $(grep -m1 -o 'error: .*' "$W/log$n" | cut -c1-140)"; passes=$((passes+1))
  else
    echo "FAIL $name: exit $rc, OUT $([ -e "$out" ] && echo exists || echo absent): $(tail -2 "$W/log$n" | tr '\n' ' ' | cut -c1-300)"; fails=$((fails+1))
  fi
}
parses() {  # parses NAME ARGS... : a remaining option: no retirement refusal, the preflight runs
  local name=$1; shift; n=$((n+1)); local out=$W/out$n
  "$FV" - "$CH" "$out" --from-export "$GOOD" --threads 2 --preflight-only "${PINS[@]}" "$@" > "$W/log$n" 2>&1; local rc=$?
  if ! grep -q "retired" "$W/log$n" && grep -q "^fastverify: preflight" "$W/log$n"; then
    echo "PASS $name: accepted by the option parser, preflight ran (exit $rc: $(grep -m1 '^fastverify: preflight' "$W/log$n" | cut -c1-80))"; passes=$((passes+1))
  else
    echo "FAIL $name: exit $rc: $(tail -2 "$W/log$n" | tr '\n' ' ' | cut -c1-300)"; fails=$((fails+1))
  fi
}
refused preset-fast-exact --preset fast-exact
refused preset-default --preset default
refused no-preset-no-check
refused check-C1 --check C1
refused check-C2 --check C2
refused check-CS-plus-C1 --check CS,C1
refused check-C3-plus-C2 --preset sound --check C3,C2
refused check-alias-fast --check fast
refused check-alias-both --check both
refused fast-checks-checkA --check C3 --fast-checks checkA
refused fast-checks-checkB --check C3 --fast-checks checkB
refused fast-policy-checkA --check C3 --fast-policy checkA
refused unsafe-nanoda-c07 --check C3 --unsafe nanoda-c07
refused unsafe-nanoda-c07-in-list --preset fastest --unsafe ignore-order,nanoda-c07
parses preset-sound --preset sound
parses preset-sound-auto --preset sound-auto
parses preset-notary --preset notary --experimental   # the notary check is EXPERIMENTAL in v0.1
parses preset-reference --preset reference
parses preset-fastest --preset fastest
parses check-C3-C0-without-preset --check C3,C0
parses check-official-alias --check official --fast-policy primary
echo "RESULT pass=$passes fail=$fails"
[ "$fails" = 0 ]

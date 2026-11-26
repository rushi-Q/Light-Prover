#!/bin/bash
# tests/ultralowmem-wiring/run.sh [FV_ROOT]: the ULTRA-low-memory judge
# check/lowmem/check-sound-ultralowmem.sh shares the wiring of check-sound-lowmem.sh, but its only suite (tests/ultralowmem-check) has
# none of tests/lowmem-check's option / integrity / adversarial cases. This test runs THIS package's tests/lowmem-check/test.sh
# against the ultra-low-memory judge (a private copy with CS_LM and PINS switched, made at run time, so it follows tests/lowmem-check), and
# ignores only the 5 cases that need --pins / --hide, which this judge does not support (plus the --pins confinement row).
# PASS iff every other tests/lowmem-check case passes on check-sound-ultralowmem.sh.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${1:-$(cd "$H/../.." && pwd)}
W=$(mktemp -d "${TMPDIR:-/tmp}/ultralowmem-wiring.XXXXXX") || { echo "FAIL setup: mktemp"; echo "RESULT pass=0 fail=1"; exit 1; }
trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
LOWMEM_TEST=$FV/tests/lowmem-check/test.sh
[ -f "$LOWMEM_TEST" ] || { echo "FAIL setup: $LOWMEM_TEST missing"; echo "RESULT pass=0 fail=1"; exit 1; }
mkdir -p "$W/tests/lowmem-check-u"
# the copy must resolve FV to THIS package: lowmem-check computes FV=$HERE/../.. -> point HERE's parent chain at a shim tree
sed -e 's|^CS_LM="$FV/check/lowmem/check-sound-lowmem.sh"$|CS_LM="$FV/check/lowmem/check-sound-ultralowmem.sh"|' \
    -e 's|^PINS="$FV/check/lowmem/pins.env"$|PINS="$FV/check/lowmem/pins-ultralowmem.env"|' \
    -e 's|^FV=.*$|FV='"$FV"'|' "$LOWMEM_TEST" > "$W/tests/lowmem-check-u/test.sh"
grep -q '^CS_LM="$FV/check/lowmem/check-sound-ultralowmem.sh"$' "$W/tests/lowmem-check-u/test.sh" && grep -q '^PINS="$FV/check/lowmem/pins-ultralowmem.env"$' "$W/tests/lowmem-check-u/test.sh" \
  || { echo "FAIL setup: tests/lowmem-check/test.sh no longer has the CS_LM= / PINS= lines this wrapper switches"; echo "RESULT pass=0 fail=1"; exit 1; }
SKIP='^FAIL (cs-lowmem-437-preflight-and-selftest|cs-lowmem-v12-hide-and-invalid-hide-guard|cs-lowmem-symlink-pins-icache-guard|cs-lowmem-pins-outside-package-refused|cs-lowmem-437-nonsorried-challenge-def-rejected):'   # F2: + the --pins confinement row (this judge has no --pins: DECLINED 'unknown argument')
out=$(TMPDIR=$W bash "$W/tests/lowmem-check-u/test.sh" 2>&1)
printf '%s\n' "$out" | grep -E '^(PASS|FAIL) ' | sed -E "s/$SKIP/SKIP (needs pins-437 or --hide) \\1:/"
pass=$(printf '%s\n' "$out" | grep -c '^PASS ')
fail=$(printf '%s\n' "$out" | grep -E '^FAIL ' | grep -v -c -E "$SKIP")
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ] && [ "$pass" -gt 0 ]

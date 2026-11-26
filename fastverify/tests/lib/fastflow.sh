#!/bin/bash
# fastflow.sh PRISTINE WORK CHALLENGE_EXPORT [pchk|dual]  -> prints "FAST: <verdict>" ; exit 0 iff ACCEPTED, 1 otherwise,
#                                                            3 = the package entry point is missing (test SKIP)
# Drop-in replacement for the original fastflow.sh harness (same signature and output lines, so every repro.sh under x/ and
# the original output parser work unchanged), but the FAST flow is now the delivered package:
#     $FV_BIN PRISTINE CHALLENGE_DIR WORK/out --check $FV_CHECK --threads $EVAL_THREADS
# FV_BIN   (default: <package>/bin/fastverify)     FV_ARGS (package options; default '--check C3,C0')   CHALLENGE_DIR = dirname CHALLENGE_EXPORT
# (previously the default was '--check both' = C1,C3,C0; C1 = check A was retired, 'both' is refused since)
# With --check C3,C0 the package reports the official comparator's verdict on ITS export plus the fast check's verdict; the
# test's FAST outcome is ACCEPTED if either accepts (lib/result.py), 2 if DECLINED, 4 if ERROR.
# The 4th argument (pchk|dual, the old fast-check selector) is ignored: the package decides which fast checks run and must
# fall back to the official path whenever one declines; the test compares the package's FINAL verdict with the official one.
# FV_FAST=deployed runs the original harness (fastflow.deployed.sh next to the symlink) = the deployed fast flow.
# For repros that look at the fast export directly, the package's export is hard-linked (or copied) to WORK/run/solution.export.
{ # whole script parsed before it runs (safe against edits while running)
set -u
# FV_FAST=deployed: run the original harness instead (the deployed fast flow) to show the original divergence
if [ "${FV_FAST:-}" = deployed ]; then exec bash "$(dirname "$0")/fastflow.deployed.sh" "$@"; fi
H=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd)
FVROOT=${FV_ROOT:-$(cd "$H/../.." && pwd)}
FVB=${FV_BIN:-$FVROOT/bin/fastverify}
P=$(readlink -f "$1"); W=$2; CE=$(readlink -f "$3")
CD=$(dirname "$CE")
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
if [ ! -x "$FVB" ]; then echo "FAST: SKIPPED (package entry point $FVB missing)"; exit 3; fi
T=${EVAL_THREADS:-16}
# dependencies: projects with packages in their lake-manifest get the trusted RH workspace (pinned Mathlib cache), exactly
# what the original officialflow.sh copies into the official build (FV_PACKAGES overrides)
PK=()
if python3 -I -c 'import json,sys; sys.exit(0 if json.load(open(sys.argv[1])).get("packages") else 1)' "$P/lake-manifest.json" 2>/dev/null; then
  PK=(--packages "${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}"); fi
# FV_ARGS = the package options under test (menu: --preset/--build/--export/--check/--unsafe); default --check C3,C0
read -r -a FA <<< "${FV_ARGS:---check ${FV_CHECK:-C3,C0}}"
echo "fast: $FVB $P $CD $W/out ${FA[*]} --threads $T ${PK[*]}"
# the package must not depend on the caller's environment: run it with a minimal one (the tests also run it polluted, 016)
t0=$(date +%s)
env -i HOME="$HOME" PATH=/usr/local/bin:/usr/bin:/bin USER="${USER:-}" LANG=C.UTF-8 ${FV_EXTRA_ENV:-} \
  timeout -k 30 "${FV_E2E_TIMEOUT:-3600}" "$FVB" "$P" "$CD" "$W/out" "${FA[@]}" --threads "$T" "${PK[@]}" > "$W/fastverify.log" 2>&1; rc=$?
t1=$(date +%s)
tail -n 15 "$W/fastverify.log" | cut -c1-300 | sed 's/^/fast: | /'
R=$W/out/result.json
if [ $rc = 124 ] || [ $rc = 137 ]; then echo "FAST: ERROR (no verdict: bin/fastverify did not finish within ${FV_E2E_TIMEOUT:-3600} s)"; exit 4; fi
if [ ! -s "$R" ]; then echo "FAST: ERROR (no result.json, fastverify rc=$rc, $((t1-t0)) s)"; exit 4; fi
python3 -I "$H/result.py" "$R" "$W/out" "$W/run/solution.export" "$rc" "$((t1-t0))"
exit $?
}

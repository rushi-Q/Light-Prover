#!/bin/bash
# test 036 (kind component/fail-closed: degrade.py runs bin/fastverify from COPIES of the package with one broken component)
# finding: 036 pipeline silently degrades when the fast toolchain/exporter cannot run: every module built 3x, official fallbacks, exit 0
# PASS iff the intact package gives the official verdict, every broken copy refuses (or gives the official verdict without
# using the broken component), and a broken OFFICIAL toolchain pin always makes the package refuse.
{ # whole script parsed before it runs (safe against edits while running)
set -u
TD=$(cd "$(dirname "$0")" && pwd); W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/036.XXXXXX")}
mkdir -p "$(dirname "$W")"; W=$(readlink -f "$(dirname "$W")")/$(basename "$W"); rm -rf "$W"
case "${FV_BIN:-}" in *standin*) FVS=1;; *) FVS=0;; esac
if [ "${FV_FAST:-}" = deployed ] || [ $FVS = 1 ]; then echo "=== RESULT case=all official=- fast=3" > "$W.log"
else python3 -I "$TD/degrade.py" "$W" > "$W.log" 2>&1; fi
python3 -I "$TD/../lib/parse.py" 036 "$W.log" | tee "$W.tsv"
[ -n "${KEEP_WORK:-}" ] || { chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"; }
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}

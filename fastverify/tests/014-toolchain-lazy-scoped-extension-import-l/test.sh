#!/bin/bash
# test 014 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 014 toolchain lazy scoped-extension import leaks marker and thunk through public State fields: different export, segfault
# PASS iff (e2e) for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
# The liveness case (official lake build never terminates; bounded to 300 s) only runs with --heavy (FV_HEAVY=1).
{ # whole script parsed before it runs (safe against edits while running)
S="e2e/repro-e2e.sh"; [ "${FV_HEAVY:-0}" = 1 ] && S="$S e2e/repro-e2e-liveness.sh"
export FV_E2E_TIMEOUT=${FV_E2E_TIMEOUT:-900}   # liveness case: the official build is bounded at 300 s; no verdict after 900 s
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/014.XXXXXX")}; T=$(dirname "$0")/../lib
# part 1: the end-to-end repro (package as FAST flow); part 2: the toolchain component rows for 014 (tests/toolchain/run.sh)
bash "$T/xrepro.sh" "$(dirname "$0")" "$W.e2e" "$S"; r1=$?
bash "$T/component.sh" 014 "$W.tc" "$(dirname "$0")/../toolchain/run.sh"; r2=$?
cat "$W.e2e.tsv" "$W.tc.tsv" > "$W.tsv" 2>/dev/null; cat "$W.e2e.log" "$W.tc.log" > "$W.log" 2>/dev/null
[ $r1 = 0 ] && [ $r2 = 0 ]
exit $?
}

#!/bin/bash
# test 020 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 020 fast toolchain core library differs from official: 114 extra, 14 missing, 38 changed constants visible to user code
# PASS iff (e2e) for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
{ # whole script parsed before it runs (safe against edits while running)
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/020.XXXXXX")}; T=$(dirname "$0")/../lib
# part 1: the end-to-end repro (package as FAST flow); part 2: the toolchain component rows for 020 (tests/toolchain/run.sh)
bash "$T/xrepro.sh" "$(dirname "$0")" "$W.e2e"; r1=$?
bash "$T/component.sh" 020 "$W.tc" "$(dirname "$0")/../toolchain/run.sh"; r2=$?
cat "$W.e2e.tsv" "$W.tc.tsv" > "$W.tsv" 2>/dev/null; cat "$W.e2e.log" "$W.tc.log" > "$W.log" 2>/dev/null
[ $r1 = 0 ] && [ $r2 = 0 ]
exit $?
}

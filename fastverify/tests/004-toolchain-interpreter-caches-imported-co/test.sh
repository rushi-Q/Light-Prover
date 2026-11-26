#!/bin/bash
# test 004 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 004 toolchain interpreter caches imported constants per thread: different and nondeterministic exports, accepts what official rejects
# PASS iff (e2e) for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
{ # whole script parsed before it runs (safe against edits while running)
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/004.XXXXXX")}; T=$(dirname "$0")/../lib
# part 1: the end-to-end repro (package as FAST flow); part 2: the toolchain component rows for 004 (tests/toolchain/run.sh)
bash "$T/xrepro.sh" "$(dirname "$0")" "$W.e2e"; r1=$?
bash "$T/component.sh" 004 "$W.tc" "$(dirname "$0")/../toolchain/run.sh"; r2=$?
cat "$W.e2e.tsv" "$W.tc.tsv" > "$W.tsv" 2>/dev/null; cat "$W.e2e.log" "$W.tc.log" > "$W.log" 2>/dev/null
[ $r1 = 0 ] && [ $r2 = 0 ]
exit $?
}

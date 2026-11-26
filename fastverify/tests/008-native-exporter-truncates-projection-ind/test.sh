#!/bin/bash
# test 008 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 008 native exporter truncates projection index to 32 bits (CRITICAL-EXPORT -> CRITICAL-ACCEPT with skipKernelTC build)
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
{ # whole script parsed before it runs (safe against edits while running)
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/008.XXXXXX")}; T=$(dirname "$0")/../lib
# part 1: the end-to-end repro (package as FAST flow); part 2: exporter component cases (ECASES: export.sh vs official)
bash "$T/xrepro.sh" "$(dirname "$0")" "$W.e2e"; r1=$?
bash "$T/exportcases.sh" "$(dirname "$0")" "$W.ex"; r2=$?
cat "$W.e2e.tsv" "$W.ex.tsv" > "$W.tsv" 2>/dev/null; cat "$W.e2e.log" "$W.ex.log" > "$W.log" 2>/dev/null
[ $r1 = 0 ] && [ $r2 = 0 ]
exit $?
}

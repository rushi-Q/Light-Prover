#!/bin/bash
# test 022 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 022 -Dlinter.all=false (R5) changes the build verdict: warningAsError / #guard_msgs projects rejected officially, accepted fast
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/022.XXXXXX")}"

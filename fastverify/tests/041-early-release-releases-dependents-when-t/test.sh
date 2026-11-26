#!/bin/bash
# test 041 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 041 EARLY_RELEASE releases dependents when the exported .olean part exists, but module-system files write .olean.server/.olean.private seconds later -
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/041.XXXXXX")}"

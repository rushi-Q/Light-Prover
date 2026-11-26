#!/bin/bash
# test 066 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 066 official lake build reuses shipped .lake/build artifacts whose trace matches (olean from another source); the fast pipeline rebuilds from src: ver
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
export OFFICIALFLOW=${OFFICIALFLOW:-officialflow-clean.sh}   # reference = lake build of the SOURCES (shipped .lake/build removed), the fix for 066
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/066.XXXXXX")}"

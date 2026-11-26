#!/bin/bash
# heavy (Mathlib-scale inputs; run with --heavy)
# test 015 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 015 native package code (--load-dynlib) changes heartbeat accounting: official build times out, fast build passes
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/015.XXXXXX")}"

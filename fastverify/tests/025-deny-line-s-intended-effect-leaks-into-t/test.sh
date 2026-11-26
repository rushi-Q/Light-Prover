#!/bin/bash
# test 025 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 025 deny line's intended effect leaks into the .olean: the module's exported library-suggestion data (SineQuaNon triggers, symbol frequencies) is empt
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/025.XXXXXX")}"

#!/bin/bash
# test 070 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 070 lakefile buildType=debug (debugAssertions) and Lake arg precedence not reproduced by the pipeline or by the 011 mkargs fix
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/070.XXXXXX")}"

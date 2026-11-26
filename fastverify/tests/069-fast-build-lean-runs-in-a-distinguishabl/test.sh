#!/bin/bash
# test 069 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 069 fast build lean runs in a distinguishable environment (TOOLWRAP_LOG, HOME=/tmp/home, pkglib on LEAN_PATH): elaboration-time code observes it, offi
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/069.XXXXXX")}"

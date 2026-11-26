#!/bin/bash
# test 023 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 023 deny-eof line is elaborated in the module's EOF scope: a module ending inside a namespace that defines Lean.modifyEnv hijacks it (code runs only i
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/023.XXXXXX")}"

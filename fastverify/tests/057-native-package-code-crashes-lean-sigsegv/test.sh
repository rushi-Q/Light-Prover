#!/bin/bash
# heavy (Mathlib-scale inputs; run with --heavy)
# test 057 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 057 native package code crashes lean (SIGSEGV) on module-system files importing Mathlib; pipeline masks it by retrying and switches natives off after 
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/057.XXXXXX")}"

#!/bin/bash
# test 043 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 043 pipeline runs lean without Lake's --setup: the module's package id (modPkgExt, stored in every .olean) is unset, observable via public Environment
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/043.XXXXXX")}"

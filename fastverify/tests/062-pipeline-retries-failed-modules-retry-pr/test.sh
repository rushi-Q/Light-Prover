#!/bin/bash
# test 062 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 062 pipeline retries failed modules (RETRY_PRISTINE/RETRY_OFFICIAL/native): a module that fails its first or a nondeterministic build is accepted; off
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/062.XXXXXX")}"

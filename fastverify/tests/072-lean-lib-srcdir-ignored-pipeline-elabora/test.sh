#!/bin/bash
# test 072 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 072 Lake source layout ignored (lean_lib srcDir, package srcDir, lakefile.lean precedence over lakefile.toml): pipeline elaborates a decoy src/Main.le
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/072.XXXXXX")}"

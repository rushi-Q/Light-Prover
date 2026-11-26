#!/bin/bash
# test 048 (kind component/toolchain: tests/toolchain/run.sh = lib/toolchain.py refusals + regress_toolchain.sh
#   with the toolchain the package resolves; shared by 004 014 020 031 037 040 046 048 050 052 061, run once per suite run)
# finding: 048 fast lean needs ~7 GiB more address space importing Mathlib: failed to create thread under RLIMIT_AS where official works
# PASS iff every row for this finding is SAME/PASS (deployed toolchain: DIFFERENT).
export FV_COMPONENT_ALL=1   # not in the toolchain regression list: holds by construction (package toolchain == official tree, byte-verified)
exec "$(dirname "$0")/../lib/component.sh" 048 "${1:-$(mktemp -d "${TMPDIR:-/tmp}/048.XXXXXX")}" "$(dirname "$0")/../toolchain/run.sh"

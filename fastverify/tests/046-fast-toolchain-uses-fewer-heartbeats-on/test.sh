#!/bin/bash
# test 046 (kind component/toolchain: tests/toolchain/run.sh = lib/toolchain.py refusals + regress_toolchain.sh
#   with the toolchain the package resolves; shared by 004 014 020 031 037 040 046 048 050 052 061, run once per suite run)
# finding: 046 fast toolchain uses fewer heartbeats on ordinary Mathlib tactic proofs: official timeout, fast build succeeds
# PASS iff every row for this finding is SAME/PASS (deployed toolchain: DIFFERENT).
export FV_COMPONENT_ALL=1   # not in the toolchain regression list: holds by construction (package toolchain == official tree, byte-verified)
exec "$(dirname "$0")/../lib/component.sh" 046 "${1:-$(mktemp -d "${TMPDIR:-/tmp}/046.XXXXXX")}" "$(dirname "$0")/../toolchain/run.sh"

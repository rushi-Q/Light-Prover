#!/bin/bash
# test 037 (kind component/toolchain: tests/toolchain/run.sh = lib/toolchain.py refusals + regress_toolchain.sh
#   with the toolchain the package resolves; shared by 004 014 020 031 037 040 046 048 050 052 061, run once per suite run)
# finding: 037 fast toolchain built with CHECK_OLEAN_VERSION=OFF: imports oleans of any Lean version
# PASS iff every row for this finding is SAME/PASS (deployed toolchain: DIFFERENT).
exec "$(dirname "$0")/../lib/component.sh" 037 "${1:-$(mktemp -d "${TMPDIR:-/tmp}/037.XXXXXX")}" "$(dirname "$0")/../toolchain/run.sh"

#!/bin/bash
# test 050 (kind component/toolchain: tests/toolchain/run.sh = lib/toolchain.py refusals + regress_toolchain.sh
#   with the toolchain the package resolves; shared by 004 014 020 031 037 040 046 048 050 052 061, run once per suite run)
# finding: 050 stack band: deeply nested source overflows the official lean stack but not the fast one (official crash, fast accepts)
# PASS iff every row for this finding is SAME/PASS (deployed toolchain: DIFFERENT).
exec "$(dirname "$0")/../lib/component.sh" 050 "${1:-$(mktemp -d "${TMPDIR:-/tmp}/050.XXXXXX")}" "$(dirname "$0")/../toolchain/run.sh"

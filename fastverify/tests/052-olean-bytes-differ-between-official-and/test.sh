#!/bin/bash
# test 052 (kind component/toolchain: tests/toolchain/run.sh = lib/toolchain.py refusals + regress_toolchain.sh
#   with the toolchain the package resolves; shared by 004 014 020 031 037 040 046 048 050 052 061, run once per suite run)
# finding: 052 olean bytes differ between official and fast toolchain for 36 of 3033 Lean test modules (byte-identical claim does not hold)
# PASS iff every row for this finding is SAME/PASS (deployed toolchain: DIFFERENT).
exec "$(dirname "$0")/../lib/component.sh" 052 "${1:-$(mktemp -d "${TMPDIR:-/tmp}/052.XXXXXX")}" "$(dirname "$0")/../toolchain/run.sh"

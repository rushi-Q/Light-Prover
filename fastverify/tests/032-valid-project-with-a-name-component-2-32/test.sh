#!/bin/bash
# test 032 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 032 valid project with a name component >= 2^32: official comparator rejects (nanoda u32 names), fast check B accepts
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/032.XXXXXX")}"

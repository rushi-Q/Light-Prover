#!/bin/bash
# heavy (slow official / generated inputs; run with --heavy)
# test 051 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 051 deep definition chain: official replay walk runs out of stack (comparator rejects), pchk walk does not (accepts); check B accepts deeper chains
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/051.XXXXXX")}"

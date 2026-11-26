#!/bin/bash
# test 024 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 024 check B lacks the nanoda leg: export with a duplicate expr node -> official comparator rejects (nanoda panic), fast B accepts
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/024.XXXXXX")}"

#!/bin/bash
# test 068 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 068 check B rejects a forged isReflexive/numNested flag on a solution-only inductive that the official comparator ignores
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/068.XXXXXX")}"

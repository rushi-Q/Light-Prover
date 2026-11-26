#!/bin/bash
# test 045 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 045 nanoda (official and C07) rejects definitions of reducibility height >= 65536 (u16): official comparator rejects a valid generated-definition proj
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/045.XXXXXX")}"

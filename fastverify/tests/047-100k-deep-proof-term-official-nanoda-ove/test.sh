#!/bin/bash
# test 047 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 047 100k-deep proof term: official nanoda overflows its 16 MiB stack (official comparator rejects), check B accepts
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/047.XXXXXX")}"

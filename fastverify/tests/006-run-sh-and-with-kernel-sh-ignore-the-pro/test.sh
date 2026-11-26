#!/bin/bash
# test 006 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 006 run.sh and with-kernel.sh ignore the project comparator config (hard-coded RH theorem names, axioms, definition_names)
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/006.XXXXXX")}"

#!/bin/bash
# test 002 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 002 run.sh and with-kernel.sh path/no-challenge bypass skips statement+axiom comparison and 2nd kernel
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/002.XXXXXX")}"

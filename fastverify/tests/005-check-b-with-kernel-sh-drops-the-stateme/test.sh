#!/bin/bash
# test 005 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 005 check B with-kernel.sh drops the statement/axiom comparison when the export path contains /arena/suite/ or /inputs/suitex/
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/005.XXXXXX")}"

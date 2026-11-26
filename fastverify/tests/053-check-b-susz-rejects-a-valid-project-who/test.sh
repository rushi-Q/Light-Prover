#!/bin/bash
# test 053 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 053 check B susz rejects a valid project whose helper theorem has the anonymous name
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/053.XXXXXX")}"

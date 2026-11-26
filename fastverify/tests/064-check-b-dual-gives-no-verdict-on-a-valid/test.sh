#!/bin/bash
# heavy (slow official / generated inputs; run with --heavy)
# test 064 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 064 check B dual gives no verdict on a valid heavy `decide +kernel` proof: nl-fast declines (declaration arena/work budget exhausted) where the offici
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/064.XXXXXX")}"

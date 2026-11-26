#!/bin/bash
# test 065 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 065 check B dual gives no verdict on a valid project whose proof contains a Nat literal with more than 65536 digits
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/065.XXXXXX")}"

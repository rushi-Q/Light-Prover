#!/bin/bash
# test 042 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 042 pchk fails on every input under an address-space limit (RLIMIT_AS): one 1 GiB-stack thread per CPU
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/042.XXXXXX")}"

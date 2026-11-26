#!/bin/bash
# heavy (slow official / generated inputs; run with --heavy)
# test 029 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 029 Nat.shiftRight by a huge literal: official comparator with nanoda rejects (nanoda aborts after ~6 min), pchk rejects, check B accepts in <1 s
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/029.XXXXXX")}"

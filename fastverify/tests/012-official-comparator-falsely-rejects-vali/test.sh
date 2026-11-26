#!/bin/bash
# test 012 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 012 official comparator falsely rejects valid string-literal proofs (replay order) but fast check B accepts them
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/012.XXXXXX")}"

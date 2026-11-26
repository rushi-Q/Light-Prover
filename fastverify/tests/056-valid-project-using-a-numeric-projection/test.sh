#!/bin/bash
# test 056 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 056 valid project using a numeric projection on an indexed inductive family: official nanoda (and C07) panic -> official comparator rejects; check B s
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/056.XXXXXX")}"

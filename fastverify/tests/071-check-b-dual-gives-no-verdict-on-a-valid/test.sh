#!/bin/bash
# test 071 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 071 check B gives no verdict on a valid project with a deep binder nest: nl-fast declines bound variable index >= 32,766 (dual exit 2), gruszka declin
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/071.XXXXXX")}"

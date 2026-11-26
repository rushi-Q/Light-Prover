#!/bin/bash
# test 055 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 055 check B gruszka falsely rejects a valid nested inductive whose container takes a type-constructor parameter (BaseFoo Option V) or a function-typed
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/055.XXXXXX")}"

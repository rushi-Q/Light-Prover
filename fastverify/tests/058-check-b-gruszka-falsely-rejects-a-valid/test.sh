#!/bin/bash
# test 058 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 058 check B gruszka falsely rejects a valid reflexive nested inductive (inductive T | c0 : List (Nat -> T) -> T): isReflexive computed on the uninstan
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/058.XXXXXX")}"

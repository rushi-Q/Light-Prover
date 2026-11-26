#!/bin/bash
# test 016 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 016 fast wrappers take verdict-relevant settings from inherited environment variables (KC_AXIOMS, KC_THEOREMS, CCMP_LEANCHECKER, GRUSZKA, SUSZ, LEAN_S
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/016.XXXXXX")}"

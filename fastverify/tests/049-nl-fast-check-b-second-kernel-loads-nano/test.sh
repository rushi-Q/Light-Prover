#!/bin/bash
# test 049 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 049 nl-fast (check B second kernel) loads nano-lean.toml from the working directory: cwd file changes the verdict, the checker core, or enables a trus
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/049.XXXXXX")}"

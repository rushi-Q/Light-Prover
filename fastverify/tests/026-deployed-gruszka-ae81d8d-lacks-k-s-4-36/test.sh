#!/bin/bash
# test 026 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 026 deployed gruszka ae81d8d lacks K's 4.36-conformance fixes (B17 _nested prefix 018b0d6, B18 uniform nested occurrences 4ad120b): single-kernel chec
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/026.XXXXXX")}"

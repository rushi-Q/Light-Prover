#!/bin/bash
# test 009 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 009 pleanchecker and run.sh accept a kernel-invalid export read from a pipe (FastParse decline re-opens drained pipe)
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/009.XXXXXX")}"

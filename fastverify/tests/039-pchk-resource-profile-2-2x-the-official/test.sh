#!/bin/bash
# test 039 (kind export-level, heavy: rh-mid 1.1 GB): every fast checker vs the official comparator (recorded: ACCEPT)
# finding: 039 pchk resource profile: 2.2x the official comparator's peak memory; one trailing sparse-index line forces a second full parse
# PASS iff the fast verdicts are unchanged (accept) on rh-mid and on rh-mid + one late sparse line. check A's mitigation: --timeout
# (DECLINE instead of an unbounded run), SIGKILL (OOM) of a kernel -> DECLINE instead of REJECT; memory need documented in its README.
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/039.XXXXXX")}"

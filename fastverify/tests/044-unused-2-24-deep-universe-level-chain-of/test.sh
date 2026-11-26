#!/bin/bash
# heavy (slow official / generated inputs; run with --heavy)
# test 044 (kind export-level: every fast checker of the package vs the official lake comparator 4.36, cases in CASES)
# finding: 044 unused 2^24-deep universe level chain: official Lean export parser internal-panics (Level.mkData depth limit), check B (kcompare+gruszka[+nano-lea
# PASS iff no fast checker accepts what the official rejects or rejects what it accepts (decline = exit 2 -> official path).
exec "$(dirname "$0")/../lib/checkcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/044.XXXXXX")}"

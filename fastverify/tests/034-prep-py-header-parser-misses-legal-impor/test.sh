#!/bin/bash
# test 034 (kind e2e: the end-to-end repro, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 034 prep.py header parser misses legal imports (guillemets, name on next line, imports beyond 64 KiB): no dependency edge, fast build races and reject
# PASS iff for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
[ "${FV_HEAVY:-0}" = 1 ] || export CASES="${CASES:-a b}"   # case c (1200 modules, ~10 min) only with --heavy
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/034.XXXXXX")}"

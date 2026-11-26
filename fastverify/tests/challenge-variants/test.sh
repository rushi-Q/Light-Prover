#!/bin/bash
# test challenge-variants (kind e2e, generality: more challenge configurations; not a finding id): enable_nanoda instead of
#   external_kernels, definitions only (theorem_names []), nested challenge/solution modules, «»-escaped and unicode theorem
#   names, Quot.sound not permitted (no builtin Quot targets), sorryAx permitted. 13 cases (x/cases.txt, x/mkcases.py).
# finding: challenge-variants: the package must read ANY valid comparator.json exactly as Lake 4.36 does (names, modules, kernels, axioms)
# PASS iff for every case the package's final verdict == the official verdict and, when both export, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/challenge-variants.XXXXXX")}"

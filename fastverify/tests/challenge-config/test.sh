#!/bin/bash
# test challenge-config (kind e2e, generality: a NON-RH challenge configuration; not a finding id): solution_module = Solution,
#   theorems foo/bar, definition_names = [myDef], permitted axioms without Classical.choice. Cases: honest, definition body
#   differs from the challenge's, Classical axiom used, statement differs, sorry, extra helper theorem.
# finding: challenge-config: the package must take theorem names, definitions, axioms and the solution module from the challenge's comparator.json
# PASS iff for every case the package's final verdict == the official verdict and, when both export, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/challenge-config.XXXXXX")}"

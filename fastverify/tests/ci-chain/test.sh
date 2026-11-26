#!/bin/bash
# test ci-chain (kind component): tools/ci (CI benchmark: official per-commit flow with a cached .lake,
#   sound per-commit chain on top of tools/incr) and the closure items: B3 item closure-only (plan restricted to the solution module's import closure),
#   tools/incr --closure-of / --import-arts-empty. A 5-commit history of a tiny 3-library project; per commit the sound
#   closure chain must give the verdict of the official 4.36 `lake comparator` build set (`lake build <solution_module>`),
#   and the default-target official flow documents that a broken module outside the closure rejects.
#   No Mathlib; ~4 min.
# finding: planner importArts walk and tools/incr re-planning; default targets vs solution module
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/ci-chain.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" ci-chain "$W" "$(dirname "$0")/run.sh" "$W.work"

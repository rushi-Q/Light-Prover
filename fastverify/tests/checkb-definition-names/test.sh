#!/bin/bash
# test checkb-definition-names (kind component/generality: check/checkB/regress/defs/run.sh - comparator.json definition_names: 25 Lean
#   projects built + exported officially, kcompare --definitions / check B C3 / C4 vs the OFFICIAL Lean 4.36 comparator)
# finding: checkb-definition-names: check B decides definition_names (Lean 4.36 definition holes) exactly as the official comparator
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/checkb-definition-names.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" checkb-definition-names "$W" "${FV_ROOT:-$(dirname "$0")/../..}/check/checkB/regress/defs/run.sh" "$W.work" 8

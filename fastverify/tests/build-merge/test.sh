#!/bin/bash
# test build-merge (kind component/stage: build/test/merge.sh - B3 'merge' (sound preset only): toy projects merge/merge-silent:
#   a group merges and builds; a leak-failing group is rebuilt by the split fallback, or dissolved up front by a deny
#   list (mergeplan --deny; build/hints/merge-deny.txt is read by default); a merged header keeps the original import
#   order (equal-priority instances; the legacy order breaks a downstream module); a SILENT namespace-shadowing leak is
#   kept apart by the exact leak rule, and with every rule disabled the unmerged retry recovers the build)
# finding: build-merge: module merging can only cost time, never the build (sound-mode build transform, not tied to a numbered test)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-merge.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" build-merge "$W" "${FV_ROOT:-$(dirname "$0")/../..}/build/test/merge.sh" "$W.work"

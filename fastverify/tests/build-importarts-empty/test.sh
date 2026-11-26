#!/bin/bash
# test build-importarts-empty (kind component/stage): opt-in sound build item sound-fast-path=importarts-empty:
#   module-system toy built with exact importArts vs importArts = {}: BUILT, identical outputs, no visibility change. ~1 min.
# finding: build-importarts-empty: importArts = {} on a module-system toy: identical outputs, no visibility change
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-importarts-empty.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" build-importarts-empty "$W" "$(dirname "$0")/run.sh" "$(dirname "$W")"

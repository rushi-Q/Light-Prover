#!/bin/bash
# test stage-build (kind component/stage: build/test/run.sh - fast build vs the official sandboxed lake build at the same path,
#   every artifact byte-compared: two libs with options, module system imports, self-modifying sources -> DECLINED)
# finding: stage-build: build stage byte-identity with the official lake build (011 019 041 043 063 066 069 070 072 class)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/stage-build.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" stage-build "$W" "${FV_ROOT:-$(dirname "$0")/../..}/build/test/run.sh" "$W.work"

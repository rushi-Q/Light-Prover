#!/bin/bash
# test lean436-projects (kind component/generality: tests/toolchain/v436.sh - projects on a SECOND official release, Lean v4.36.0:
#   good/sorry/axiom toys, package vs the plain official 4.36 flow (lake build + the release's leanexport + lake comparator))
# finding: lean436-projects: the package handles any pinned official Lean release (fast stages decline -> official stages), same verdicts/exports
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/lean436-projects.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" lean436-projects "$W" "$(dirname "$0")/../toolchain/v436.sh" "$W.work"

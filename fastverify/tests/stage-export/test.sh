#!/bin/bash
# test stage-export (kind component/stage: tests/export/run.sh - export stage on oleans built by the official Lean 4.33.1:
#   native output byte-identical to the official lean4export, or a decline whose official fallback is identical; githash,
#   IR files, missing targets, options, duplicates, paths with spaces; rh-mid byte-identity only with --heavy)
# finding: stage-export: export stage exactness and fail-closed declines (008 010 013 018 030 033 + IR/githash cases)
export FV_COMPONENT_ALL=1
H=; [ "${FV_HEAVY:-0}" = 1 ] && H=--heavy
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/stage-export.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" stage-export "$W" "$(dirname "$0")/../export/run.sh" "$W.work" $H

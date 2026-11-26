#!/bin/bash
# test orchestrator-package (kind component/stage: tests/package/run.sh - orchestrator-level tests of bin/fastverify: OUT reuse refused,
#   shipped .lake ignored, caller environment ignored, unpinned/unstartable components refused, refusals for inputs the
#   package cannot judge exactly, official verdicts on toy projects)
# finding: orchestrator-package: bin/fastverify orchestration fixes (067 066 016 036 001 + refusal paths)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/orchestrator-package.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" orchestrator-package "$W" "$(dirname "$0")/../package/run.sh" "$W.work"

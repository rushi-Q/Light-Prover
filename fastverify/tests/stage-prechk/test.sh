#!/bin/bash
# test stage-prechk (kind component/stage: check/prechk/test/run.sh --quick - official-limits pre-check on the exports of the numbered tests,
#   generated chains and mutations of an honest export; the 16.7M-line level chain only with --heavy)
# finding: stage-prechk: prechk must flag exactly the official tools' failure cases (012 024 029 032 044 045 047 051 056) and stay clean on honest exports
export FV_COMPONENT_ALL=1
Q=--quick; [ "${FV_HEAVY:-0}" = 1 ] && Q=
exec "$(dirname "$0")/../lib/component.sh" stage-prechk "${1:-$(mktemp -d "${TMPDIR:-/tmp}/stage-prechk.XXXXXX")}" "${FV_ROOT:-$(dirname "$0")/../..}/check/prechk/test/run.sh" $Q

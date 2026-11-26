#!/bin/bash
# test retired-checka (kind component/package: tests/package/retired-checkA.sh - the retired check A options are refused with a message
#   naming the replacement, never mapped; the remaining presets/options still parse; no Lean build)
# finding: retired-checka: retirement of the legacy judge check A (C1/C2, presets fast-exact/default)
export FV_COMPONENT_ALL=1
exec "$(dirname "$0")/../lib/component.sh" retired-checka "${1:-$(mktemp -d "${TMPDIR:-/tmp}/retired-checka.XXXXXX")}" "${FV_ROOT:-$(dirname "$0")/../..}/tests/package/retired-checkA.sh"

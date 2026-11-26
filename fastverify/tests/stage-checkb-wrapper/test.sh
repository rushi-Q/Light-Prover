#!/bin/bash
# test stage-checkb-wrapper (kind component/stage: check/checkB/test/run.sh - check B wrapper: inputs, configs, env/cwd isolation,
#   pinned binaries, resource/timeout behaviour; expectations 0/1/2, n1 = no false reject, n0 = never accept)
# finding: stage-checkb-wrapper: check B wrapper behaviour (002 005 016 049 class + config handling)
export FV_COMPONENT_ALL=1
exec "$(dirname "$0")/../lib/component.sh" stage-checkb-wrapper "${1:-$(mktemp -d "${TMPDIR:-/tmp}/stage-checkb-wrapper.XXXXXX")}" "${FV_ROOT:-$(dirname "$0")/../..}/check/checkB/test/run.sh"

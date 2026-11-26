#!/bin/bash
# test 001 (kind component/deployment: tests/001-*/portability.sh on THIS host)
# finding: 001 gruszka binary uses AMD-only SSE4a insertq: SIGILL on Intel hosts, fast check B cannot run
# PASS iff every package binary is free of SSE4a, needs no newer glibc than the host, resolves its libraries, and every
# stage's --preflight passes here (run it on each class of host you deploy to, e.g. Intel AND AMD hosts).
export FV_COMPONENT_ALL=1
exec "$(dirname "$0")/../lib/component.sh" 001 "${1:-$(mktemp -d "${TMPDIR:-/tmp}/001.XXXXXX")}" "$(dirname "$0")/portability.sh"

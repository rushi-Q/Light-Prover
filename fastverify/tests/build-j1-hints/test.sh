#!/bin/bash
# test build-j1-hints (kind component/stage): j1-saturated only with applicable cost hints (build/sched.py
#   305942cf): a tiny core-only project, 2 threads, --preset sound without / with a hints file for its short modules. ~2 min.
# finding: build-j1-hints: j1-saturated only with applicable cost hints (Mathlib-as-project generality)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-j1-hints.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" build-j1-hints "$W" "$(dirname "$0")/run.sh" "$(dirname "$W")"

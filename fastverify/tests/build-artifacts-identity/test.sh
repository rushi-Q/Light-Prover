#!/bin/bash
# heavy (~78 projects, each built twice; ~20-40 min with 6 in parallel)
# test build-artifacts-identity (kind component/stage: build-artifacts-identity/run.sh = build/test/cmp_official.sh over every project dir of the numbered tests)
# finding: build-artifacts-identity: the fast build produces byte-identical artifacts to the official lake build (or declines) on every project of the numbered regression tests
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-artifacts-identity.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" build-artifacts-identity "$W" "$(dirname "$0")/run.sh" "$W.work"

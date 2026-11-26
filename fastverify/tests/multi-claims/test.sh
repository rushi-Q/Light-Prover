#!/bin/bash
# test multi-claims (kind component/e2e): tools/claims.py - many comparator claims of one project verified
#   with ONE untrusted build (first claim with --keep-work, the others exported from the kept tree by the official exporter
#   and judged in export-in sound mode against their own pinned official challenge exports): two claims ACCEPTED, a claim
#   whose challenge statement differs REJECTED by the trusted check; 'claims.py pin' reproduces the reference run's
#   challenge export byte for byte. Core-only, default toolchain, ~2 min.
# finding: none (scenario 'verify a published release with many claims')
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/multi-claims.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" multi-claims "$W" "$(dirname "$0")/x/check.sh" "$W.work"

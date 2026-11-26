#!/bin/bash
# test 013 (kind exporter component: the package's export/export.sh vs the official lean4export v4.33.0 on the same .olean files)
# finding: 013 native exporter's duplicate-constant rule ignores types: accepts import sets the official exporter rejects (MEDIUM)
# PASS iff both succeed with byte-identical output or both fail (cases in ECASES).
exec "$(dirname "$0")/../lib/exportcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/013.XXXXXX")}"

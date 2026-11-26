#!/bin/bash
# test 033 (kind exporter component: the package's export/export.sh vs the official lean4export v4.33.0 on the same .olean files)
# finding: 033 native exporter's reference fallback is NOT official Export.lean (getIdxS): on panic paths it writes different (invalid) NDJSON, exit 0 (MEDIUM)
# PASS iff both succeed with byte-identical output or both fail (cases in ECASES).
exec "$(dirname "$0")/../lib/exportcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/033.XXXXXX")}"

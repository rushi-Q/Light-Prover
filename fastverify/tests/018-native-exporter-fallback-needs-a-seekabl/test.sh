#!/bin/bash
# test 018 (kind exporter component: the package's export/export.sh vs the official lean4export v4.33.0 on the same .olean files)
# finding: 018 native exporter fallback needs a seekable stdout: on a pipe any native failure -> exit 1 + truncated export; on a file -> reference-speed cliff (M
# PASS iff both succeed with byte-identical output or both fail (cases in ECASES).
exec "$(dirname "$0")/../lib/exportcases.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/018.XXXXXX")}"

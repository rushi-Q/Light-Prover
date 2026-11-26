#!/bin/bash
# test odd-layouts (kind e2e, generality: odd but valid project layouts; not a finding id): symlinked source file, symlinked
#   source directory, symlink to a file outside the project, non-ASCII + deep module paths, guillemet module names, CRLF/BOM
# finding: odd-layouts: the package must build exactly what lake build builds from any valid source layout (or decline)
# PASS iff for every case the package's final verdict == the official verdict and, when both export, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/odd-layouts.XXXXXX")}"

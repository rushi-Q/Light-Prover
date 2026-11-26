#!/bin/bash
# test lake-config (kind e2e, generality: Lake configuration handling; not a finding id - cases found while testing the
#   proposed build fixes: globs as a single string, multi-line TOML strings/arrays, lakefile.lean-only
#   projects, option value types, package names needing escapes/quotes, the standard `lake new` layout, dotted keys, roots)
# finding: lake-config: the build stage must reproduce Lake's own reading of ANY lakefile (or decline to the official lake build)
# PASS iff for every case the package's final verdict == the official verdict and, when both export, the exports are identical.
exec "$(dirname "$0")/../lib/xrepro.sh" "$(dirname "$0")" "${1:-$(mktemp -d "${TMPDIR:-/tmp}/lake-config.XXXXXX")}"

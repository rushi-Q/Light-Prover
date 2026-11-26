#!/bin/bash
# test escaped-package-name (kind component/e2e): a VALID project that requires a package
#   whose Lake name needs «» escaping (real cases: Foundation 2deab58 / PhysLean b9043cc require «doc-gen4», «axiom-audit»).
#   Lake writes the manifest name escaped ("«my-dep»") but materializes the package under the UNESCAPED directory
#   (.lake/packages/my-dep). lib/manifest.py uses the escaped name as the directory: (a) on a workspace laid out by Lake it
#   refuses ("package «my-dep» ... missing", no verdict); (b) with a «my-dep» -> my-dep symlink it binds the package to
#   .lake/packages/«my-dep», Lake cannot find .lake/packages/my-dep, tries to clone (no network) -> every build option fails
#   -> REJECTED ("the official lake build fails"). PASS iff the verdict is ACCEPTED in both layouts.
# finding: escaped package names in the manifest (availability / false reject or refusal, not soundness)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/escaped-package-name.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" escaped-package-name "$W" "$(dirname "$0")/x/check.sh" "$W.work"

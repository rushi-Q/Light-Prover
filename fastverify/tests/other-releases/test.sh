#!/bin/bash
# heavy
# test other-releases (kind generality/e2e): projects pinned to OTHER official Lean releases, enabled with
#   tools/addrelease.py (official toolchain tree pinned by manifest, official exporter of the release, gate: the 4.36
#   kernel-primitive targets must export from the release's Init + check/xversion/releases.json). Core-only cases through
#   --preset reference (B0 + E0 of the release + official 4.36 lake comparator) and --preset sound (B0 + E0 + CS):
#   verdicts must equal the expected ones (incl. a false `decide +kernel` claim and a non-elaborating proof: REJECTED),
#   exports byte-identical; a release <= 4.25 (no String.ofList) must be refused by addrelease.py. SKIP if no release was
#   added. ~3 min per release.
# finding: none (generality: other Lean releases)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/other-releases.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" other-releases "$W" "$(dirname "$0")/x/check.sh" "$W.work"

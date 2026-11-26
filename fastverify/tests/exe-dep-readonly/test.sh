#!/bin/bash
# test exe-dep-readonly (kind component/e2e): a VALID project whose default targets include a
#   lean_exe that imports a dependency package (here Batteries; the same EROFS class: PhysLean b9043cc's Lake
#   artifact cache, compfiles 0035280's exes - whose official verdict is REJECTED anyway because of Usa2022P6). B1-B3 decline
#   (finding 063 rule), the official build B0 must compile the dependency's C code (Batteries ...:c.o) and the trusted
#   workspace is bound read-only -> EROFS -> the package reports REJECTED ("the official lake build fails") in every preset,
#   although `lake build` with a writable .lake/packages (any normal checkout) succeeds. PASS iff the verdict is not REJECTED
#   (ACCEPTED, or no verdict = fail closed, reported as WARN-NOVERDICT in the row).
# finding: lean_exe importing a dependency fails on the read-only workspace (availability / false reject, not soundness)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/exe-dep-readonly.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" exe-dep-readonly "$W" "$(dirname "$0")/x/check.sh" "$W.work"

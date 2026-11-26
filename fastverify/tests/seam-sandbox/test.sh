#!/bin/bash
# test seam-sandbox (kind e2e, sound mode): a project whose module runs IO at elaboration time inside the
#   build sandbox (writes to /dev/shm, /tmp, $HOME, /scratch, OUT/work, OUT/incr; pid count; a setsid+nohup detached
#   process with delayed writes): no write reaches the host, read-only paths give EROFS, own pid namespace, no survivor
#   after the build or 90 s later; verdict ACCEPTED. No Mathlib; ~2.5 min.
# finding: none (seam probe of the build sandbox)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/seam-sandbox.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" seam-sandbox "$W" "$(dirname "$0")/run.sh" "$W.work"

#!/bin/bash
# test incr-reverify (kind component): tools/incr (incremental re-verification after small edits: untrusted
#   reuse of an earlier sound run's build tree + E1 + the trusted check-sound.sh, optional warm pleanchecker_incr): valid
#   proof edit ACCEPTED in the full, optimistic and warm modes; sorry edit REJECTED; ill-typed edit -> build fails; a
#   definition change under a stale importer: optimistic attempt REJECTED by the official-kernel leg, full rebuild ACCEPTED.
#   No Mathlib; ~3 min (two small base runs through --preset sound).
# finding: none (tool regression of tools/incr)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/incr-reverify.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" incr-reverify "$W" "$(dirname "$0")/run.sh" "$W.work"

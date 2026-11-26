#!/bin/bash
# test check-sound-svc (kind component): check/sound/check-sound-svc.sh = check-sound.sh + --integrity-cache:
#   verdicts equal check-sound.sh's with and without a cache hit (good / extra axiom / kernel-invalid /
#   changed statement / missing declaration / missing target); the cache is used only after a full verification and only
#   while every stamp is unchanged (touched / changed / mtime-restored pin, extra 4.36 tree file, other key, symlinked
#   record or pin, changed pins.env, bad cache-dir mode). All on private copies of the pins and the 4.36 tree. ~2 min.
# finding: none (trusted-wiring regression of the sound service)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/check-sound-svc.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" check-sound-svc "$W" "${FV_ROOT:-$(dirname "$0")/../..}/check/sound/test/svc.sh"

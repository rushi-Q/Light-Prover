#!/bin/bash
# heavy
# test fvserve-437 (kind component/e2e): the attempt service on a Lean 4.37.0-rc1 problem set with the 4.37
#   trusted check (pins-437.env): the official 4.37 flow builds a 12-problem batch project switched to 4.37 (Mathlib of
#   FV437_PACKAGES) and yields the problem set; fvserve --svc-check --pins check/sound/pins-437.env with a fork server built by
#   fork/build.sh for 4.37 must give the official flow's verdict on all 18 attempts (12 honest ACCEPTED, 6 cheat variants
#   REJECTED; 6 concurrent clients), use the 4.37 native exporter and the fork server; tools/batchverify.py --pins gives the
#   same verdicts. Needs the 4.37.0-rc1 toolchain (tools/addrelease.py), the 4.37 judge binaries and a BUILT 4.37 Mathlib
#   workspace in FV437_PACKAGES; otherwise SKIP. ~6 min on 16 threads.
# finding: the attempt service on a 4.37.0-rc1 problem set must use the 4.37 judge, exporter and fork server end to end
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/fvserve-437.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" fvserve-437 "$W" "${FV_ROOT:-$(dirname "$0")/../..}/tools/guard/test/test-fvserve-437.sh" "$W.work"

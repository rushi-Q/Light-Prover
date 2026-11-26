#!/bin/bash
# heavy
# test fvserve-service (kind component/e2e): tools/fvserve (persistent sound verification service) on a 16-problem
#   Mathlib set: the official flow on the positive batch must ACCEPT (it yields the official problem-set challenge export);
#   per-attempt verdicts of the g06 attempt set submitted one by one AND concurrently (shared batches) = the official labels
#   (6 cheat classes REJECTED, honest and look-alike ACCEPTED, non-compiling / misspelt / cross-importing REJECTED); compiler
#   feedback returned; best-of-3 of one theorem; an attempt writing into the service's batch dir gets no file and no
#   ACCEPTED (Landlock-confined fork child / batchverify sandbox); fork-server death -> fallback to the official lean;
#   wrong challenge pin -> the service refuses to start. Needs the Mathlib workspace (FV_PACKAGES, node-local recommended)
#   and the official 4.33.1 toolchain (TC433) for the fork-server build. ~5 min.
# finding: none (tool regression of the sound service)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/fvserve-service.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" fvserve-service "$W" "${FV_ROOT:-$(dirname "$0")/../..}/tools/fvserve/test/test-fvserve.sh" "$W.work"

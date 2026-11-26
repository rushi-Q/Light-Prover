#!/bin/bash
# heavy
# test batchverify (kind component/e2e): tools/batchverify.py (sound per-attempt verdicts for many proof
#   attempts in one batch around the unchanged trusted check-sound.sh) on a 14-problem Mathlib set: the official flow on the
#   positive batch must ACCEPT; cheating variants (axiom, weaker statement, changed constant, macro-hidden sorry, ill-typed
#   addDecl under debug.skipKernelTC, native_decide), a non-compiling attempt, a misspelt theorem name, an attempt importing another attempt and a sorry attempt whose problem another attempt proves validly (no cross-credit) must be REJECTED,
#   an honest proof and a harmless @[implemented_by] look-alike ACCEPTED; a wrong challenge pin must give no ACCEPTED.
#   Needs the Mathlib workspace (FV_PACKAGES; a node-local copy is much faster on NFS hosts). Heavy-ish: ~3-6 min.
# finding: none (tool regression of tools/batchverify.py)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/batchverify.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" batchverify "$W" "${FV_ROOT:-$(dirname "$0")/../..}/bench/throughput/test/test-batchverify.sh" "$W.work"

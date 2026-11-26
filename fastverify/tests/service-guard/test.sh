#!/bin/bash
# heavy
# test service-guard (kind component/e2e): tools/batchverify.py and tools/fvserve under per-attempt
#   resource limits (--limits, tools/guard) on a 16-problem Mathlib set: the official flow on the positive batch must ACCEPT
#   (it yields the official problem-set challenge export); 6 BOUNDED resource probes (4 GB heap, 1 GB into the sandbox /tmp,
#   100 MB of messages, 100 processes, 300 threads, a 90 s loop; each an honest proof) must end NO-VERDICT (resource limit /
#   timeout) or, in the fork-server path, be refused by the sandbox; 10 honest attempts must stay ACCEPTED; the service
#   survives and leaves no fork child behind; --max-pending answers 'queue full' at once; --request-timeout drops a
#   stalled client. Needs the Mathlib workspace (FV_PACKAGES, node-local recommended) and the official 4.33.1 toolchain
#   (TC433). ~8 min.
# finding: per-attempt resource limits of the attempt service (no fork child left behind, queue limit, request timeout)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/service-guard.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" service-guard "$W" "${FV_ROOT:-$(dirname "$0")/../..}/tools/guard/test/test-service-guard.sh" "$W.work"

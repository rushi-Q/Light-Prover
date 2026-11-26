#!/bin/bash
# test fvguard (kind component): tools/guard/fvguard.py, the root-less resource guard of untrusted work -
#   20 BOUNDED probes (each ends by itself within seconds, <= ~1.5 GB / 60 processes / 600 MB disk even unguarded): honest
#   exit codes passed through (0, 1, 3, signal); memory (heap; hidden in a sandbox-private tmpfs), processes (plain and in a
#   pid namespace), threads, wall, RLIMIT_CPU, tree CPU, RLIMIT_FSIZE, RLIMIT_DATA, output volume, disk bytes, disk entries ->
#   the right violation and exit 125; a daemonized orphan dies with the tree; library API; and, where a cgroup launcher works
#   (a cgrun scope launcher), the cgroup backend (OOM kill of heap and tmpfs -> violation mem, TasksMax refusals). No Lean, ~40 s.
# finding: service hardening (resource limits of untrusted work)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/fvguard.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" fvguard "$W" "${FV_ROOT:-$(dirname "$0")/../..}/tools/guard/test/test-fvguard.sh" "$W.work"

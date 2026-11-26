#!/bin/bash
# heavy
# test sound-auto (kind availability/e2e + unit): --preset sound-auto = lib/autotune.py (untrusted item choice by
#   project shape and host) + B3 item skip-kernel-tc=except-translate (per-module gate; the @[to_dual] false-reject class of confirm-reject). ~4-6 min, 16 threads.
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/sound-auto.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" sound-auto "$W" "$(dirname "$0")/run.sh" "$(dirname "$W")"

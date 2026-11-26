#!/bin/bash
# Builds expdiff (std-only Rust, no dependencies) and prints the binary path on the last line.
# Target dir on node-local scratch (keep it off NFS homes): EXPDIFF_TARGET (default ${FV_SCRATCH:-$TMPDIR}/$USER-expdiff-target).
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
TD=${EXPDIFF_TARGET:-}
if [ -z "$TD" ]; then
  TD=${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-expdiff-target
fi
cd "$HERE"
CARGO_TARGET_DIR="$TD" cargo build --release --quiet 2>&1 | grep -v "^warning\|^ *|\|^ *=\|-->\|^$" >&2 || true
B="$TD/release/expdiff"
test -x "$B"
sha256sum "$B" >&2
echo "$B"

#!/bin/bash
# Builds exphash & expcompress (offline Rust) and prints the release bin directory on the last line.
# Target dir on node-local scratch (NFS home has limited quota): EXPHASH_TARGET (default ${FV_SCRATCH:-$TMPDIR}/$USER-exphash-target).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
TD=${EXPHASH_TARGET:-}
if [ -z "$TD" ]; then
  TD=${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-exphash-target
fi
cd "$HERE"
CARGO_TARGET_DIR="$TD" cargo build --release --offline --quiet 2>&1 | grep -v "^warning\|^ *|\|^ *=\|-->\|^$" >&2 || true
B="$TD/release"
test -x "$B/exphash"
test -x "$B/expcompress"
echo "$B"

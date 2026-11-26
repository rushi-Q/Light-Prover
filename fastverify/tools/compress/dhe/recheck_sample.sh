#!/bin/bash
# recheck_sample.sh SAMPLE_RES OUT -- re-run DeadLetCheck (batch) over the A/B oleans of a finished sample
R=$1; OUT=$2; W=${DHE_WORK:-${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-dhe/w}
H=$(cd "$(dirname "$0")" && pwd)
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
L=$(mktemp)
awk '{print $2}' "$R" | while read m; do
  [ -f "$W/$m/a/M.olean" ] && [ -f "$W/$m/b/M.olean" ] && echo "$m $W/$m/a/M.olean $W/$m/b/M.olean"; done > "$L"
LEAN_PATH=$TC/lib/lean $TC/bin/lean --run "$H/DeadLetCheck.lean" --list "$L" > "$OUT"
rm -f "$L"

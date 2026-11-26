#!/bin/bash
# run_sample.sh LIST EDITS OUT [J] -- dhe_check.sh over a module list in parallel; RESULT lines -> OUT
# work dirs: $DHE_WORK (default ${FV_SCRATCH:-$TMPDIR}/$USER-dhe/w), one per module (kept for recheck_sample.sh)
LIST=$1; ED=$2; OUT=$3; J=${4:-46}
H=$(cd "$(dirname "$0")" && pwd)
W=${DHE_WORK:-${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-dhe/w}
mkdir -p "$W"
cat "$LIST" | xargs -P "$J" -I{} bash -c "'$H/dhe_check.sh' {} '$ED' '$W/{}' 2>/dev/null" > "$OUT"

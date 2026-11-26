#!/bin/bash
# campaign.sh OUTROOT PER_OP SEED JOBS [BASE...] [-- OPS] : differential export fuzzing (runfuzz.py) over the bases
# (default: cmpx if available + ind quot lit univ hole). OPS (after --) default: all operators.
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
R=$1; N=$2; S=$3; J=$4; shift 4
BL=(); OPS=all
while [ $# -gt 0 ]; do [ "$1" = -- ] && { OPS=$2; break; }; BL+=("$1"); shift; done
[ ${#BL[@]} -gt 0 ] || BL=(cmpx ind quot lit univ hole)
for b in "${BL[@]}"; do
  base_inputs "$b" || { echo "base $b: not available here, skipped"; continue; }
  echo "[$(date -u +%FT%TZ)] base $b"
  python3 -I "$H/runfuzz.py" --base "$SOL" --challenge "$CH" --config "$CFG" --targets "$(targets_of "$CFG")" --out "$R/$b" \
     --ops "$OPS" --per-op "$N" --seed "$S" --jobs "$J" --threads 1 --pkg "$FV" --label "$b seed $S" 2>&1 | tail -1
done

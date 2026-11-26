#!/bin/bash
# runseams.sh OUTROOT JOBS [BASE...] : the targeted seam cases (seams.py) of every base through parsediff, the official
# comparator and CS (mutants kept).
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
R=$1; J=$2; shift 2
for b in ${*:-cmpx ind quot lit univ hole}; do
  base_inputs "$b" || { echo "base $b: not available here, skipped"; continue; }
  rm -rf "$W/seams/$b"; python3 -I "$H/seams.py" "$SOL" "$CFG" "$W/seams/$b" "$b-" 2>/dev/null
  echo -n "$b: "; python3 -I "$H/runfuzz.py" --premade "$W/seams/$b" --challenge "$CH" --config "$CFG" --out "$R/$b" --jobs "$J" --threads 1 \
     --pkg "$FV" --keep-all --label "seams $b" | tail -1
done

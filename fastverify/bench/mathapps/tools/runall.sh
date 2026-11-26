#!/bin/bash
# runall.sh NAME THREADS [ROOT] [PRESETS] : after fetch.sh + bigprojects/tools/mkws.sh: one sound run that builds the
# challenge officially (B0 + E0), pin it, then the presets of PRESETS (default "sound reference"; the recorded runs also
# used the preset fast-exact, retired with check A and now refused) against the pinned challenge, then collect.py over the
# runs. FV = package (default: this one). Rows: ROOT/runs/NAME-*.
set -u
H=$(cd "$(dirname "$0")/.." && pwd); BP=$H/../bigprojects/tools; N=$1 T=$2 ROOT=${3:-/scratch/$USER/mathapps}
PRESETS=${4:-sound reference}
C=$ROOT/projects/$N-challenge
if [ ! -f "$C/challenge.export.sha256" ]; then
  TAG=c bash "$BP/run.sh" "$N" sound "$T" "$ROOT"
  [ -f "$ROOT/runs/$N-sound-c/challenge.export" ] && bash "$BP/pin.sh" "$N" "$ROOT/runs/$N-sound-c" "$ROOT"
fi
for p in $PRESETS; do TAG=pinned bash "$BP/run.sh" "$N" "$p" "$T" "$ROOT"; done
python3 -I "$BP/collect.py" "$ROOT"/runs/$N-*/ 2>&1

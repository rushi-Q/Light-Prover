#!/bin/bash
# run.sh NAME PRESET THREADS [ROOT] [fastverify args...] : one bin/fastverify run of project NAME (after fetch.sh + mkws.sh)
# -> ROOT/runs/NAME-PRESET (result.json, log/), wall time appended to ROOT/runs/done.txt. FV = the package (default: the one
# containing this bench). With a pinned challenge (ROOT/projects/NAME-challenge/challenge.export + .sha256, written by
# pin.sh from an earlier run) sound runs pass --challenge-sha256.
set -u
H=$(cd "$(dirname "$0")/.." && pwd); N=$1 PR=$2 T=$3 ROOT=${4:-/scratch/$USER/bigprojects}; shift 3; [ $# -gt 0 ] && shift
FV=${FV:-$(cd "$H/../.." && pwd)}
C=$ROOT/projects/$N-challenge; X=(); [ "$PR" = sound ] && [ -f "$C/challenge.export.sha256" ] && X=(--challenge-sha256 "$(cat "$C/challenge.export.sha256")")
O=$ROOT/runs/$N-$PR${TAG:+-$TAG}; rm -rf "$O"; mkdir -p "$ROOT/runs"
t0=$(date +%s.%N)
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$ROOT/projects/$N" "$C" "$O" --preset "$PR" \
  --threads "$T" --packages "$ROOT/ws/$N" "${X[@]}" "$@" > "$O.log" 2>&1
rc=$?; echo "$(basename "$O") rc=$rc wall=$(echo "$(date +%s.%N) - $t0" | bc)" | tee -a "$ROOT/runs/done.txt"

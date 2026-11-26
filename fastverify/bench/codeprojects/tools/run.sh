#!/bin/bash
# run.sh NAME PRESET THREADS [ROOT] [fastverify args...] : one bin/fastverify run of project NAME (after fetch.sh)
# -> ROOT/runs/NAME-PRESET[-TAG] (result.json, log/), wall time appended to ROOT/runs/done.txt.
# FV = the package (default: ROOT/../local/fv if present - a node-local install from bench/shapes/mklocal.sh - else this
# package); WS = the trusted dependency workspace (default: ROOT/ws/NAME if present, else the node-local copy of the RH
# challenge workspace ROOT/../local/ws). With a pinned challenge (NAME-challenge/challenge.export + .sha256, tools/pin.sh)
# sound runs pass --challenge-sha256.
set -u
H=$(cd "$(dirname "$0")/.." && pwd); N=$1 PR=$2 T=$3 ROOT=${4:-/scratch/$USER/codeprojects}; shift 3; [ $# -gt 0 ] && shift
L=$(dirname "$ROOT")/local
FV=${FV:-$( [ -x "$L/fv/bin/fastverify" ] && echo "$L/fv" || (cd "$H/../.." && pwd) )}
WS=${WS:-$( [ -d "$ROOT/ws/$N" ] && echo "$ROOT/ws/$N" || echo "$L/ws" )}
C=$ROOT/projects/$N-challenge; X=(); [ "$PR" = sound ] && [ -f "$C/challenge.export.sha256" ] && X=(--challenge-sha256 "$(cat "$C/challenge.export.sha256")")
O=$ROOT/runs/$N-$PR${TAG:+-$TAG}; rm -rf "$O"; mkdir -p "$ROOT/runs"
t0=$(date +%s.%N)
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$ROOT/projects/$N" "$C" "$O" --preset "$PR" \
  --threads "$T" --packages "$WS" "${X[@]}" "$@" > "$O.log" 2>&1
rc=$?; echo "$(basename "$O") rc=$rc wall=$(echo "$(date +%s.%N) - $t0" | bc) $(date -u +%H:%M:%SZ)" | tee -a "$ROOT/runs/done.txt"

#!/bin/bash
# mkgiven.sh CORPUS OUTROOT CASE : OUTROOT/given/CASE = the challenge dir + the official challenge export that the
# reference run OUTROOT/runs/CASE.reference built (official B0 + E0), with its sha256 (pinned by the runs via
# --challenge-sha256).
set -eu
C=$1; R=$2; CASE=$3
SRC=$R/runs/$CASE.reference/challenge.export
[ -s "$SRC" ] || { echo "no challenge export for $CASE"; exit 1; }
G=$R/given/$CASE; rm -rf "$G"; mkdir -p "$R/given"; cp -a "$C/challenges/$CASE" "$G"
cp "$SRC" "$G/challenge.export"; (cd "$G" && sha256sum challenge.export > challenge.export.sha256)

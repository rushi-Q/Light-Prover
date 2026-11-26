#!/bin/bash
# pin.sh NAME RUNDIR [ROOT] : pin the official challenge export built by an earlier run (RUNDIR/challenge.export)
set -eu
C=${3:-/scratch/$USER/codeprojects}/projects/$1-challenge
cp "$2/challenge.export" "$C/challenge.export"; sha256sum "$C/challenge.export" | cut -d' ' -f1 | tee "$C/challenge.export.sha256"

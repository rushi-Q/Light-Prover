#!/bin/bash
# export-in of the WHOLE Mathlib export (official lean4export of module Mathlib, 6.07 GB, 707k constants; challenge: the
# targets are 10 Mathlib theorems): sound check CS (node-local install) vs the official comparator C0
set -u
ML=${ML_ROOT:-${FV_SCRATCH:-/scratch}/mathlib-as-project}; FV=${FV:-$ML/local/fv/bin/fastverify}; WS=${WS:-$ML/local/ws}; R=${R:-$ML/runs}
E=/scratch/bench-inputs/mathlib/export/mathlib.export
one() { # tag threads args...
  local tag=$1 th=$2; shift 2; rm -rf $R/$tag
  echo "$(date -u +%FT%TZ) $(hostname) start $tag $*" >> $R/progress.log
  local t0=$(date +%s.%N)
  /usr/bin/time -v -o $R/$tag.time env -i HOME=$HOME PATH=/usr/bin:/bin LANG=C.UTF-8 $FV - $ML/chal/mlall $R/$tag --threads $th --packages $WS --from-export $E "$@" > $R/$tag.log 2>&1
  echo "$(date -u +%FT%TZ) $(hostname) done $tag rc=$? wall=$(python3 -c "import time; print(round(time.time()-$t0,1))")s" >> $R/progress.log
}
one mlall.sound-T32 32 --preset sound
one mlall.official-C0 32 --preset reference --check C0 --official-timeout 14400

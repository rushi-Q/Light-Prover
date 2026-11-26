#!/bin/bash
# prune_compose.sh TAG OTHER_EDITS... : the RH pruning plan (G1 rules of ../prune/prune.py) composed with other owners'
# edit lists. Reads the pruning index RH_INDEX (refs_index.py output) and the pristine RH project RH_PROJECT (read-only),
# writes $FV_SCRATCH/prune/{tree-TAG,TAG.json*}.
set -u
TAG=$1; shift
PR=$(cd "$(dirname "$0")/../prune" && pwd)
IDX=${RH_INDEX:?pruning index of the RH project (refs_index.py INDEX.pkl) (required)}
RH=${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}
A=${FV_SCRATCH:?node-local scratch directory for the output (required)}/prune; mkdir -p $A
echo "other edits: $*"; sha256sum "$@"
date -u
python3 -I $PR/prune.py "$IDX" "$RH" $A/tree-$TAG --drop-empty-modules \
  --ext-namespaces $PR/data/ext_namespaces-mathlib0df444a-lean4.33.1.txt --report $A/$TAG.json --other-edits "$@"
rc=$?; date -u; echo "rc=$rc"; exit $rc

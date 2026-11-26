#!/bin/bash
# attempt_caps.sh OUT PROJ CHAL WS CPUS THREADS "MEM..." [fastverify args] - cold-cache cap sweep of one attempt project
# (pass the preset explicitly, e.g. --preset sound; env SUFFIX is appended to the row tag, e.g. SUFFIX=.sound):
# before every run the workspace, the toolchains and the project are evicted from the page cache (evict.py), so the scope's
# memory.peak includes the oleans the build/export/check actually touch. Rows OUT/<tag>.cold.{cg.json,fv.log,result.json}.
set -u
OUT=$1; PROJ=$2; CHAL=$3; WS=$4; CPUS=$5; T=$6; MEMS=$7; shift 7
H=$(cd "$(dirname "$0")" && pwd)
export WS
for M in $MEMS; do
  TAG=$(basename "$(dirname "$PROJ")").c$T.m${M%G}.cold${SUFFIX:-}
  [ -s "$OUT/$TAG.cg.json" ] && { echo "skip $TAG"; continue; }
  python3 -I "$H/evict.py" "$WS" "$PROJ" "$CHAL" "$HOME/.elan/toolchains" "$OUT/$TAG" 2>/dev/null | tail -1
  "$H/run_fv.sh" "$OUT" "$TAG" "$CPUS" "$M" "$T" "$PROJ" "$CHAL" "$@"
done

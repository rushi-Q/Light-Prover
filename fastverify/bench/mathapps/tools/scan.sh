#!/bin/bash
# scan.sh SRCROOT REPO_URL... : partial-clone each repo (no checkout, no code run) and list the commits whose
# lean-toolchain is v4.33.x or whose manifest pins mathlib db584cd6 (v4.33.0) / 0df444a (v4.33.1).
set -u
ROOT=$1; shift
for url in "$@"; do
  n=$(echo "$url" | sed -E 's#https://github.com/##; s#/#_#; s#\.git$##')
  S=$ROOT/$n
  [ -d "$S" ] || timeout 900 git clone -q --filter=blob:limit=16k --bare "$url" "$S" 2>/dev/null || { echo "$n CLONE-FAIL"; continue; }
  head=$(git -C "$S" rev-parse HEAD 2>/dev/null)
  htc=$(git -C "$S" show HEAD:lean-toolchain 2>/dev/null | tr -d '\n')
  # all commits touching toolchain/manifest, newest first
  hits=""
  for c in $(git -C "$S" log --format=%H -- lean-toolchain lake-manifest.json 2>/dev/null | head -400); do
    tc=$(git -C "$S" show "$c:lean-toolchain" 2>/dev/null | tr -d '\n')
    case "$tc" in *v4.33*) ml=$(git -C "$S" show "$c:lake-manifest.json" 2>/dev/null | python3 -I -c 'import json,sys
try:
  m=json.load(sys.stdin); print(next((p.get("rev","")[:8] for p in m["packages"] if p["name"]=="mathlib"),"none"))
except Exception: print("?")'); hits="$hits $c:${tc##*:}:$ml:$(git -C "$S" show -s --format=%cs "$c")";;
    esac
  done
  echo "$n HEAD=${head:0:10} tc=$htc HITS:$hits"
done

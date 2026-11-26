#!/bin/bash
# Build the zygote toolchain lean4-s01zy (branch s01/zy = r/r11z + SIGCHLD + replicas + rusage log; see README.md)
# incrementally from the harness-built d0619cbcf0 tree (same cmake paths via a bwrap bind, PGO profile of the tree).
# usage (in the shipped dir): bash build_tc.sh  -> prints the stage1 path on the last line
#   S01ZY_BASE_TREE  the harness-built d0619cbcf0 tree (configured by cmake at exactly this absolute path; README.md)
#   S01ZY_WORK       work directory: patched copy tczy-<patch sha>, ccache, zyc, tczy-latest.txt
set -euo pipefail
HERE=$(pwd)
SRC=${S01ZY_BASE_TREE:?harness-built d0619cbcf0 tree, see README.md (required)}
W=${S01ZY_WORK:?work directory for the patched copy, ccache and outputs (required)}
PS=$(sha256sum "$HERE/s01zy.patch" | cut -c1-10)
DST=$W/tczy-$PS
mkdir -p "$W"
if [ ! -f "$DST/OK.S01" ]; then
  rm -rf "$DST"
  echo "[$(date -u +%T)] copy $SRC -> $DST"
  cp -a "$SRC" "$DST"
  rm -f "$DST/OK" "$DST/.git"
  (cd "$DST" && patch -p1 --forward < "$HERE/s01zy.patch")
  echo "[$(date -u +%T)] make"
  t0=$(date +%s)
  bwrap --dev-bind / / --bind "$DST" "$SRC" --chdir "$SRC" \
    env CCACHE_DIR="$W/ccache" make -C build/release -j256 > "$DST/make.S01.log" 2>&1 || { tail -40 "$DST/make.S01.log"; exit 1; }
  echo "[$(date -u +%T)] make done in $(( $(date +%s) - t0 )) s"
  grep -c "Building" "$DST/make.S01.log" || true
  echo "$PS $(date -u +%FT%TZ)" > "$DST/OK.S01"
fi
TC=$DST/build/release/stage1
"$TC/bin/lean" --version
strings "$TC/lib/lean/libleanshared.so" | grep -c LEAN_ZYGOTE_REPLICAS
sha256sum "$TC/bin/lean" "$TC/lib/lean/libleanshared.so"
gcc -O2 -o "$W/zyc" "$HERE/zyc.c"
C=$(cat "$HERE/s01zy.commit" 2>/dev/null || echo unknown)
echo "$TC lean4-s01zy-$C-pgo $C" > "$W/tczy-latest.txt"
echo "$TC"

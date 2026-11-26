#!/bin/bash
# Reproducible offline sandboxed build recipe for gruszka-lowmem.
# Usage: bash build-gruszka-lowmem.sh WORKDIR (env: CHECKB_REPOS = a directory with the gruszka git repository holding the pinned commit; KBUILD = a sandboxed cargo wrapper
# with Rust 1.97.1, as for check/checkB/build.sh)
set -euo pipefail
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
WORKDIR=$(mkdir -p "${1:?WORKDIR}" && cd "$1" && pwd)
K=${CHECKB_REPOS:?directory with the gruszka git repository}
KB=${KBUILD:?sandboxed cargo wrapper KBUILD SRC_DIR CMD}
CHECKB=$(cd "$HERE/../../checkB" && pwd)

rm -rf "$WORKDIR/gruszka-lowmem"
mkdir -p "$WORKDIR/gruszka-lowmem"
git -C "$K/gruszka" archive 4ad120b | tar -x -C "$WORKDIR/gruszka-lowmem"
(cd "$WORKDIR/gruszka-lowmem" && \
  patch -p1 --quiet < "$CHECKB/patches/gruszka-combined.diff" && \
  patch -p1 --quiet < "$HERE/patches/gruszka-lowmem.patch")
"$KB" "$WORKDIR/gruszka-lowmem" 'cargo build --release --locked --offline -p gruszka -p susz'
BIN="$WORKDIR/gruszka-lowmem/target/release/gruszka"
sha256sum "$BIN"
n=$(objdump -d "$BIN" | grep -cE '\b(insertq|extrq)\b' || true)
g=$(objdump -T "$BIN" | grep -oE 'GLIBC_[0-9.]+' | sort -Vu | tail -n 1)
echo "gruszka-lowmem: insertq/extrq=$n max_glibc=$g"
[ "$n" = 0 ] || { echo "non-portable SSE4a instructions detected!"; exit 1; }

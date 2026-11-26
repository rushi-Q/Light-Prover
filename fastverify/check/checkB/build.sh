#!/bin/bash
# check/checkB/build.sh DIR [NODE_AGENT]   rebuild the check-B binaries from pinned sources + the patches in ./patches
# (offline, inside a bwrap build sandbox: Rust 1.97.1, default x86-64 target, no -C target-cpu).
# Result: DIR/bin/{gruszka,nl-fast,kcompare} + DIR/bin/SHA256SUMS. The sha256 values pinned in components.json were produced
# in one fixed build directory (gruszka embeds debug info with source paths, so another DIR gives another hash
# for gruszka; the code is the same). v4 (pinned): gruszka + nl-fast = the v3 binaries, kcompare = c620664 + patches 01+02
# (kcompare-combined.diff), whose build is bit-identical in any DIR (b2db231b...). env: CHECKB_REPOS = a directory with git
# repositories gruszka/, nano-lean/ and kcompare/ holding the pinned commits (sources/ in this repository is a snapshot),
# KBUILD = a sandboxed cargo wrapper 'KBUILD SRC_DIR CMD' (neither is shipped).
set -euo pipefail
D=$(mkdir -p "$1" && cd "$1" && pwd); H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
K=${CHECKB_REPOS:?directory with the git repositories gruszka/ nano-lean/ kcompare/}; KB=${KBUILD:?sandboxed cargo wrapper KBUILD SRC_DIR CMD}
mkdir -p "$D/src" "$D/bin" "$D/logs"; cd "$D/src"; rm -rf gruszka nano-lean kcompare; mkdir gruszka nano-lean kcompare
git -C $K/gruszka archive 4ad120b | tar -x -C gruszka          # gruszka (jasisz) + 4.36-conformance commits
git -C $K/nano-lean archive 10b28d2 | tar -x -C nano-lean      # nano-lean (sdiehl) + 4.36-conformance commits
git -C $K/kcompare archive c620664 | tar -x -C kcompare     # kcompare
for c in gruszka nano-lean kcompare; do (cd $c && patch -p1 --quiet < "$H/patches/$c-combined.diff"); done
$KB "$D/src/gruszka" 'cargo build --release --locked --offline -p gruszka -p susz' > "$D/logs/build-gruszka.log" 2>&1
$KB "$D/src/nano-lean" 'cargo build --release --locked --offline --bin nl-fast' > "$D/logs/build-nl.log" 2>&1
$KB "$D/src/kcompare" 'cargo build --release --locked --offline' > "$D/logs/build-kc.log" 2>&1
install -m 555 gruszka/target/release/gruszka nano-lean/target/release/nl-fast kcompare/target/release/kcompare "$D/bin/"
cd "$D/bin"; sha256sum gruszka kcompare nl-fast > SHA256SUMS; cat SHA256SUMS
for b in gruszka nl-fast kcompare; do   # portability: no AMD-only SSE4a (finding 001), glibc symbols <= 2.35
  n=$(objdump -d $b | grep -c -E '\b(insertq|extrq)\b' || true); g=$(objdump -T $b | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1)
  echo "$b: insertq/extrq=$n max=$g"; [ "$n" = 0 ] || { echo "non-portable instructions in $b"; exit 1; }
done

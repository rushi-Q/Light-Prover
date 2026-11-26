#!/bin/bash
# rebuild-lowmem-437.sh SRC OUT [TC37]  - the check/lowmem 4.37 recipe in a fresh dir (bwrap, no network, HOME private):
# leanc -O3 lowmem_arena.c (file-prefix-mapped) + `lake build ccmp-lowmem` with the official 4.37.0-rc1 toolchain.
set -eu
SRC=$1; OUT=$2; TC37=${3:-$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1}
rm -rf "$OUT"; mkdir -p "$OUT/src" "$OUT/home"; cp -a "$SRC"/. "$OUT/src/"; rm -rf "$OUT/src/.lake"
env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc \
  --ro-bind "$TC37" "$TC37" --bind "$OUT" "$OUT" --chdir "$OUT/src" --setenv HOME "$OUT/home" --setenv PATH "$TC37/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 \
  -- bash -c "\"$TC37/bin/leanc\" -c -O3 -Wall -Wextra -Wno-unused-parameter -ffile-prefix-map=\"$OUT/src\"=. -ffile-prefix-map=\"$TC37\"=/lean-tc -isystem /usr/include -isystem /usr/include/x86_64-linux-gnu lowmem_arena.c -o lowmem_arena.o && \"$TC37/bin/lake\" build ccmp-lowmem" > "$OUT/build.log" 2>&1
echo "host $(hostname) $(date -u +%FT%TZ); $(tail -1 "$OUT/build.log" | cut -c1-60)"
f="$OUT/src/.lake/build/bin/ccmp-lowmem"; echo "ccmp-lowmem $(sha256sum "$f" | cut -d' ' -f1) size $(stat -c %s "$f") max $(objdump -T "$f" | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1) GLIBCXX $(objdump -T "$f" | grep -o 'GLIBCXX_[0-9.]*' | sort -uV | tail -1)"

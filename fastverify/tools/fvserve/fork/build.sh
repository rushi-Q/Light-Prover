#!/bin/bash
# build.sh TC OUTDIR : build the fvfork worker with the OFFICIAL Lean toolchain TC (4.33.1; also 4.37.0-rc1) (lean -> C, leanc -> binary)
set -eu
TC=${1:?toolchain}; O=${2:?outdir}; HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
mkdir -p "$O"
cp "$HERE/FvFork.lean" "$HERE/shim.c" "$O/"
cd "$O"
LEAN_PATH=$TC/lib/lean "$TC/bin/lean" -c FvFork.c FvFork.lean
"$TC/bin/leanc" -c -O3 -DNDEBUG -o FvFork.o FvFork.c
"$TC/bin/leanc" -c -O2 -idirafter /usr/include/x86_64-linux-gnu -idirafter /usr/include -o shim.o shim.c
# link DYNAMICALLY against the toolchain's libleanshared.so like the official `lean` binary (the header snapshot's
# closures are relocated against that library; it must be the one loaded in this process). The library is split into
# libleanshared_N.so parts (4.33.1: _2 _1; 4.37.0-rc1: _3 _2 _1): link every part this toolchain has, highest first, as
# its own bin/lean does (on 4.37 a fixed list left lean_decode_lossy_utf8 undefined).
PARTS=$(cd "$TC/lib/lean" && ls libleanshared_[0-9]*.so 2>/dev/null | sed 's/^lib\(leanshared_[0-9]*\)\.so$/\1/' | sort -t_ -k2,2nr | sed 's/^/-l/' | tr '\n' ' ')
"$TC/bin/clang" --sysroot "$TC" -fuse-ld=lld -o fvfork FvFork.o shim.o -L "$TC/lib" -L "$TC/lib/glibc" -L "$TC/lib/lean" \
  -lc -lc_nonshared -Wl,--as-needed -l:ld.so -Wl,--no-as-needed -lpthread_nonshared \
  -lInit_shared $PARTS -lleanshared -Wl,-rpath,"$TC/bin/../lib/lean" -lpthread -ldl -lm -rdynamic
sha256sum fvfork

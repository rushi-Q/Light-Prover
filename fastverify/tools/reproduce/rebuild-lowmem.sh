#!/bin/bash
# rebuild-lowmem.sh BDIR - the check/lowmem/README.md recipe in a fresh dir (byte-identity of ccmp-lowmem)
set -eu
FV=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd); TC36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0; BDIR=${1:?usage: rebuild-lowmem.sh BDIR}
rm -rf "$BDIR" && mkdir -p "$BDIR"
cp -a $FV/check/sound/src/{FastParse.lean,ParAxioms.lean,CCmp.lean,CCmpMain.lean,Main.lean,PChk,lean-toolchain,lake-manifest.json} "$BDIR/"
cp -a $FV/check/lowmem/src/{lowmem_arena.c,LowMemParse.lean,CCmpLowMem.lean,CCmpLowMemMain.lean,lakefile.toml} "$BDIR/"
env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc \
  --ro-bind "$TC36" "$TC36" --bind "$BDIR" "$BDIR" --chdir "$BDIR" --setenv HOME /tmp --setenv PATH "$TC36/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 \
  -- bash -c "\"$TC36/bin/leanc\" -c -O3 -Wall -Wextra -Wno-unused-parameter -isystem /usr/include -isystem /usr/include/x86_64-linux-gnu lowmem_arena.c -o lowmem_arena.o && lake build ccmp ccmp-lowmem" > "$BDIR.log" 2>&1
sha256sum "$BDIR/.lake/build/bin/ccmp" "$BDIR/.lake/build/bin/ccmp-lowmem" "$BDIR/lowmem_arena.o"
echo "pinned: ccmp 4e82fe00f73f96c5...  ccmp-lowmem ce3a0c51a632b1c4..."
objdump -T "$BDIR/.lake/build/bin/ccmp-lowmem" | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1

#!/bin/bash
# Reproducible build recipe for pleanchecker-lowmem.
# Usage: bash build-pleanchecker-lowmem.sh WORKDIR
# Links strictly against the UNMODIFIED official Lean v4.36.0 release toolchain (GLIBC_2.17, zero dynamic libstdc++).
set -euo pipefail
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
WORKDIR=$(mkdir -p "${1:?WORKDIR}" && cd "$1" && pwd)
TC36=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
export PATH="$TC36/bin:/usr/bin:/bin"

rm -rf "$WORKDIR/pleanchecker-lowmem"
cp -a "$HERE/src/pleanchecker-lowmem" "$WORKDIR/pleanchecker-lowmem"
cd "$WORKDIR/pleanchecker-lowmem"
lake build pleanchecker
BIN="$WORKDIR/pleanchecker-lowmem/.lake/build/bin/pleanchecker"
sha256sum "$BIN"
echo "max_glibc=$(objdump -T "$BIN" 2>/dev/null | grep -oE 'GLIBC_[0-9.]+' | sort -Vu | tail -n 1)"
echo "libstdcxx_deps=$(ldd "$BIN" 2>/dev/null | grep -c 'libstdc++' || true)"

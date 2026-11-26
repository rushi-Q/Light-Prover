#!/bin/bash
# repro: olean version check. Any test host with docker (the ubuntu:24.04 image is loaded from a saved copy if missing, never pulled).
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/fhdr.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; cp -r "$H/src" "$W/src"; cd "$W/src"; export FL_BIND="$W"
echo "fast toolchain CMake: $(grep CHECK_OLEAN_VERSION /scratch/fastverify/tc/stage1/CMakeCache.txt)"
LEAN_PATH=$T33/lib/lean $T33/bin/lean -o $W/A.olean A.lean
mkdir -p $W/foreign; python3 -I -c "
import sys; b=bytearray(open(sys.argv[1],'rb').read()); i=b.find(b'819816b2e0a3bf405af45ae5c7af2491d8f5bee6'); b[i:i+40]=b'0123456789abcdef0123456789abcdef01234567'; open(sys.argv[2],'wb').write(b)" $W/A.olean $W/foreign/A.olean
echo "A.olean with a different Lean githash in its header (= an .olean written by another Lean version):"
LEAN_PATH=$W/foreign:$T33/lib/lean $T33/bin/lean B.lean > $W/o 2>&1; echo "official: rc=$? $(head -1 $W/o)"
LEAN_PATH=$W/foreign:/scratch/fastverify/tc/stage1/lib/lean "$H/fastlean" B.lean > $W/o 2>&1; echo "fast    : rc=$? $(head -1 $W/o)"

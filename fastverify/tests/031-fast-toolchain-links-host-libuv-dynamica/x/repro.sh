#!/bin/bash
# repro: libuv host dependence of the fast toolchain. Test hosts with docker (ubuntu:24.04 runs the REAL fast lean
# with the HOST's /lib/x86_64-linux-gnu/libuv.so.1 = libuv 1.43, which is what the binary dynamically links on a test host).
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/fuv.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; export PATH=$T33/bin:$PATH
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
cp -r "$H/src" "$W/src"; mkdir -p "$W/off" "$W/fast"; cd "$W/src"
FAST="$H/fastlean"; FTC=/scratch/fastverify/tc/stage1/lib/lean; export FL_BIND="$W/fast:$W/src"
echo "official lean dynamic deps on libuv/gmp: $(ldd $T33/bin/lean $T33/lib/lean/libleanshared.so 2>/dev/null | grep -cE 'libuv|libgmp') (statically linked)"
echo "fast lean dynamic deps: $(ldd /scratch/fastverify/tc/stage1/lib/lean/libleanshared.so 2>/dev/null | grep -oE 'lib(uv|gmp|stdc\+\+)[^ ]*' | sort -u | paste -sd' ') ; host: $(dpkg -l libuv1 2>/dev/null | awk '/^ii/{print $2" "$3}')"
LEAN_PATH=$T33/lib/lean $T33/bin/lean -o $W/off/UV.olean UV.lean > $W/o 2>&1; echo "official: rc=$? $(paste -sd' ' $W/o)"
LEAN_PATH=$FTC $FAST -Ddebug.skipKernelTC=true -Dlinter.all=false -o $W/fast/UV.olean UV.lean > $W/o 2>&1; echo "fast    : rc=$? $(paste -sd' ' $W/o)"
cd $W; LEAN_PATH=$W/off:$T33/lib/lean $EXP UV -- v > e.off 2>/dev/null; LEAN_PATH=$W/fast:$T33/lib/lean $EXP UV -- v > e.fast 2>/dev/null
echo "official lean4export of UV.v: official build vs fast build -> $(cmp -s e.off e.fast && echo IDENTICAL || echo DIFFERENT): $(grep -h natVal e.off) vs $(grep -h natVal e.fast)"
echo "--- libuv behaviour, not only its version: Std.IO.Process.constrainedMemory (from the official test tests/elab/async_systems_info.lean)"
cd $W/src; echo "official: $(LEAN_PATH=$T33/lib/lean $T33/bin/lean UVMem.lean 2>&1 | paste -sd' ')   fast: $(LEAN_PATH=$FTC $FAST UVMem.lean 2>&1 | paste -sd' ')"

#!/bin/bash
# repro: FunInfo.collectDeps complexity. Any x86-64 host with docker (the ubuntu:24.04 image is loaded from a saved copy if missing, never pulled).
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/ffi.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; cp -r "$H/src" "$W/src"; mkdir -p $W/off $W/fast; cd "$W/src"; export FL_BIND="$W"
FTC=/scratch/fastverify/tc/stage1/lib/lean
LEAN_PATH=$T33/lib/lean $T33/bin/lean -o $W/off/BigFn.olean BigFn.lean || exit 3
LEAN_PATH=$FTC "$H/fastlean" -o $W/fast/BigFn.olean BigFn.lean || exit 3
s=$(date +%s.%N); LEAN_PATH=$W/off:$T33/lib/lean $T33/bin/lean Probe.lean > $W/o.off 2>&1; ro=$?; to=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-5)
s=$(date +%s.%N); LEAN_PATH=$W/fast:$FTC "$H/fastlean" -Ddebug.skipKernelTC=true -Dlinter.all=false Probe.lean > $W/o.fast 2>&1; rf=$?; tf=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-5)
echo "official lean: rc=$ro (${to}s)"; sed 's/^/   /' $W/o.off | cut -c1-160 | head -6
echo "fast lean    : rc=$rf (${tf}s, incl. container start)"; sed 's/^/   /' $W/o.fast | cut -c1-160 | head -6

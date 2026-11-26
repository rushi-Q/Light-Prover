#!/bin/bash
# repro for 061: the fast toolchain's BUILD CONFIGURATION differs from the official 4.33.1 release and Lean code sees it.
# Runs the REAL deployed fast lean (/scratch/fastverify/tc/stage1, needs glibc 2.38) in a throw-away ubuntu:24.04 container
# (./fastlean) and the official 4.33.1 lean natively, on any x86-64 host, ~1 min.
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/f061.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; export PATH=$T33/bin:$PATH
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
FAST="$H/fastlean"; FTC=/scratch/fastverify/tc/stage1/lib/lean
cp -r "$H/src" "$W/src"; mkdir -p "$W/off" "$W/fast"; cd "$W/src"; export FL_BIND="$W/fast:$W/src"
echo "(1) lean --version"
echo "    official: $($T33/bin/lean --version)"
echo "    fast    : $($FAST --version)"
# the fast build uses the pipeline's LEAN_EXTRA flags (they do not matter here)
off()  { LEAN_PATH=$T33/lib/lean $T33/bin/lean "$@"; }
fast() { LEAN_PATH=$FTC $FAST -Ddebug.skipKernelTC=true -Dlinter.all=false "$@"; }
echo "(2) Tgt.lean: def buildTarget : String := platform%   (elab-time System.Platform.target) -> official lean4export of buildTarget"
off  -o $W/off/Tgt.olean  Tgt.lean > $W/o 2>&1; echo "    official build rc=$? $(head -c 300 $W/o)"
fast -o $W/fast/Tgt.olean Tgt.lean > $W/o 2>&1; echo "    fast     build rc=$? $(head -c 300 $W/o)"
cd $W; LEAN_PATH=$W/off:$T33/lib/lean $EXP Tgt -- buildTarget > e.off 2>/dev/null; LEAN_PATH=$W/fast:$T33/lib/lean $EXP Tgt -- buildTarget > e.fast 2>/dev/null
echo "    exports (official lean4export on the official vs the fast .olean): $(cmp -s e.off e.fast && echo IDENTICAL || echo DIFFERENT)"
echo "      official: $(grep -ho '"strVal":"[^"]*"' e.off)"; echo "      fast    : $(grep -ho '"strVal":"[^"]*"' e.fast)"
cd $W/src
echo "(3) Flip.lean: theorem helper : (platform% : String) = \"x86_64-pc-linux-gnu\" := rfl"
off  Flip.lean > $W/o 2>&1; echo "    official rc=$? $(grep -m1 error $W/o | cut -c1-120)"
fast Flip.lean > $W/o 2>&1; echo "    fast     rc=$? $(grep -m1 error $W/o | cut -c1-120)"
echo "(4) Ver.lean: /-- info: Lean 4.33.1 / Target: x86_64-unknown-linux-gnu -/ #guard_msgs in #version   (a toolchain-pin test)"
off  Ver.lean > $W/o 2>&1; echo "    official rc=$? $(grep -m1 -A4 error $W/o | paste -sd' ' | cut -c1-200)"
fast Ver.lean > $W/o 2>&1; echo "    fast     rc=$? $(grep -m1 -A4 error $W/o | paste -sd' ' | cut -c1-200)"
echo "(5) public Lean.Compiler.FFI.getLinkerFlags / getInternalLinkerFlags (what the toolchain was linked with)"
off  Flags.lean > $W/o 2>&1; echo "    official: $(paste -sd' ' $W/o | cut -c1-400)"
fast Flags.lean > $W/o 2>&1; echo "    fast    : $(paste -sd' ' $W/o | cut -c1-400)"
echo "(6) C++ standard library inside libleanshared.so: official $(nm -D $T33/lib/lean/libleanshared.so | grep -c '@GLIBCXX') GLIBCXX imports (libc++ linked statically), fast $(nm -D /scratch/fastverify/tc/stage1/lib/lean/libleanshared.so | grep -c '@GLIBCXX') GLIBCXX imports (dynamic host libstdc++.so.6)"

#!/bin/bash
# repro for finding 005. Run on a host with docker (the ubuntu:24.04 image is loaded from a saved copy if missing, never pulled); elsewhere falls back
# to a native build of 7586a50cec (same Lean sources).
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/f005.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; export PATH=$T33/bin:$PATH
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
cp -r "$H/src" "$W/src"; mkdir -p "$W/off" "$W/fast"; cd "$W/src"
if docker info >/dev/null 2>&1; then FAST="$H/fastlean"; FTC=/scratch/fastverify/tc/stage1/lib/lean; export FL_BIND="$W/fast:$W/src"; echo "FAST = /scratch/fastverify/tc/stage1 (real binary in ubuntu:24.04 container)"
else FAST=/scratch/fast-tc/7586/bin/lean; FTC=/scratch/fast-tc/7586/lib/lean; echo "FAST = FALLBACK /scratch/fast-tc/7586"; fi
for m in Scopes RawState; do
  LEAN_PATH=$T33/lib/lean $T33/bin/lean -o $W/off/$m.olean $m.lean > $W/off.$m.out 2>&1; ro=$?
  LEAN_PATH=$FTC $FAST -Ddebug.skipKernelTC=true -Dlinter.all=false -o $W/fast/$m.olean $m.lean > $W/fast.$m.out 2>&1; rf=$?
  echo "== $m.lean: official rc=$ro: $(paste -sd' ' $W/off.$m.out | cut -c1-200)"
  echo "== $m.lean: fast     rc=$rf: $(paste -sd' ' $W/fast.$m.out | cut -c1-200)"
done
cd $W; LEAN_PATH=$W/off:$T33/lib/lean $EXP Scopes -- n1 n2 > off.export 2>/dev/null; LEAN_PATH=$W/fast:$T33/lib/lean $EXP Scopes -- n1 n2 > fast.export 2>/dev/null
echo "official lean4export of Scopes (n1 n2): official build $(sha256sum < off.export | cut -c1-16) / fast build $(sha256sum < fast.export | cut -c1-16) -> $(cmp -s off.export fast.export && echo IDENTICAL || echo DIFFERENT)"
diff <(grep natVal off.export) <(grep natVal fast.export)
echo "--- (c) official Lean test tests/elab/binopInfoTree.lean (v4.33.1, set_option trace.Elab.info true): the pretty printer forces the"
echo "    lazy coe-extension state inside a (sync := true) task -> panic 'Task.get called from a (sync := true) task'"
cd $W/src
for ab in "" 1; do
  if [ -n "$ab" ]; then export LEAN_ABORT_ON_PANIC=1; else unset LEAN_ABORT_ON_PANIC; fi
  LEAN_PATH=$T33/lib/lean $T33/bin/lean BinopInfoTree.lean > $W/o.off 2>&1; ro=$?
  LEAN_PATH=$FTC $FAST BinopInfoTree.lean > $W/o.fast 2>&1; rf=$?
  echo "LEAN_ABORT_ON_PANIC=${ab:-unset}: official rc=$ro panics=$(grep -c 'Task.get' $W/o.off)  fast rc=$rf panics=$(grep -c 'Task.get' $W/o.fast) $(grep -m1 -o 'Lean.ScopedEnvExtension.getState[^)]*' $W/o.fast)"
done
unset LEAN_ABORT_ON_PANIC
echo "--- (d) a SCOPED instance registered (public Meta.addInstance) for the namespace _lazyImportedState.3141592653, which is never"
echo "    opened: officially inactive; in the fast toolchain every lazily imported state carries that name in activeScopes, so"
echo "    the scoped entry is applied immediately -> instance resolution changes (default : Nat) from 0 to 42"
cd $W/src
LEAN_PATH=$T33/lib/lean $T33/bin/lean ScopedMarker.lean > $W/o.off 2>&1; ro=$?
LEAN_PATH=$FTC $FAST -Ddebug.skipKernelTC=true -Dlinter.all=false ScopedMarker.lean > $W/o.fast 2>&1; rf=$?
echo "official: rc=$ro #eval (default : Nat) = $(sed -n 1p $W/o.off); $(grep -m1 -o 'error: [^:]*' $W/o.off)"
echo "fast    : rc=$rf #eval (default : Nat) = $(sed -n 1p $W/o.fast); $(grep -c error $W/o.fast) errors (theorem t : (default : Nat) = 42 := rfl accepted)"
echo "--- (e) liveness: user simple scoped extension (LA) whose addEntry diverges only when entries from two modules meet;"
echo "    LB1/LB2 add one entry each; LC imports both and never uses the extension (60 s limit)"
cd $W/src; mkdir -p $W/off $W/fast
for m in LA LB1 LB2; do LEAN_PATH=$W/off:$T33/lib/lean $T33/bin/lean -o $W/off/$m.olean $m.lean > /dev/null 2>&1; LEAN_PATH=$W/fast:$FTC $FAST -o $W/fast/$m.olean $m.lean > /dev/null 2>&1; done
s=$(date +%s); LEAN_PATH=$W/off:$T33/lib/lean timeout 60 $T33/bin/lean LC.lean > /dev/null 2>&1; ro=$?; to=$(( $(date +%s) - s ))
s=$(date +%s); LEAN_PATH=$W/fast:$FTC timeout 60 $FAST -Ddebug.skipKernelTC=true -Dlinter.all=false LC.lean > /dev/null 2>&1; rf=$?; tf=$(( $(date +%s) - s ))
echo "official lean on LC: rc=$ro after ${to}s (124 = killed by the 60 s timeout: the eager import fold never terminates)"
echo "fast     lean on LC: rc=$rf after ${tf}s (lazy state never forced)"

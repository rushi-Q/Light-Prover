#!/bin/bash
# repro for finding 004: run on a host with docker (the ubuntu:24.04 image is loaded from a saved copy if missing, never pulled), else the fallback below.
# OFFICIAL = original Lean 4.33.1 (~/.elan toolchain).  FAST = the fast flow's build toolchain
#   /scratch/fastverify/tc/stage1 (lean4 d5e35ef223) run unmodified inside an ubuntu:24.04 container (it needs glibc 2.38;
#   the test hosts have 2.35), with the pipeline's LEAN_EXTRA flags -Ddebug.skipKernelTC=true -Dlinter.all=false.
#   Fallback if docker/ubuntu:24.04 is unavailable: a native build of 7586a50cec (= the same
#   sources minus the PGO build commits).
# Export = official lean4export v4.33.0 with the official 4.33.1 core library on LEAN_PATH (as pipeline/export.sh does).
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/f004.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
export PATH=$T33/bin:$PATH
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
cp -r "$H/src" "$W/src"; mkdir -p "$W/off" "$W/fast"
if docker info >/dev/null 2>&1; then
  FAST="$H/fastlean"; FTC=/scratch/fastverify/tc/stage1/lib/lean; export FL_BIND="$W/fast:$W/src"; echo "FAST toolchain: /scratch/fastverify/tc/stage1 (real binary, ubuntu:24.04 container)"
else
  FAST=/scratch/fast-tc/7586/bin/lean; FTC=/scratch/fast-tc/7586/lib/lean; echo "FAST toolchain: FALLBACK /scratch/fast-tc/7586 (7586a50cec native build)"
fi
build() { # $1=off|fast $2=module ; prints rc
  cd "$W/src"
  if [ $1 = off ]; then LEAN_PATH=$W/off:$T33/lib/lean $T33/bin/lean -o $W/off/$2.olean $2.lean > $W/$1.$2.out 2>&1; else
    LEAN_PATH=$W/fast:$FTC $FAST -Ddebug.skipKernelTC=true -Dlinter.all=false -o $W/fast/$2.olean $2.lean > $W/$1.$2.out 2>&1; fi
  echo $?
}
for m in A B C; do ro=$(build off $m); rf=$(build fast $m); echo "build $m: official rc=$ro  fast rc=$rf"; done
echo "--- (1) same module C.lean (three 'def xi : Nat := tick'), both builds succeed:"
echo "official: $(grep -A1 '^def x' $W/off.C.out | grep -v -- -- | paste -sd' ')"
echo "fast    : $(grep -A1 '^def x' $W/fast.C.out | grep -v -- -- | paste -sd' ')"
cd "$W"; LEAN_PATH=$W/off:$T33/lib/lean $EXP C -- x1 x2 x3 > off.C.export 2>/dev/null; LEAN_PATH=$W/fast:$T33/lib/lean $EXP C -- x1 x2 x3 > fast.C.export 2>/dev/null
echo "official lean4export of C (x1 x2 x3): official build sha256 $(sha256sum < off.C.export | cut -c1-16), fast build sha256 $(sha256sum < fast.C.export | cut -c1-16) -> $(cmp -s off.C.export fast.C.export && echo IDENTICAL || echo DIFFERENT)"
diff <(grep -E '"natVal"|"name":"x[123]"' off.C.export) <(grep -E '"natVal"|"name":"x[123]"' fast.C.export) | head -6
echo "--- (2) nondeterminism: D.lean = 16 x 'theorem pi : ∃ n : Nat, n = n := ⟨tick, rfl⟩' (proofs elaborated on worker threads); witnesses per run:"
for r in 1 2 3; do build off D > /dev/null; echo "official run $r: $(grep -o 'intro [0-9]*' $W/off.D.out | cut -d' ' -f2 | paste -sd' ')"; done
for r in 1 2 3; do build fast D > /dev/null; echo "fast     run $r: $(grep -o 'intro [0-9]*' $W/fast.D.out | cut -d' ' -f2 | paste -sd' ')"; done
echo "--- (3) accept/reject: E.lean = 'theorem main_thm : 2 + 2 = 4 := by tick_bump; tick_or_fail'"
ro=$(build off E); rf=$(build fast E)
echo "official build of E: rc=$ro  $(head -1 $W/off.E.out)"
echo "fast     build of E: rc=$rf  $(head -1 $W/fast.E.out)"
if [ "$rf" = 0 ]; then
  cd "$W"; LEAN_PATH=$W/fast:$T33/lib/lean $EXP E -- main_thm > fast.E.export 2>/dev/null
  $T36/bin/leanchecker --from-export fast.E.export > lc.out 2>&1; echo "official 4.36 leanchecker --from-export on the FAST export of E: rc=$? $(tail -1 lc.out)"
fi
echo "--- (4) root cause check: the same fast binary with the interpreter pool AND the cross-instance constant cache switched off"
echo "    (LEAN_INTERP_NO_POOL=1 LEAN_INTERP_NO_CONST_CACHE=1; either one alone is NOT enough):"
export LEAN_INTERP_NO_POOL=1 LEAN_INTERP_NO_CONST_CACHE=1; build fast C > /dev/null; unset LEAN_INTERP_NO_POOL LEAN_INTERP_NO_CONST_CACHE
echo "fast+switches: $(grep -A1 '^def x' $W/fast.C.out | grep -v -- -- | paste -sd' ')"
echo "VERDICT: official flow REJECTS E (build error, rc=$ro); fast flow builds it (rc=$rf) and its export is accepted by the official kernel."
echo "--- (5) PURE code, no unsafe: HA.lean 'def table : Array Nat := (List.range 400000).toArray'; HB.lean tactics touch_table/use_table"
echo "    read it; HC.lean 'set_option maxHeartbeats 800 in theorem t : 2 + 2 = 4 := by touch_table; touch_table; use_table'."
echo "    Official re-evaluates the closed term in every interpreter entry (3x allocations = heartbeats), fast once per thread."
for m in HA HB; do build off $m > /dev/null; build fast $m > /dev/null; done
ro=$(build off HC); rf=$(build fast HC)
echo "official build of HC: rc=$ro $(head -1 $W/off.HC.out | cut -c1-120)"
echo "fast     build of HC: rc=$rf $(head -1 $W/fast.HC.out | cut -c1-120)"
echo "--- (6) PURE code nondeterminism: ND.lean = 24 x 'set_option maxHeartbeats 200 in theorem pi : 2 + 2 = 4 := by use_table'"
echo "    (cold thread: the closed term is evaluated -> over the limit; warm thread: cached -> passes). Failing theorems per run:"
for r in 1 2; do build off ND > /dev/null; echo "official run $r: $(grep -oE '^ND.lean:[0-9]+' $W/off.ND.out | sed 's/ND.lean://' | awk '{printf "p%d ", $1/2}')"; done
for r in 1 2 3; do build fast ND > /dev/null; echo "fast     run $r: $(grep -oE '^ND.lean:[0-9]+' $W/fast.ND.out | sed 's/ND.lean://' | awk '{printf "p%d ", $1/2}')"; done

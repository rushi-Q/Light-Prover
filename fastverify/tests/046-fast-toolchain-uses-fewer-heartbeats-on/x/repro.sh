#!/bin/bash
# repro: heartbeat consumption of the fast toolchain on an ordinary Mathlib proof. Any x86-64 host (docker; the REAL fast
# lean in an ubuntu:24.04 container). Copies the ~180 MB import closure of the Mathlib cache (verify/challenge/.lake/packages,
# read-only) to a node-local temp dir (docker cannot read the NFS home). ~3 min.
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/fhbm.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; P=$LIGHT_LEAN/verify/challenge/.lake/packages
LP=$(ls -d $P/*/.lake/build/lib/lean | paste -sd:); FTC=/scratch/fastverify/tc/stage1/lib/lean
cp -r "$H/src" "$W/src"; cd "$W/src"
LEAN_PATH=$LP:$T33/lib/lean $T33/bin/lean --run "$H/Closure.lean" Mathlib.Tactic.Ring Mathlib.Tactic.Linarith > $W/closure.txt || exit 3
mkdir -p $W/pkg; grep "/packages/" $W/closure.txt | sed -E 's|^(.*/lib/lean)/(.*)\.olean$|\1 \2|' | while read root rel; do
  mkdir -p "$W/pkg/$(dirname $rel)"; cp "$root/$rel".olean* "$root/$rel".ir* "$W/pkg/$(dirname $rel)/" 2>/dev/null; done
echo "copied $(find $W/pkg -type f | wc -l) package files ($(du -sh $W/pkg | cut -f1))"
export FL_BIND="$W"
run() { # $1=off|fast $2=maxHeartbeats -> rc
  sed "s/HB/$2/" Proof.lean > P$1.lean
  if [ $1 = off ]; then LEAN_PATH=$W/pkg:$T33/lib/lean $T33/bin/lean P$1.lean > $W/o.$1 2>&1
  else LEAN_PATH=$W/pkg:$FTC "$H/fastlean" -Ddebug.skipKernelTC=true -Dlinter.all=false P$1.lean > $W/o.$1 2>&1; fi; echo $?; }
for k in off fast; do lo=2000; hi=4000; while [ $((hi-lo)) -gt 1 ]; do mid=$(((lo+hi)/2)); if [ "$(run $k $mid)" = 0 ]; then hi=$mid; else lo=$mid; fi; done; eval min_$k=$hi; done
echo "minimal maxHeartbeats with which the proof builds: official $min_off, fast $min_fast"
m=$(( (min_off + min_fast) / 2 ))
ro=$(run off $m); rf=$(run fast $m)
echo "with 'set_option maxHeartbeats $m': official rc=$ro $(grep -m1 -o 'error: .*heartbeats ([0-9]*)' $W/o.off) | fast rc=$rf"

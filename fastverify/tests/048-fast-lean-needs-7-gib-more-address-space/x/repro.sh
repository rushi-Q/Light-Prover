#!/bin/bash
# repro: virtual address space needed by the official vs the REAL fast lean to import (part of) Mathlib.
# Any x86-64 host (docker). Copies the Mathlib.Tactic.{Ring,Linarith} import closure of the Mathlib cache to a node-local temp
# dir (docker cannot read the NFS home), then binary-searches the smallest `ulimit -v` with which the module builds.
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/fas.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; P=$LIGHT_LEAN/verify/challenge/.lake/packages
LP=$(ls -d $P/*/.lake/build/lib/lean | paste -sd:); FTC=/scratch/fastverify/tc/stage1/lib/lean
cp -r "$H/src" "$W/src"; cd "$W/src"
LEAN_PATH=$LP:$T33/lib/lean $T33/bin/lean --run "$H/Closure.lean" Mathlib.Tactic.Ring Mathlib.Tactic.Linarith > $W/closure.txt || exit 3
mkdir -p $W/pkg; grep "/packages/" $W/closure.txt | sed -E 's|^(.*/lib/lean)/(.*)\.olean$|\1 \2|' | while read root rel; do
  mkdir -p "$W/pkg/$(dirname $rel)"; cp "$root/$rel".olean* "$root/$rel".ir* "$W/pkg/$(dirname $rel)/" 2>/dev/null; done
IMG=${FV_DOCKER_IMAGE:-$LIGHT_LEAN/repro-bin/ubuntu-24.04.tar}
docker image inspect ubuntu:24.04 >/dev/null 2>&1 || docker load -q -i "$IMG" >/dev/null
okoff() { bash -c "ulimit -v $(($1*1024)); LEAN_PATH=$W/pkg:$T33/lib/lean $T33/bin/lean Imp.lean > $W/o.off 2>&1"; }
okfast() { docker run --rm --pull never --network none -u "$(id -u):$(id -g)" -v /scratch/fastverify:/scratch/fastverify:ro \
  -v /lib/x86_64-linux-gnu/libuv.so.1:/hostlib/libuv.so.1:ro \
  -v $W:$W -w $W/src -e LD_LIBRARY_PATH=/hostlib -e LEAN_PATH=$W/pkg:$FTC ubuntu:24.04 \
  bash -c "ulimit -v $(($1*1024)); /scratch/fastverify/tc/stage1/bin/lean Imp.lean" > $W/o.fast 2>&1; }
for k in off fast; do lo=2048; hi=32768; while [ $((hi-lo)) -gt 256 ]; do mid=$(((lo+hi)/2)); if ok$k $mid; then hi=$mid; else lo=$mid; fi; done; eval min_$k=$hi; done
echo "smallest 'ulimit -v' (MiB, +-256) with which 'import Mathlib.Tactic.Ring/Linarith' builds: official $min_off, fast $min_fast"
m=$(( (min_off + min_fast) / 2 ))
okoff $m; ro=$?; okfast $m; rf=$?
echo "with ulimit -v ${m} MiB: official rc=$ro | fast rc=$rf $(grep -m1 -o 'what():.*' $W/o.fast)"

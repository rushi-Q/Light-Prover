#!/bin/bash
# kernelon-rebuild.sh MODULE_NAME [MODULE_NAME...] - does the OFFICIAL Lean 4.37 build (elaboration + build-time kernel
# check, no transforms) of the module(s) declaring the stuck theorems finish, and how long does it take? Reflink copy of
# a cache-restored community tree (XFS, seconds), the module's build outputs removed, `lake build +Module` with the official
# 4.37 toolchain inside bwrap (no network; everything else up to date, so exactly these modules are re-elaborated and
# kernel-checked), wall time + max RSS per module. Untrusted diagnostic (nothing here produces a verdict).
set -u
SRC=${FV_RHC_TREE:-${FV_BENCH_INPUTS:-/scratch/bench-inputs}/rh437/proj}; W=${FV_WORK:-${TMPDIR:-/tmp}}/kernelon; TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.37.0-rc1
mkdir -p $W; [ -d $W/proj ] || { t0=$(date +%s); cp -a --reflink=always $SRC $W/proj || cp -a $SRC $W/proj; echo "[kon] tree copied in $(( $(date +%s) - t0 )) s"; }
for M in "$@"; do
  rel=$(echo "$M" | tr . /); L=$W/proj/.lake/build/lib/lean
  rm -f $L/$rel.olean $L/$rel.olean.private $L/$rel.olean.server $L/$rel.ilean $L/$rel.olean.hash $L/$rel.ilean.hash $L/$rel.trace $W/proj/.lake/build/ir/$rel.c $W/proj/.lake/build/ir/$rel.c.hash 2>/dev/null
  t0=$(date +%s)
  /usr/bin/time -f "%e s wall, %U s user, %M KB maxrss" -o $W/$M.time /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc --ro-bind $TC $TC --bind $W/proj $W/proj --chdir $W/proj --clearenv --setenv PATH $TC/bin:/usr/bin:/bin --setenv HOME /tmp --setenv LEAN_ABORT_ON_PANIC 1 --setenv LANG C.UTF-8 -- timeout --kill-after=10 1800 $TC/bin/lake build +$M > $W/$M.out 2>&1; rc=$?
  echo "$M rc=$rc $(cat $W/$M.time 2>/dev/null) ($(( $(date +%s) - t0 )) s incl. lake)" | tee -a $W/results.txt
  grep -n "error\|kernel\|deterministic timeout" $W/$M.out | head -3
done

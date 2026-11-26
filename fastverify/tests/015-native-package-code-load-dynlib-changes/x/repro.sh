#!/bin/bash
# Self-contained repro (~6 min, run with >= 48 cores, e.g. `repro.sh WORKDIR`):
# OFFICIAL flow (lake build 4.33.1 + official lean4export + lake comparator 4.36) vs FAST flow (fastverify/pipeline/pipeline.sh
# with its default native package code ON + pchk run.sh) on the crafted project ./proj with the challenge ./challenge.
# Step 0 shows the mechanism directly: the same file elaborated by the same official lean with and without the pipeline's
# --load-dynlib=libpkgs.so (built by the pipeline's own native.sh from the trusted Mathlib cache).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-015}; R=$LIGHT_LEAN
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W"); cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"
echo "=== STEP 0: same official lean 4.33.1, Aesop interpreted vs native (libpkgs.so from fastverify/pipeline/native.sh)"
bash $R/fastverify/pipeline/native.sh $R/verify/challenge/.lake/packages "$W/native" 48 "$W/native.ready" > "$W/native.log" 2>&1
tail -1 "$W/native.log"
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; P=$R/verify/challenge/.lake/packages
LP=$(for d in $P/*/.lake/build/lib/lean; do printf '%s:' $d; done)$T33/lib/lean
sed '/^import Delay/d' "$D/proj/src/Main.lean" > "$W/M.lean"
( cd "$W" && LEAN_PATH=$LP $T33/bin/lean M.lean > M.interp 2>&1; echo "interpreted (official lake build mode): lean rc=$?"; grep -m1 timeout M.interp )
( cd "$W" && LEAN_PATH=$LP $T33/bin/lean $(cat native.ready) M.lean > M.native 2>&1; echo "native (fast pipeline mode, $(cat native.ready)): lean rc=$?"; grep -m1 timeout M.native )
echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"

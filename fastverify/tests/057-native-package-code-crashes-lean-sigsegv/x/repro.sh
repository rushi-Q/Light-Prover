#!/bin/bash
# Self-contained repro (~10 min; needs ~10 GB on /scratch for the official side's Mathlib cache copy):
#   bash repro.sh [WORKDIR]   (48 CPUs)
# STEP 0: same official lean 4.33.1, interpreted vs with the pipeline's --load-dynlib=libpkgs.so (built by its own native.sh):
#   step0/ModMathlib.lean   = 'module / import Mathlib'                (crashes natively even with the pipeline's flags)
#   step0/PlainMathlib.lean = 'import Mathlib'                         (control: no crash)
#   step0/ModDocLinter.lean = module + docstring (Mathlib docstring linter; crashes natively unless -Dlinter.all=false)
# Then the OFFICIAL flow and the FAST flow (pipeline.sh, natives ON) on ./proj: module files A1-A3 import Mathlib.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-057}; R=$LIGHT_LEAN
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W"); cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"; cp -a "$D/step0" "$W/step0"
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; P=$R/verify/challenge/.lake/packages
LP=$(for d in $P/*/.lake/build/lib/lean; do printf '%s:' $d; done)$T33/lib/lean
PF="--tstack=400000 -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true -DmaxHeartbeats=4000000 -Ddebug.skipKernelTC=true -Dlinter.all=false"
echo "=== STEP 0: official lean 4.33.1, interpreted vs native package code"
bash $R/fastverify/pipeline/native.sh $P "$W/native" 48 "$W/native.ready" > "$W/native.log" 2>&1; tail -1 "$W/native.log"
cd "$W/step0"
for f in ModMathlib PlainMathlib ModDocLinter; do
  for flags in "" "$PF"; do
    LEAN_PATH=$LP $T33/bin/lean $flags -R . $f.lean -o $f.i.olean > /dev/null 2>&1; ri=$?
    LEAN_PATH=$LP $T33/bin/lean $flags $(cat "$W/native.ready") -R . $f.lean -o $f.n.olean > /dev/null 2>&1; rn=$?
    echo "$f.lean flags=[$([ -n "$flags" ] && echo pipeline || echo default)]: interpreted rc=$ri  native rc=$rn"
  done
done 2>&1 | grep -v Segmentation
cd "$W"
echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "--- fast scheduler native handling:"; grep -E "NATIVE|retry .* without native" "$W/fast/run/log/sched.log" | cut -c1-160
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"

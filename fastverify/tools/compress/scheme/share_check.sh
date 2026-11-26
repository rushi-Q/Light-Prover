#!/bin/bash
# share_check.sh EXPORT OUTDIR [THREADS] -- export-level sharing (exphash/share.sh: semantic classes, cheapest acyclic
# representative, challenge constants never redirected) of an accepted candidate export + the TRUSTED check of the result
# against the official challenge (check-sound.sh). cwd = ship dir (fv/, bin/{exphash,expcompress}, tools/exphash).
# env: RH_CHALLENGE (challenge workspace, default $LIGHT_LEAN/verify/challenge).
set -u
S=$(pwd); EXP=$1; OUT=$2; T=${3:-128}; WS=${RH_CHALLENGE:-$LIGHT_LEAN/verify/challenge}
mkdir -p $OUT; t0=$(date +%s)
EXPHASH_BIN=$S/bin bash $S/tools/exphash/share.sh "$EXP" $WS/challenge.export $WS/comparator.json $OUT > $OUT/share.out 2>&1
echo "share rc=$? $(( $(date +%s) - t0 )) s"; tail -5 $OUT/share.out
ls -l "$EXP" $OUT/solution.export; sha256sum $OUT/solution.export | tee $OUT/solution.export.sha256
t0=$(date +%s)
$S/fv/check/sound/check-sound.sh $OUT/solution.export $WS/challenge.export $WS/comparator.json --threads $T --log $OUT/check.log --json $OUT/check.json | tail -3
echo "check-sound rc=$? $(( $(date +%s) - t0 )) s"; cat $OUT/check.json 2>/dev/null | head -c 1500

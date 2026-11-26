#!/bin/bash
# sweep_check.sh OUTDIR LABEL INDIR CPUBASE "T1 T2 ..." [MEM1 MEM2 ...]
#   export-in trusted check (check/sound/check-sound.sh) of INDIR/solution.export against INDIR/challenge/{challenge.export,
#   comparator.json}, once per thread count T (cpuset = CPUBASE..CPUBASE+T-1, memory unlimited), then optionally once per
#   memory limit MEM (at the LAST thread count). One cgrun JSON per run in OUTDIR/<LABEL>.T<T>[.M<MEM>].json; a run whose
#   JSON exists is skipped (restartable after an interruption). Env: CHECK_SH (default the package's check-sound.sh),
#   CHECK_ARGS (extra arguments, e.g. "--pins /path/pins-437.env" for a staged check).
set -u
OUT=$1; LABEL=$2; IN=$3; CPUBASE=$4; TS=$5; shift 5; MEMS=("$@")
FV=${FV:-$LIGHT_LEAN/fastverify}
CG=${CGRUN:-$(dirname "$(readlink -f "$0")")/cgrun.sh}
CS=${CHECK_SH:-$FV/check/sound/check-sound.sh}   # another check script (e.g. a staged check-sound.sh) + its extra args
read -r -a CSARGS <<< "${CHECK_ARGS:-}"
mkdir -p "$OUT"
E=$IN/solution.export; C=$IN/challenge/challenge.export; J=$IN/challenge/comparator.json
run1() { # tag threads mem
  local tag=$1 t=$2 mem=$3 cpus
  [ -s "$OUT/$tag.json" ] && { echo "skip $tag"; return; }
  cpus="$CPUBASE-$(( CPUBASE + t - 1 ))"
  echo "$(date -u +%FT%TZ) start $tag threads=$t cpus=$cpus mem=$mem"
  "$CG" --name "sw-$tag" --cpus "$cpus" --mem "$mem" --json "$OUT/$tag.json.part" --timeline "$OUT/$tag.tl" --timeout 7200 -- \
     "$CS" "$E" "$C" "$J" --threads "$t" --log "$OUT/$tag.log" "${CSARGS[@]}" > "$OUT/$tag.out" 2>&1
  local rc=$?
  mv "$OUT/$tag.json.part" "$OUT/$tag.json"
  echo "$(date -u +%FT%TZ) done  $tag rc=$rc $(tail -1 "$OUT/$tag.out" | cut -c1-160)"
}
last=
for t in $TS; do run1 "$LABEL.T$t" "$t" max; last=$t; done
for m in "${MEMS[@]}"; do run1 "$LABEL.T$last.M$m" "$last" "$m"; done
echo SWEEP_DONE

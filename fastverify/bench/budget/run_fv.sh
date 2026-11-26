#!/bin/bash
# run_fv.sh OUTDIR TAG CPUS MEM THREADS PROJECT CHALLENGE [fastverify args...]
#   one `bin/fastverify PROJECT CHALLENGE OUTDIR/TAG` run inside a cgroup leaf (cpuset CPUS, memory.max MEM) with the
#   stage timeline sampled; records OUTDIR/TAG.cg.json (cgrun), OUTDIR/TAG.fv.log (orchestrator log) and copies
#   OUTDIR/TAG/result.json -> OUTDIR/TAG.result.json. --challenge-sha256 is added when CHALLENGE/challenge.export.sha256
#   exists. Existing OUTDIR/TAG.cg.json = skipped. Environment: FV (package root), WS (trusted workspace).
set -u
OUT=$1; TAG=$2; CPUS=$3; MEM=$4; T=$5; PROJ=$6; CHAL=$7; shift 7
FV=${FV:-$LIGHT_LEAN/fastverify}
WS=${WS:-$LIGHT_LEAN/verify/challenge}
CG=${CGRUN:-$(dirname "$(readlink -f "$0")")/cgrun.sh}
mkdir -p "$OUT"
[ -s "$OUT/$TAG.cg.json" ] && { echo "skip $TAG"; exit 0; }
EXTRA=()
[ -f "$CHAL/challenge.export.sha256" ] && EXTRA=(--challenge-sha256 "$(cut -d' ' -f1 "$CHAL/challenge.export.sha256")")
rm -rf "$OUT/$TAG"
echo "$(date -u +%FT%TZ) start $TAG cpus=$CPUS mem=$MEM threads=$T $*"
"$CG" --name "fv-$TAG" --cpus "$CPUS" --mem "$MEM" ${PS:+--ps $PS} --json "$OUT/$TAG.cg.json.part" --timeline "$OUT/$TAG.tl" --timeout "${TIMEOUT:-14400}" -- \
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$PROJ" "$CHAL" "$OUT/$TAG" --threads "$T" --packages "$WS" "${EXTRA[@]}" "$@" > "$OUT/$TAG.fv.log" 2>&1
rc=$?
mv "$OUT/$TAG.cg.json.part" "$OUT/$TAG.cg.json"
[ -f "$OUT/$TAG/result.json" ] && cp "$OUT/$TAG/result.json" "$OUT/$TAG.result.json"
echo "$(date -u +%FT%TZ) done  $TAG rc=$rc $(grep -a -m1 'fastverify: verdict' "$OUT/$TAG.fv.log" | cut -c1-200)"
exit 0

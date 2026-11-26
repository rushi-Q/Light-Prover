#!/bin/bash
# swarm_check.sh OUTDIR TAG INDIR N THREADS CPUS MEM
#   N CONCURRENT export-in trusted checks (check/sound/check-sound.sh, THREADS each) of INDIR/solution.export inside ONE
#   limited scope (cpuset CPUS, memory.max MEM) = N clients sharing a machine / a CI runner. Records per run: verdict, wall,
#   exit; for the group: cgrun JSON (peak, OOM kills, CPU). Output: OUTDIR/TAG.cg.json, OUTDIR/TAG.runs.tsv, OUTDIR/TAG.r<i>.*
set -u
OUT=$1; TAG=$2; IN=$3; N=$4; T=$5; CPUS=$6; MEM=$7
FV=${FV:-$LIGHT_LEAN/fastverify}
CG=${CGRUN:-$(dirname "$(readlink -f "$0")")/cgrun.sh}
mkdir -p "$OUT"
[ -s "$OUT/$TAG.cg.json" ] && { echo "skip $TAG"; exit 0; }
E=$IN/solution.export; C=$IN/challenge/challenge.export; J=$IN/challenge/comparator.json
cat > "$OUT/$TAG.inner.sh" <<EOF
#!/bin/bash
cd "$OUT"
: > "$TAG.runs.tsv"
for i in \$(seq 1 $N); do
  ( t0=\$(date +%s.%N); "$FV/check/sound/check-sound.sh" "$E" "$C" "$J" --threads $T --log "$TAG.r\$i.log" > "$TAG.r\$i.out" 2>&1; rc=\$?; t1=\$(date +%s.%N)
    v=\$(grep -o '"verdict":"[A-Z_]*"' "$TAG.r\$i.out" | tail -1 | cut -d'"' -f4)
    why=\$(grep -o '"reason":"[^"]*"' "$TAG.r\$i.out" | tail -1 | cut -c1-120)
    printf '%s\t%s\t%s\t%.1f\t%s\n' "\$i" "\$rc" "\${v:-none}" "\$(echo "\$t1 - \$t0" | bc)" "\$why" >> "$TAG.runs.tsv" ) &
done
wait
echo SWARM_DONE
EOF
chmod +x "$OUT/$TAG.inner.sh"
echo "$(date -u +%FT%TZ) start $TAG N=$N threads=$T cpus=$CPUS mem=$MEM"
"$CG" --name "sw-$TAG" --cpus "$CPUS" --mem "$MEM" --ps 2 --json "$OUT/$TAG.cg.json.part" --timeline "$OUT/$TAG.tl" --timeout 7200 -- "$OUT/$TAG.inner.sh" > "$OUT/$TAG.out" 2>&1
rc=$?
mv "$OUT/$TAG.cg.json.part" "$OUT/$TAG.cg.json" 2>/dev/null
echo "$(date -u +%FT%TZ) done  $TAG rc=$rc"; sort -n "$OUT/$TAG.runs.tsv" | cut -c1-160

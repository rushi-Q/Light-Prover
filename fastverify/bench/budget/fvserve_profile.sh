#!/bin/bash
# fvserve_profile.sh STATE PSET ATTEMPTS_DIR OUTDIR [N_SEQ] [CONC] : latency (one attempt at a time) and burst throughput
#   of a running fvserve, with the service scope's memory before/after/peak (scope name contains "fvserve-").
set -u
S=$1; P=$2; A=$3; OUT=$4; NSEQ=${5:-20}; CONC=${6:-8}; mkdir -p "$OUT"
FC="/usr/bin/python3 -I $LIGHT_LEAN/fastverify/tools/fvserve/fvclient.py"
d=$(ls -d /sys/fs/cgroup/system.slice/cgrun-*fvserve-* 2>/dev/null | head -1)
mem() { echo "current $(cat $d/memory.current 2>/dev/null) peak $(cat $d/memory.peak 2>/dev/null)"; }
echo "scope $d idle: $(mem)"
t0=$(date +%s.%N); $FC seq --state "$S" --pset "$P" "$A" --n "$NSEQ" --out "$OUT/seq.tsv" > "$OUT/seq.out" 2>&1; echo "seq rc=$? wall=$(echo "$(date +%s.%N) - $t0" | bc) : $(mem)"
tail -3 "$OUT/seq.out" | cut -c1-200
t0=$(date +%s.%N); $FC burst --state "$S" --pset "$P" "$A" --conc "$CONC" --out "$OUT/burst.tsv" > "$OUT/burst.out" 2>&1; echo "burst rc=$? wall=$(echo "$(date +%s.%N) - $t0" | bc) : $(mem)"
tail -3 "$OUT/burst.out" | cut -c1-200
/usr/bin/python3 -I $LIGHT_LEAN/fastverify/tools/fvserve/fvserve.py stats --state "$S" 2>/dev/null | cut -c1-400
echo PROFILE_DONE

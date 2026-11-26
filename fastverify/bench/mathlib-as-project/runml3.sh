#!/bin/bash
# runml.sh CASE PRESET THREADS [TAGSUFFIX] [extra fastverify args...] : run one Mathlib-as-project case through bin/fastverify
# on this host. Inputs $R/{proj,chal}/CASE; output $R/runs/CASE.PRESET[TAGSUFFIX]; summary line appended to
# $R/runs/summary.tsv (R defaults to a site directory; set it)
set -u
CASE=$1; PRESET=$2; THREADS=$3; SUF=${4:-}; shift 4 2>/dev/null || shift $#
R=${R:-${FV_SCRATCH:-/scratch}/mathlib-as-project}; FV=${FV:-$LIGHT_LEAN/fastverify/bin/fastverify}
WS=${WS:-$LIGHT_LEAN/verify/challenge}
TAG=$CASE.$PRESET$SUF; OUT=$R/runs/$TAG
mkdir -p $R/runs; rm -rf "$OUT"
CH=$R/chal/$CASE; [ -n "${CHAL:-}" ] && CH=$CHAL
t0=$(date +%s.%N)
echo "$(date -u +%FT%TZ) $(hostname) start $TAG pin=${PIN:-pool} fv=$FV ws=$WS $*" >> $R/runs/progress.log
${PIN:+taskset -c $PIN} env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV" "$R/proj/$CASE" "$CH" "$OUT" \
    --preset "$PRESET" --threads "$THREADS" --packages "$WS" "$@" > "$R/runs/$TAG.log" 2>&1
rc=$?
t1=$(date +%s.%N); wall=$(python3 -c "print(round($t1-$t0,1))")
echo "$(date -u +%FT%TZ) $(hostname) done $TAG rc=$rc wall=${wall}s" >> $R/runs/progress.log
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$TAG" "$CASE" "$PRESET" "$rc" "$wall" "$(hostname)" "$*" >> $R/runs/summary.tsv

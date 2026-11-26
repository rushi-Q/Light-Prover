#!/bin/bash
# kill_one_lean.sh OUTDIR TAG CPUS THREADS PROJECT CHALLENGE DELAY [fastverify args...]
#   an OOM-kill SIMULATION for the official build path: run bin/fastverify (default: --preset sound --build B0) and, DELAY
#   seconds after the first `lean` of the build appears, SIGKILL exactly one running `lean` of THIS run (what the kernel
#   OOM killer does to a lean process when the cgroup limit is hit). Records the verdict and how the build classified it.
set -u
OUT=$1; TAG=$2; CPUS=$3; T=$4; PROJ=$5; CHAL=$6; DELAY=$7; shift 7
FV=${FV:-$LIGHT_LEAN/fastverify}; WS=${WS:-$LIGHT_LEAN/verify/challenge}
mkdir -p "$OUT"; rm -rf "$OUT/$TAG"
EXTRA=(); [ -f "$CHAL/challenge.export.sha256" ] && EXTRA=(--challenge-sha256 "$(cut -d' ' -f1 "$CHAL/challenge.export.sha256")")
( env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 taskset -c "$CPUS" "$FV/bin/fastverify" "$PROJ" "$CHAL" "$OUT/$TAG" --threads "$T" --packages "$WS" "${EXTRA[@]}" "$@" > "$OUT/$TAG.fv.log" 2>&1; echo "rc=$?" >> "$OUT/$TAG.fv.log" ) &
FVPID=$!
# wait for the first lean of this run (its argv mentions OUT/TAG), then DELAY s, then kill one
for i in $(seq 1 600); do
  pids=$(pgrep -f "lean .*$OUT/$TAG/work/proj" 2>/dev/null | head -5)
  [ -n "$pids" ] && break; sleep 1
done
sleep "$DELAY"
victim=$(pgrep -f "lean .*$OUT/$TAG/work/proj" | head -1)
if [ -n "$victim" ]; then
  echo "$(date -u +%FT%TZ) killing lean pid $victim: $(tr '\0' ' ' < /proc/$victim/cmdline | cut -c1-200)" | tee "$OUT/$TAG.kill.log"
  kill -9 "$victim"
else
  echo "no lean found to kill" | tee "$OUT/$TAG.kill.log"
fi
wait $FVPID
grep -E "fastverify: (WARNING|build|export|check|verdict)|^rc=" "$OUT/$TAG.fv.log" | cut -c1-220
python3 -c "import json; r=json.load(open('$OUT/$TAG/result.json')); print(r['verdict'], '|', r['verdict_basis'][:200]); print([(a['option'], a['exit'], (a.get('stage') or {}).get('detail','')[:160]) for a in r['build']['attempts']])" 2>/dev/null

#!/bin/bash
# incr_train.sh -- stage-3 integrator: verify a train INCREMENTALLY on the previous train's kept build tree
# (tools/incr: rebuild of the touched cone, then the WHOLE closure is exported and judged by the full trusted check, so
# the verdict is as complete as a cold run's). Runs on the node of the base train.
# cwd = ship dir (fv/ = package snapshot, c1/t2.tar.gz = the new composite tree). env: BASE = run root of the base train
# (verify_tree.sh's run-<tag>-<stamp> with run/ kept by KEEP_WORK=1), TAG, THREADS, WORKROOT (default $FV_SCRATCH),
# RH_CHALLENGE (default $LIGHT_LEAN/verify/challenge).
set -u
S=$(pwd); TAG=${TAG:-incr}; B=${BASE:?BASE=run root of the base train}; R=${WORKROOT:-${FV_SCRATCH:?node-local scratch directory for the run (required; or set WORKROOT)}}/run-$TAG-$(date -u +%m%dT%H%M)
WS=${RH_CHALLENGE:-$LIGHT_LEAN/verify/challenge}
mkdir -p $R/t2 && tar xzf $S/c1/t2.tar.gz -C $R/t2 || exit 2
echo "== $TAG $(date -u +%FT%TZ) host=$(hostname) threads=${THREADS:-200} mode=incr base=$B R=$R"; sha256sum $S/c1/t2.tar.gz
echo "TREE files=$(find $R/t2/src -name '*.lean' | wc -l) lines=$(find $R/t2/src -name '*.lean' -print0 | xargs -0 cat | wc -l)"
tr -s " " "\n" < $WS/export-targets.txt | sed "/^$/d" > $B/run/log/export-targets.txt   # one name per line
t0=$(date +%s)
env -i HOME=$HOME PATH=/usr/bin:/bin LANG=C.UTF-8 FASTVERIFY=$S/fv bash $S/fv/tools/incr/incr-reverify.sh $B/run $R/t2 $WS $R/incr \
  --challenge-sha256 3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d --threads ${THREADS:-200} --export-dir /dev/shm --keep-export --hardlink > $R/incr.log 2>&1
rc=$?; echo "incr-reverify rc=$rc wall=$(( $(date +%s) - t0 )) s"; tail -5 $R/incr.log
python3 -I - $R/incr/summary.json <<'PY'
import json, sys
try: r = json.load(open(sys.argv[1]))
except Exception as e: print('RESULT no summary', e); sys.exit(0)
print('RESULT verdict=%s exit=%s total_s=%s' % (r.get('verdict'), r.get('exit'), r.get('total_s')))
for a in r.get('attempts', []):
    print('RESULT attempt=%s outcome=%s build_s=%s export_s=%s check_s=%s modules=%s dirty=%s export_bytes=%s check=%s' % (a.get('attempt'), a.get('outcome'),
          a.get('build_s'), a.get('export_s'), a.get('check_s'), a.get('modules'), a.get('dirty'), a.get('export_bytes'), (a.get('check') or {}).get('verdict')))
PY
E=$(ls $R/incr/*/solution.export 2>/dev/null | tail -1); [ -n "$E" ] && sha256sum $(readlink -f $E) | tee $R/export.sha256
echo "== done $(date -u +%FT%TZ)"

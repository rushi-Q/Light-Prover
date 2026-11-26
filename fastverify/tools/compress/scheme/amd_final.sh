#!/bin/bash
# amd_final.sh -- final timing run (cwd = ship dir: fv/, cand/t2.tar.gz, bin/expdiff, tools/):
# --preset sound (the measured configuration incl. merge) on the UNMODIFIED RH sources and on the compressed candidate,
# same package, same node, back to back; RESULT lines; expdiff evidence of the candidate export vs the honest export.
# env: FV_SCRATCH (node-local scratch root, required), RH_PROJECT (default $LIGHT_LEAN/alpoge-rh/lean),
#      RH_CHALLENGE (default $LIGHT_LEAN/verify/challenge), RH_REF (honest RH export, required), AMD_THREADS, PRESET, RUNS.
set -u
S=$(pwd); W=${FV_SCRATCH:?node-local scratch directory for the runs (required)}/final-$(date -u +%m%dT%H%M); mkdir -p $W
T=${AMD_THREADS:-$(nproc)}
WS=${RH_CHALLENGE:-$LIGHT_LEAN/verify/challenge}; RH=${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}
REF=${RH_REF:?honest RH export (reference for the runs and expdiff) (required)}
CSHA=3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d
echo "== final $(date -u +%FT%TZ) host=$(hostname) threads=$T preset=${PRESET:-sound} runs=${RUNS:-orig cand}"; df -h "$W" /dev/shm | tail -2
mkdir -p $W/cand; tar xzf $S/cand/t2.tar.gz -C $W/cand; sha256sum $S/cand/t2.tar.gz
echo "candidate files=$(find $W/cand/src -name '*.lean' | wc -l)"
summ() { python3 -I - "$1" <<'PY'
import json, sys
r = json.load(open(sys.argv[1])); e = r.get("export") or {}
cs = (r.get("checks") or {}).get("sound") or {}
print("RESULT verdict=%s basis=%s" % (r.get("verdict"), r.get("verdict_basis")))
print("RESULT export sha256=%s size=%s identical_to_reference=%s" % (e.get("sha256"), e.get("size"), (e.get("reference") or {}).get("identical")))
print("RESULT stage_seconds=%s" % json.dumps(r.get("stage_seconds")))
print("RESULT check=%s %s s legs=%s" % (cs.get("verdict"), cs.get("seconds"), json.dumps((cs.get("stage") or {}).get("leg_ms"))))
PY
}
for run in ${RUNS:-orig cand}; do
  P=$RH; [ $run = cand ] && P=$W/cand
  o=$W/out-$run; t0=$(date +%s.%N)
  KE=(); [ $run = cand ] && KE=(--keep-work)
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$S/fv/bin/fastverify" "$P" "$WS" "$o" --preset ${PRESET:-sound} --threads "$T" \
    --no-build-fallback "${KE[@]}" --challenge-sha256 $CSHA --comparator-sha256 "$(sha256sum "$WS/comparator.json" | cut -d' ' -f1)" --reference-export $REF > "$o.log" 2>&1
  echo "== $run: fastverify rc=$? wall=$(echo "$(date +%s.%N) - $t0" | bc) s"; summ $o/result.json
  grep -E "build-fast|modules|merge" $o.log | tail -3 | cut -c1-300
done
EXP=$(readlink -f $W/out-cand/solution.export 2>/dev/null)
if [ -f "$EXP" ]; then
  EXPDIFF=$S/bin/expdiff AMD_THREADS=$T bash $S/tools/amd-evidence.sh "$EXP" $W/evidence $REF $WS/export-targets.txt 2>&1 | tail -40
fi
mkdir -p $W/keep; for run in orig cand; do cp $W/out-$run/result.json $W/keep/result-$run.json 2>/dev/null; cp $W/out-$run.log $W/keep/ 2>/dev/null; done
cp -r $W/evidence $W/keep/ 2>/dev/null
[ -n "$EXP" ] && case "$EXP" in /dev/shm/*) rm -rf "$(dirname "$EXP")";; esac
rm -rf $W/out-orig/work $W/out-cand/work $W/cand $W/out-*/solution.export
echo "kept $W/keep"; echo "== done $(date -u +%FT%TZ)"

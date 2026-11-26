#!/bin/bash
# amdjob-p06-incr.sh EDITS_DIR [MODE]  — whole-node batch job (cwd = the shipped package incl. EDITS_DIR): sound
# re-verification of RH with the autoshorten edits (proof suffixes of theorem/lemma commands replaced by automated closers,
# each module re-elaborated and verified by apply.py beforehand). Base = a COPY of the B1 build tree of the honest RH run
# RH_BASE_OUT (official lean, 175,187 modules, read-only reuse) + its plan; NEW = pristine RH sources with the
# edited modules of EDITS_DIR overlaid; tools/incr/incr-reverify.sh (untrusted incremental build, E1, the TRUSTED
# check-sound.sh against the pinned official challenge export). MODE: optimistic (default: edited modules only, retry
# with the importer cone if not ACCEPTED) | full (importer cone at once).
# Adapted from tools/incr/amdjob-rh-incr.sh. Everything under W is deleted at the end except K.
# env: FV_SCRATCH (node-local scratch root, required), RH_BASE_OUT (OUT directory of an honest RH run of bin/fastverify
#      with --keep-work; required), RH_PROJECT (default $LIGHT_LEAN/alpoge-rh/lean), RH_CHALLENGE (default
#      $LIGHT_LEAN/verify/challenge).
set -u
export FASTVERIFY=$(pwd)
ED=$(readlink -f "$1"); MODE=${2:-optimistic}
FS=${FV_SCRATCH:?node-local scratch directory for the work tree (required)}
W=$FS/rhincr; K=$FS/keep-$(date -u +%H%M)
CH=${RH_CHALLENGE:-$LIGHT_LEAN/verify/challenge}
RH=${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}
CSHA=3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d
B=${RH_BASE_OUT:?OUT directory of an honest RH run with --keep-work (required)}
LEAN=/scratch/fastverify-next/tc/lean4-d5e35ef223-pgo/bin/lean
cleanup() { rm -rf "$W"; for x in /dev/shm/incr-export.*; do [ -O "$x" ] && rm -rf "$x"; done; }
trap 'cleanup; exit 2' TERM INT HUP
date -u; nproc; free -g | head -2; df -h "$FS" /dev/shm | tail -2; uptime
rm -rf "$W"; mkdir -p "$W/base/work" "$W/base/log/build-fast" "$K"
t0=$(date +%s.%N)
cp "$B/log/build-fast/plan.jsonl" "$W/base/log/build-fast/" && cp "$B/log/export-targets.txt" "$W/base/log/" \
  && cp "$B/result.json" "$W/base/" && cp -a "$B/log/build-fast/planner" "$W/base/log/build-fast/" || exit 2
cp -a "$B/work/proj" "$W/base/work/proj" || exit 2
t1=$(date +%s.%N); echo "BASE copy of the B1 tree: $(echo "$t1 - $t0" | bc) s, $(du -sh "$W/base/work/proj" | cut -f1)"
cp -a "$RH" "$W/new" || exit 2
n=0; for f in $(cd "$ED" && find . -name '.wd' -prune -o -name '*.lean' -print); do
  [ -f "$W/new/src/$f" ] || { echo "edited module $f not in RH sources"; exit 2; }
  cp "$ED/$f" "$W/new/src/$f"; n=$((n+1)); done
t2=$(date +%s.%N); echo "source copy + $n edited modules: $(echo "$t2 - $t1" | bc) s"
A=(--optimistic --reuse-plan); [ "$MODE" = full ] && A=(--reuse-plan)
echo "=== incr-reverify ($(date -u +%H:%M:%S)): ${A[*]}"
bash tools/incr/incr-reverify.sh "$W/base" "$W/new" "$CH" "$W/out" --challenge-sha256 "$CSHA" --threads "$(nproc)" \
  --packages "$CH" --lean "$LEAN" --export-dir /dev/shm --hardlink "${A[@]}" | tail -3
rc=${PIPESTATUS[0]}
cp "$W/out/summary.json" "$K/" 2>/dev/null
for a in "$W/out"/a*; do m=$(basename "$a"); mkdir -p "$K/$m"
  cp "$a"/*.json "$a"/*.out "$a"/times "$a"/check.log "$K/$m/" 2>/dev/null; cp "$a/work/log/sched.out" "$K/$m/" 2>/dev/null; done
cat "$K/summary.json" 2>/dev/null; echo
cleanup; date -u; echo "kept: $K  rc=$rc"

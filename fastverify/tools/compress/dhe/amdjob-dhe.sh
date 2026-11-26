#!/bin/bash
# amdjob-dhe.sh — whole-node batch job (cwd = shipped dir: fastverify/ package copy, dhe/, expdiff, EDITS): dead-have
# elimination (DHE) applied to the WHOLE RH proof and verified end to end:
#  A. module check: every edited module (edits of EDITS) is elaborated in bwrap (PGO lean of the sound preset,
#     skip-kernel-tc, linters off, its exact setup from the B1 plan) against the read-only honest B1 tree
#     RH_BASE_OUT and its new .olean is compared with the B1 .olean by DeadLetCheck (equal / alpha-equal /
#     equal modulo dead lets; anything else = different). Modules that fail or differ keep their original source.
#  B. the passing edits form the DHE tree; tools/incr/incr-reverify.sh --optimistic-only rebuilds those modules on a
#     COPY of the B1 tree (reflink/full copy: the base stays untouched), exports (E1) and runs the TRUSTED sound check
#     against the pinned official challenge.
#  C. expdiff diff: original export vs DHE export over the targets' closure (statuses, explain, RESULT line).
# Keeps summaries in K; deletes the work dirs and the /dev/shm export at the end.
# env: FV_SCRATCH (node-local scratch root, required), RH_BASE_OUT (OUT directory of an honest RH run of
#      bin/fastverify with --keep-work: log/, work/proj, solution.export; required), RH_PROJECT (pristine RH sources,
#      default $LIGHT_LEAN/alpoge-rh/lean), RH_CHALLENGE (default $LIGHT_LEAN/verify/challenge), EDITS, AMD_THREADS.
set -u
SHIP=$(pwd); export FASTVERIFY=$SHIP/fastverify
EDITS=${EDITS:-$SHIP/edits.tsv}
FS=${FV_SCRATCH:?node-local scratch directory for the work tree (required)}
W=$FS/dhe; K=$FS/dhe-keep-$(date -u +%H%M)
B=${RH_BASE_OUT:?OUT directory of an honest RH run with --keep-work (required)}
RH=${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}
CH=${RH_CHALLENGE:-$LIGHT_LEAN/verify/challenge}
CSHA=3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d
LEAN=/scratch/fastverify-next/tc/lean4-d5e35ef223-pgo/bin/lean
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
T=${AMD_THREADS:-$(nproc)}
cleanup() { rm -rf "$W"; for x in /dev/shm/incr-export.*; do [ -O "$x" ] && rm -rf "$x"; done; }
trap 'cleanup; exit 2' TERM INT HUP
date -u; echo "threads $T"; free -g | head -2; df -h "$FS" /dev/shm | tail -2
rm -rf "$W"; mkdir -p "$W" "$K"
cp "$EDITS" "$K/edits.tsv"
t0=$(date +%s)
# ---- A. module check
python3 -I "$SHIP/dhe/amd_phaseA.py" --edits "$EDITS" --src "$RH/src" \
  --plan "$B/log/build-fast/plan.jsonl" --lean-path "$(cat $B/log/build-fast/lean_path.txt)" --base-proj "$B/work/proj" \
  --lean "$LEAN" --tc "$TC" --dlc "$SHIP/dhe/DeadLetCheck.lean" --work "$W/A" --threads "$T" --out "$K/phaseA" \
  > "$K/phaseA.log" 2>&1
echo "phase A rc=$? $(( $(date +%s) - t0 )) s"; tail -5 "$K/phaseA.log"
[ -s "$K/phaseA/pass_edits.tsv" ] || { echo "no passing edits"; cleanup; exit 2; }
# ---- B. DHE tree + incremental sound re-verification
t1=$(date +%s)
cp -a "$RH" "$W/src-dhe" || { cleanup; exit 2; }
python3 -I "$SHIP/dhe/apply_inplace.py" "$W/src-dhe/src" "$K/phaseA/pass_edits.tsv" > "$K/apply.json" || { cleanup; exit 2; }
cat "$K/apply.json"
echo "tree ready $(( $(date +%s) - t1 )) s"
bash "$FASTVERIFY/tools/incr/incr-reverify.sh" "$B" "$W/src-dhe" "$CH" "$W/o" --challenge-sha256 "$CSHA" --threads "$T" \
  --packages "$CH" --lean "$LEAN" --export-dir /dev/shm --keep-export --optimistic-only --reuse-plan > "$K/incr.out" 2>&1
irc=$?; echo "phase B (incr-reverify) rc=$irc $(( $(date +%s) - t1 )) s"; tail -1 "$K/incr.out"
cp "$W/o/summary.json" "$K/" 2>/dev/null
for a in "$W/o"/a*; do n=$(basename "$a"); mkdir -p "$K/$n"
  cp "$a"/*.json "$a"/*.out "$a"/times "$a"/check.log "$K/$n/" 2>/dev/null; cp "$a/work/log/sched.out" "$K/$n/" 2>/dev/null; done
NEWX=$(readlink -f "$W/o/a1-optimistic/solution.export" 2>/dev/null)
# ---- C. export-level diff
if [ -n "$NEWX" ] && [ -f "$NEWX" ]; then
  sha256sum "$NEWX" > "$K/dhe-export.sha256"; ls -la "$NEWX" >> "$K/dhe-export.sha256"
  t2=$(date +%s)
  /usr/bin/time -v "$SHIP/expdiff" diff -j "$T" --targets "$B/log/export-targets.txt" --explain 10 --dead-lets --tsv "$K/expdiff.tsv" \
    "$B/solution.export" "$NEWX" > "$K/expdiff.out" 2> "$K/expdiff.err"
  echo "phase C (expdiff) rc=$? $(( $(date +%s) - t2 )) s"; grep -E "^(status|RESULT|statement_changed_count|old\.|new\.)" "$K/expdiff.out"
  gzip -f "$K/expdiff.tsv"
fi
cleanup; date -u; echo "kept: $K"; echo "total $(( $(date +%s) - t0 )) s"

#!/bin/bash
# tools/incr/amdjob-rh-incr.sh [SCENARIOS...]  — whole-node job, run from the package root (cwd = the package): RH
# re-verification after small proof edits. Base = a COPY (not hard links: the source tree is read-only reuse) of the B1
# build tree of an honest RH run RH_BASE_OUT (official lean, all 175,187 modules) + its plan; edits = one `have` line
# inserted into one proof (tools/incr/mk-edit.py); each scenario = tools/incr/incr-reverify.sh (untrusted incremental
# build with the PGO lean + skip-kernel-tc + linter-off, E1 on /dev/shm, the trusted check-sound.sh).
# Scenarios (default order R1o R3o R1w R2o R1s R1f): R1-R3 = one `have` line in a theorem with 106 / 3,161 / 88,428
# importers, R1s = a `sorry` in the R1 theorem; mode o = optimistic (edited module only) + cold check, w = optimistic +
# warm server, s = optimistic-only (no retry), f = full rebuild of the importers + cold check. A scenario is skipped when
# the job's time budget (BUDGET_MIN, default 95) would be exceeded. Everything is deleted at the end except K (summaries,
# build/check logs).
# Environment: FV_SCRATCH (required) = node-local work root (W and K below); RH_BASE_OUT (required) = OUT of the base RH
# run (`bin/fastverify ... --keep-work`, B1 tree + plan); RH_CHALLENGE (default <repository root>/verify/challenge) = the RH
# challenge workspace; RH_PROJECT (default <repository root>/alpoge-rh/lean) = the RH project sources.
set -u
export FASTVERIFY=$(pwd)
S=${FV_SCRATCH:?node-local work root (required)}
W=$S/rhincr; K=$S/rhincr-keep-$(date -u +%H%M)
CH=${RH_CHALLENGE:-$(dirname "$FASTVERIFY")/verify/challenge}; [ -d "$CH" ] || { echo "no RH challenge workspace at $CH: set RH_CHALLENGE" >&2; exit 2; }
RHP=${RH_PROJECT:-$(dirname "$FASTVERIFY")/alpoge-rh/lean}; [ -d "$RHP" ] || { echo "no RH project at $RHP: set RH_PROJECT" >&2; exit 2; }
CSHA=3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d
B=${RH_BASE_OUT:?OUT directory of the base RH run with --keep-work (required)}
LEAN=/scratch/fastverify-next/tc/lean4-d5e35ef223-pgo/bin/lean
SC=("$@"); [ ${#SC[@]} = 0 ] && SC=(R1o R3o R1w R2o R1s R1f)
BUDGET=$(( ${BUDGET_MIN:-95} * 60 )); TJ0=$(date +%s)
cleanup() { rm -rf "$W"; for x in /dev/shm/incr-export.*; do [ -O "$x" ] && rm -rf "$x"; done; }
trap 'cleanup; exit 2' TERM INT HUP
date -u; nproc; free -g | head -2; df -h "$S" /dev/shm | tail -2; uptime
rm -rf "$W"; mkdir -p "$W/base/work" "$W/base/log/build-fast" "$K"
t0=$(date +%s.%N)
cp "$B/log/build-fast/plan.jsonl" "$W/base/log/build-fast/" && cp "$B/log/export-targets.txt" "$W/base/log/" \
  && cp "$B/result.json" "$W/base/" && cp -a "$B/log/build-fast/planner" "$W/base/log/build-fast/" || exit 2
cp -a "$B/work/proj" "$W/base/work/proj" || exit 2
t1=$(date +%s.%N); echo "BASE copy of the B1 tree: $(echo "$t1 - $t0" | bc) s, $(du -sh "$W/base/work/proj" | cut -f1)"
cp -a "$RHP" "$W/src0" || exit 2
t2=$(date +%s.%N); echo "source copy: $(echo "$t2 - $t1" | bc) s"
mk() { python3 -I tools/incr/mk-edit.py "$W/src0" "$W/e-$1" "$2" have "$3" || exit 2; }
mk R1 Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecay rapid_decrease      # 106 importers
mk R2 GroundTheory.AutomorphicForms.HermitianSpaces isUnit_det_of_unitary                              # 3,161 importers
mk R3 ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt chart_le_pull     # 88,428 importers
python3 -I tools/incr/mk-edit.py "$W/src0" "$W/e-R1s" Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecay sorry rapid_decrease || exit 2
declare -A EST=([o]=600 [w]=1000 [s]=400 [f]=1500)
for s in "${SC[@]}"; do
  e=${s:0:2}; m=${s:2:1}; A=(--optimistic --reuse-plan)
  [ "$m" = f ] && A=(--reuse-plan)
  [ "$m" = w ] && A+=(--warm "$B/solution.export")
  [ "$m" = s ] && { e=R1s; A=(--optimistic-only --reuse-plan); }
  if [ $(( $(date +%s) - TJ0 + ${EST[$m]:-900} )) -gt $BUDGET ]; then echo "=== scenario $s SKIPPED (time budget)"; continue; fi
  echo "=== scenario $s ($(date -u +%H:%M:%S)): ${A[*]}"
  bash tools/incr/incr-reverify.sh "$W/base" "$W/e-$e" "$CH" "$W/o-$s" --challenge-sha256 "$CSHA" --threads "$(nproc)" \
    --packages "$CH" --lean "$LEAN" --export-dir /dev/shm --hardlink "${A[@]}" | tail -1   # our own edits: hard links, as measured
  mkdir -p "$K/$s"; cp "$W/o-$s/summary.json" "$K/$s/" 2>/dev/null
  for a in "$W/o-$s"/a*; do n=$(basename "$a"); mkdir -p "$K/$s/$n"
    cp "$a"/*.json "$a"/*.out "$a"/times "$a"/check.log "$K/$s/$n/" 2>/dev/null; cp "$a/work/log/sched.out" "$K/$s/$n/" 2>/dev/null; done
  [ -f "$W/o-$s/incr/server.log" ] && cp "$W/o-$s/incr/server.log" "$K/$s/"
  rm -rf "$W/o-$s"
  free -g | sed -n 2p
done
cleanup; ls /dev/shm | grep -c incr-export; date -u; echo "kept: $K"

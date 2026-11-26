#!/bin/bash
# repro for 062: the fast pipeline's retry policy vs the official single lake build.
# OFFICIAL flow = officialflow.sh (lake build 4.33.1 + official lean4export + lake comparator 4.36);
# FAST flow = fastflow.sh = fastverify/pipeline/pipeline.sh + native lean4export + pchk run.sh with the challenge
# (harness scripts copied from tests 023/020). Any x86-64 host (LEAN_TC unset = the pipeline's documented mode with
# the official lean: RETRY_PRISTINE is active because LEAN_EXTRA is non-empty); where it exists also with FAST_TC=7586 (the
# native build of the fast toolchain sources: RETRY_PRISTINE + RETRY_OFFICIAL). ~2 min.
# Usage: bash repro.sh [WORKDIR]      (optional: COIN_N=16 bash repro.sh  -> also the flaky-module statistics, ~15 min)
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-062}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
run() { # $1 project, $2 case tag (no spaces), [FAST_TC in env]
  cp -a "$D/$1" "$W/$1" 2>/dev/null
  echo "##### $2"
  bash "$D/officialflow.sh" "$W/$1" "$W/off-$2" "$W/challenge" > "$W/off-$2.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$1" "$W/fast-$2" "$CE" > "$W/fast-$2.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error: src|official: lean4export' "$W/off-$2.log" | head -4 | sed 's/^/  /'
  grep -E 'RETRY|retry|SUMMARY|^FAST|fast: export [0-9]' "$W/fast-$2.log" | cut -c1-200 | sed 's/^/  /'
  echo "=== SUMMARY $2 official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"; }
unset LEAN_TC FAST_TC
run proj-second proj-second-offlean
if [ -x /scratch/fast-tc/7586/bin/lean ]; then FAST_TC=/scratch/fast-tc/7586 run proj-second proj-second-tc7586; fi
if [ -n "${COIN_N:-}" ]; then
  echo "##### proj-coin: $COIN_N independent runs of each flow (module fails iff monoNanosNow is even)"
  oa=0; fa=0
  for i in $(seq 1 $COIN_N); do
    bash "$D/officialflow.sh" "$D/proj-coin" "$W/oc" "$W/challenge" > "$W/oc.log" 2>&1 && oa=$((oa+1))
    bash "$D/fastflow.sh" "$D/proj-coin" "$W/fc" "$CE" > "$W/fc.log" 2>&1 && fa=$((fa+1))
    echo "  run $i: official $(grep -c '^OFFICIAL: ACCEPTED' $W/oc.log) fast $(grep -c '^FAST: ACCEPTED' $W/fc.log) (1 = accepted; fast retries: $(grep -c RETRY $W/fc.log))"
  done
  echo "  => official accepted $oa/$COIN_N, fast accepted $fa/$COIN_N"
fi
rm -rf "$W"

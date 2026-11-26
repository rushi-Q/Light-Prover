#!/bin/bash
# repro for 067: fastverify/pipeline/pipeline.sh does not clear its WORK directory, and sched_r.py APPENDS to
# WORK/log/sched.log, from which pipeline.sh takes the build verdict (grep '^EXIT 0'). Re-running into the WORK directory of an
# earlier run therefore (a) resolves imports against the earlier run's .olean files and (b) can pass a FAILED build.
#   v1: src/Helper.lean + src/Main.lean (import Helper)                         -> run into WORK first (official: accepted)
#   v2: Helper.lean deleted, Main unchanged          (case a)  official REJECTS (bad import 'Helper'); fast (same WORK) ACCEPTS
#   v3: v1 + a type error in riemannHypothesis       (case b)  official REJECTS; fast (same WORK): build fails (EXIT 1) but the
#       stale 'EXIT 0' of the earlier runs is still in sched.log -> export of the STALE Main.olean -> pchk ACCEPTS
# Deployed pipeline (copy with the documented speed knobs native.txt=off, pkgmode.txt=symlink), LEAN_TC unset, native exporter,
# pchk run.sh with the challenge. Any x86-64 host, ~1 min. Usage: bash repro.sh [WORKDIR]   (FAST_PIPELINE_DIR=<fixed pipeline>)
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-067}; R=$LIGHT_LEAN
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
P=${FAST_PIPELINE_DIR:-}; if [ -z "$P" ]; then P=$W/pipeline; cp -a $R/fastverify/pipeline "$P"; echo off > "$P/native.txt"; echo symlink > "$P/pkgmode.txt"; fi
unset LEAN_TC FAST_TC; export LEAN4EXPORT_BIN=/scratch/fastverify/exporter/lean4export EVAL_THREADS=${EVAL_THREADS:-16}
S=/scratch/fastverify/checkers/pchk
$S/.lake/build/bin/pleanchecker-k --help > /dev/null 2>&1 || export CCMP_LEANCHECKER=${PCHK_K_REBUILD:-$S/.lake/build/bin/pleanchecker}
for v in v1 v2 v3; do cp -a "$D/$v" "$W/$v"; done
mkdir -p "$W/work/log"
fast() { # $1 version -> pipeline.sh into the shared WORK, then pchk; sets FRC
  : > "$W/work/log/native.log"   # (pipeline.sh's native.txt=off knob needs this file, see fastflow.sh)
  bash "$P/pipeline.sh" "$W/$1" "$W/work" > "$W/p-$1.log" 2>&1; prc=$?
  echo "  fast: pipeline.sh $1 -> shared WORK: rc=$prc; last sched.log lines: $(tail -2 $W/work/log/sched.log | tr '\n' ' ' | cut -c1-100)"
  if [ $prc -eq 0 ] && [ -s "$W/work/solution.export" ]; then
    sh $S/run.sh $S "$W/work/solution.export" 16 "$CE" > "$W/check-$1.log" 2>&1; FRC=$?
    echo "  fast: check: $(tail -2 $W/check-$1.log | head -1)"
  else FRC=1; fi
  echo "  FAST: $([ $FRC -eq 0 ] && echo ACCEPTED || echo REJECTED) (rc=$FRC)"; }
echo "##### setup (v1 into a fresh WORK)"; fast v1
for c in v2:case-a v3:case-b; do v=${c%%:*}; n=${c#*:}
  echo "##### $n-$v-in-reused-work"
  bash "$D/officialflow.sh" "$W/$v" "$W/off-$v" "$W/challenge" > "$W/off-$v.log" 2>&1; orc=$?
  grep -E '^OFFICIAL|bad import|error: src' "$W/off-$v.log" | head -3 | sed 's/^/  /'
  fast $v
  echo "=== SUMMARY $n-$v official_rc=$orc fast_rc=$FRC (0 = ACCEPTED)"
done
echo "##### control: v2 and v3 into FRESH work dirs (must fail like the official flow)"
for v in v2 v3; do mkdir -p "$W/fresh-$v/log"; : > "$W/fresh-$v/log/native.log"
  bash "$P/pipeline.sh" "$W/$v" "$W/fresh-$v" > "$W/pf-$v.log" 2>&1; echo "  pipeline.sh $v -> fresh WORK: rc=$?"; done
rm -rf "$W"

#!/bin/bash
# mk_mathlib_corpus.sh OUTROOT [CASE...] : the Mathlib-differential export corpus for the check-level suite. Every case of
# the Mathlib-differential case set MATHLIB_DIFF through the package (preset fast-exact: B2 + E1 + C1; the
# challenge is built officially, B0+E0); OUTROOT/runs/CASE = the run, OUTROOT/corpus/CASE/{solution,challenge}.export +
# comparator.json = the suite input (gates.py inputs key "mathlib" = OUTROOT/corpus).
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
R=${1:?outroot}; shift
V=${MATHLIB_DIFF:-${BENCH_INPUTS:-/scratch/bench-inputs}/mathlib-differential}
WS=${FV_PACKAGES:-$FV/../verify/challenge}
[ $# -gt 0 ] || set -- $(python3 -I -c 'import json,sys; print(" ".join(sorted(json.load(open(sys.argv[1])))))' "$V/cases.json")
mkdir -p "$R/runs" "$R/corpus"
for CASE in "$@"; do
  CH=${CASE%%-*}; OUT=$R/runs/$CASE; rm -rf "$OUT"
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$V/projects/$CASE" "$V/challenges/$CH" "$OUT" \
     --preset fast-exact --threads "${THREADS:-48}" --packages "$WS" > "$R/runs/$CASE.log" 2>&1
  echo "$(date -u +%FT%TZ) $CASE rc=$?" >> "$R/runs/progress.log"
  mkdir -p "$R/corpus/$CASE"
  [ -f "$OUT/solution.export" ] && ln -f "$OUT/solution.export" "$R/corpus/$CASE/solution.export"
  [ -f "$OUT/challenge.export" ] && ln -f "$OUT/challenge.export" "$R/corpus/$CASE/challenge.export"
  cp "$V/challenges/$CH/comparator.json" "$R/corpus/$CASE/comparator.json"
done

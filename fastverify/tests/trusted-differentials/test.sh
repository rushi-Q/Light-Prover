#!/bin/bash
# tests/trusted-differentials/test.sh [WORK] [--base DIR] [--per-op N] [--warm-n N]
#   Randomized differentials of the NEW trusted checks against the unchanged check/sound/check-sound.sh:
#   (1) lmdiff.py: check/lowmem/check-sound-lowmem.sh, check-sound-ultralowmem.sh (when installed) and
#       check/notary/check-notary.sh as systems under test (more: FV_EXTRA_SUTS="script ..."),
#       the 52 structure-aware export-fuzz operators (tests/export-fuzz/xfuzz.py) x N per operator on one base;
#       FAIL iff a SUT ACCEPTS what check-sound.sh does not, or check-sound.sh ACCEPTS what the SUT does not;
#   (2) warmdiff.py: the warm delta check (fvcheckd, check/warm/ when published; else the path in $FV_WARM_DIR)
#       on N random deltas, each judged forward, reversed and by 16 concurrent clients, against check-sound.sh on the
#       independently materialized effective export; FAIL iff warm ACCEPTS what the cold check does not or a verdict
#       depends on query order / concurrency. Skipped (SKIP row) when no warm binaries are found.
#   BASE = an export-fuzz base dir (out/solution.export, out/challenge.export, challenge/comparator.json); default:
#   $EXPORT_FUZZ_WORK/bases/ind (build: tests/export-fuzz/bases/mk.sh). ~5-10 min on 32 cores with the defaults (per-op 1, warm-n 60).
# finding: none (differential evidence for the warm, notary and low-memory trusted checks)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=$(cd "$H/../.." && pwd)
W=${1:-${SCRATCH:-${TMPDIR:-/tmp}}/$USER-trusted-differentials}; case "$W" in --*) W=${SCRATCH:-${TMPDIR:-/tmp}}/$USER-trusted-differentials;; *) shift 2>/dev/null;; esac
BASE=; PEROP=1; WN=60
while [ $# -gt 0 ]; do case "$1" in --base) BASE=$2; shift 2;; --per-op) PEROP=$2; shift 2;; --warm-n) WN=$2; shift 2;; *) shift;; esac; done
if [ -z "$BASE" ]; then for c in ${EXPORT_FUZZ_WORK:-/nonexistent}/bases/ind; do [ -f "$c/out/solution.export" ] && { BASE=$c; break; }; done; fi
[ -n "$BASE" ] && [ -f "$BASE/out/solution.export" ] || { echo "SKIP no export-fuzz base found (build tests/export-fuzz/bases/mk.sh or pass --base)"; echo "RESULT SKIP"; exit 0; }
rm -rf "$W"; mkdir -p "$W"
bad=0
for sut in "$PKG/check/lowmem/check-sound-lowmem.sh" "$PKG/check/lowmem/check-sound-ultralowmem.sh" \
           "$PKG/check/notary/check-notary.sh" ${FV_EXTRA_SUTS:-}; do
  n=$(basename "$sut" .sh)
  if [ ! -x "$sut" ]; then echo "SKIP $n: not installed"; continue; fi
  out=$(/usr/bin/python3 -I "$H/lmdiff.py" "$BASE" "$W/$n" --per-op "$PEROP" --seed 1 --jobs 8 --threads 4 --sut "$sut" 2>&1)
  res=$(printf '%s\n' "$out" | grep '^RESULT')
  printf '%s\n' "$out" | grep -E '^(CRITICAL|AVAIL)' | head -5
  if [ -z "$res" ]; then echo "FAIL $n: no RESULT line: $(printf '%s' "$out" | tail -c 300 | tr '\n' ' ')"; bad=1
  elif printf '%s\n' "$out" | grep -qE '^(CRITICAL|AVAIL)'; then echo "FAIL $n: $res"; bad=1; else echo "PASS $n: $res"; fi
done
WD=${FV_WARM_DIR:-}
if [ -z "$WD" ] && [ -f "$PKG/check/warm/fvcheckd.py" ]; then WD=$PKG/check/warm; fi
FVD=; if [ -n "$WD" ]; then for c in "$WD/fvcheckd.py" "$WD/src/fvcheckd.py"; do [ -f "$c" ] && { FVD=$c; break; }; done; fi
if [ -n "$FVD" ]; then
  BINS=${FV_WARM_BINS:-$WD}; [ -f "$BINS/ccmp-warm" ] || BINS=$WD/bin
  # published layout: the binaries live where check/warm/pins.env says (default /scratch/fastverify-next/warm/v1)
  if [ ! -f "$BINS/ccmp-warm" ] && [ -f "$WD/pins.env" ]; then
    p=$(awk '$1=="PIN" && $2=="ccmp_warm" {print $4}' "$WD/pins.env"); [ -n "$p" ] && BINS=$(dirname "$p"); fi
  out=$(/usr/bin/python3 -I "$H/warmdiff.py" "$BASE/out/solution.export" "$BASE/out/challenge.export" "$BASE/challenge/comparator.json" \
        "$W/warm" --n "$WN" --seed 1 --jobs 6 --threads 4 --fvcheckd "$FVD" --bins "$BINS" --concurrent 16 2>&1)
  res=$(printf '%s\n' "$out" | grep '^RESULT')
  printf '%s\n' "$out" | grep -E '^(CRITICAL|AVAIL|VETO-WEAK|ORDER-DEPENDENT|CONCURRENCY-DEPENDENT)|died|not ready' | head -5
  if [ -z "$res" ]; then echo "FAIL warm: no RESULT line: $(printf '%s' "$out" | tail -c 300 | tr '\n' ' ')"; bad=1
  elif printf '%s\n' "$out" | grep -qE '^(CRITICAL|VETO-WEAK|ORDER-DEPENDENT|CONCURRENCY-DEPENDENT)|died|not ready'; then echo "FAIL warm: $res"; bad=1
  else echo "PASS warm: $res"; fi
else
  echo "SKIP warm: no check/warm (set FV_WARM_DIR=dir with fvcheckd.py and FV_WARM_BINS=dir with the three warm binaries)"
fi
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit $bad

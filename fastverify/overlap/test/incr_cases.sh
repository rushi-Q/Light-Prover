#!/bin/bash
# incr_cases.sh PLEANCHECKER WORKDIR THREADS : adversarial cases of the incremental Lean-kernel leg (rh-mid scale).
# Each case: snapshots + final through `pleanchecker --incremental` (stdin protocol); expected exit = the plain replay's.
# Inputs (environment): FV_BENCH_INPUTS = benchmark inputs dir (rh-mid/ref/solution.export = the honest rh-mid export);
#   OVERLAP_INPUTS = dir with the adversarial inputs midmut/midM1.export, midmut/midM2.export (kernel-invalid mutants of
#   the rh-mid export) and mid/s1.export, mid/s2.export (partial snapshot exports of rh-mid).
set -u
P=$1; W=$2; T=${3:-32}; mkdir -p "$W"
H=${FV_BENCH_INPUTS:?benchmark inputs directory with rh-mid/ref/solution.export (required)}/rh-mid/ref/solution.export
O=${OVERLAP_INPUTS:?directory with midmut/midM1.export, midmut/midM2.export, mid/s1.export, mid/s2.export (required)}
M1=$O/midmut/midM1.export; M2=$O/midmut/midM2.export
S1=$O/mid/s1.export; S2=$O/mid/s2.export
# truncated final: the first theorem declaration line that some later line references is deleted
if [ ! -s "$W/trunc.export" ]; then
  python3 - "$H" "$W/trunc.export" <<'PY'
import sys, json
src, dst = sys.argv[1], sys.argv[2]
lines = open(src, 'rb').read().split(b'\n')
# delete the 1000th "thm" line (an early, typically widely used library theorem)
k = 0
for i, l in enumerate(lines):
    if l.startswith(b'{"thm"'):
        k += 1
        if k == 1000:
            del lines[i]; break
open(dst, 'wb').write(b'\n'.join(lines))
PY
fi
pass=0; fail=0
run() {  # run NAME EXPECTED_RC CMDS...
  local name=$1 exp=$2; shift 2
  local t0=$(date +%s.%N)
  printf '%s\n' "$@" | "$P" --incremental -j"$T" > "$W/$name.out" 2> "$W/$name.err"
  local rc=$? dt=$(echo "$(date +%s.%N) - $t0" | bc)
  local how=$(grep -E "^\[incr\] (final|incremental path)" "$W/$name.err" | tail -2 | cut -c1-220 | tr '\n' ' ')
  if [ "$rc" = "$exp" ]; then pass=$((pass+1)); st=PASS; else fail=$((fail+1)); st=FAIL; fi
  printf '%s\t%s\texp=%s rc=%s\t%.1fs\t%s\n' "$st" "$name" "$exp" "$rc" "$dt" "$how"
}
run honest-final-only 0 "final $H"
run honest-self 0 "snap $H" "final $H"
run snapH-finalM1 1 "snap $H" "final $M1"
run snapH-finalM2 1 "snap $H" "final $M2"
run snapM1-finalH 0 "snap $M1" "final $H"
run snapM1-finalM1 1 "snap $M1" "final $M1"
run snapSnaps-finalM1 1 "snap $S1" "snap $S2" "final $M1"
run snapSnaps-finalH 0 "snap $S1" "snap $S2" "final $H"
run snapH-finalTrunc 1 "snap $H" "final $W/trunc.export"
run finalTrunc 1 "final $W/trunc.export"
run snapM2-snapH-finalH 0 "snap $M2" "snap $H" "final $H"
run garbage-snap-finalH 0 "snap /nonexistent" "snap $W/trunc.export" "final $H"
echo "RESULT pass=$pass fail=$fail"
[ $fail = 0 ]

#!/bin/bash
# 004 END-TO-END (needs FAST_TC, a native glibc-2.35 build of the fast toolchain's sources
# 7586a50cec; the deployed PGO binary /scratch/fastverify/tc/stage1 cannot run outside a glibc-2.38 container).
# OFFICIAL flow = officialflow.sh (lake build 4.33.1 + official lean4export + lake comparator 4.36);
# FAST flow = fastflow.sh = fastverify/pipeline/pipeline.sh with LEAN_TC=FAST_TC + native lean4export + pchk run.sh.
# (harness scripts copied from finding 023). Run: bash repro-e2e.sh   (16 CPUs)
#  proj-accept: Main proves riemannHypothesis `by tick_bump; tick_or_fail`  -> expected OFFICIAL rejects, FAST accepts
#  proj-export: `by tick_bump; first | tick_or_fail | exact Eq.refl 4`      -> expected both accept, exports differ
#  proj-heartbeats: PURE code (HA: def table := (List.range 400000).toArray), set_option maxHeartbeats 800 in riemannHypothesis := by touch_table; touch_table; use_table -> expected OFFICIAL rejects (deterministic timeout), FAST accepts
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-004}
export FAST_TC=${FAST_TC:-/scratch/fast-tc/7586}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"
for p in ${PROJS:-proj-accept proj-export proj-heartbeats}; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/$p" "$W/official-$p" "$W/challenge"; orc=$?
  echo "=== FAST flow (FAST_TC=$FAST_TC)"; bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$W/challenge/challenge.export"; frc=$?
  oe=$W/official-$p/solution.export; fe=$W/fast-$p/run/solution.export
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
  for e in "$oe" "$fe"; do [ -s "$e" ] && echo "    $e: $(stat -c %s $e) bytes sha256 $(sha256sum < $e | cut -c1-16)"; done
  [ -s "$oe" ] && [ -s "$fe" ] && { cmp -s "$oe" "$fe" && echo "    exports IDENTICAL" || echo "    exports DIFFER"; }
done

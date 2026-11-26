#!/bin/bash
# END-TO-END (needs FAST_TC = a native build of the fast toolchain's sources for a glibc-2.35 host
# 7586a50cec, which reports the same triple x86_64-pc-linux-gnu as the deployed PGO binary /scratch/fastverify/tc/stage1;
# the latter cannot run outside a glibc-2.38 container). OFFICIAL flow = officialflow.sh (lake build 4.33.1 + official
# lean4export + lake comparator 4.36); FAST flow = fastflow.sh = fastverify/pipeline/pipeline.sh with LEAN_TC=FAST_TC + native
# lean4export + pchk run.sh (harness scripts copied from tests 023/020).
# Run: bash repro-e2e.sh [WORKDIR]
#  proj-accept: expected OFFICIAL rejects (build error), FAST accepts
#  proj-export: expected both accept, exports differ (buildTarget's string literal)
#  proj-reject: expected OFFICIAL accepts, FAST rejects (#guard_msgs in #version)
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-e2e-061}
export FAST_TC=${FAST_TC:-/scratch/fast-tc/7586}
echo "FAST_TC lean --version: $($FAST_TC/bin/lean --version)"
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"
for p in proj-accept proj-export proj-reject; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/$p" "$W/official-$p" "$W/challenge"; orc=$?
  echo "=== FAST flow (FAST_TC=$FAST_TC)"; bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$W/challenge/challenge.export"; frc=$?
  oe=$W/official-$p/solution.export; fe=$W/fast-$p/run/solution.export
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
  for e in "$oe" "$fe"; do [ -s "$e" ] && echo "    $e: $(stat -c %s $e) bytes sha256 $(sha256sum < $e | cut -c1-16)"; done
  [ -s "$oe" ] && [ -s "$fe" ] && { cmp -s "$oe" "$fe" && echo "    exports IDENTICAL" || echo "    exports DIFFER"; }
done
rm -rf "$W"

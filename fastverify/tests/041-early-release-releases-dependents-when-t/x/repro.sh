#!/bin/bash
# repro (~4 min): OFFICIAL flow (lake build 4.33.1 + official lean4export + lake comparator 4.36) vs FAST
# flow (fastverify/pipeline/pipeline.sh, then pchk run.sh). Harness = officialflow.sh/fastflow.sh (copied here).
# Run: bash repro.sh [WORKDIR] (16 CPUs)
# proj/src/Big.lean is a Lean-4.33 `module` file with a large PRIVATE olean part (one theorem whose proof is a 2M-node term
# built by a metaprogram); proj/src/Main.lean = `import Big` + the 5 challenge theorems by rfl.
# expected: OFFICIAL rc=0 (ACCEPTED); FAST rc=1 (Main fails 'failed to open file .../Big.olean.private', RETRY_PRISTINE
# fails again within ~0.1 s, BUILD FAILED) - plus the Big.* mtimes showing the gap between .olean and .olean.private.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-earlyrel}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"
echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "=== SUMMARY official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
ls -la --time-style=full-iso "$W"/fast/run/proj/.lake/build/lib/lean/Big.* 2>/dev/null
grep -E "Big|Main" "$W"/fast/run/log/sched.log | cut -c1-300

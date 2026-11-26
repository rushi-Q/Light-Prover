#!/bin/bash
# 023 repro (~3 min): OFFICIAL flow (lake build 4.33.1 + official lean4export + lake comparator 4.36)
# vs FAST flow (fastverify/pipeline/pipeline.sh = prep.py deny line + sched_r.py, then pchk run.sh) on two crafted projects.
# Harness = officialflow.sh / fastflow.sh (copied here). Run: bash repro.sh   (16 CPUs)
#  proj-accept: src/Hijack.lean ends inside `namespace Foo` and defines Foo.Lean.modifyEnv (adds `theorem helper`);
#               src/Main.lean uses `helper`.          expected: OFFICIAL rc=1 (build fails), FAST rc=0 (ACCEPTED)
#  proj-export: same Hijack.lean; Main proves riemannHypothesis `by first | exact helper | rfl`.
#               expected: both ACCEPT, solution exports differ (fast proof term uses `helper`)
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-023}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"
for p in proj-accept proj-export; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/$p" "$W/official-$p" "$W/challenge"; orc=$?
  echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$W/challenge/challenge.export"; frc=$?
  oe=$W/official-$p/solution.export; fe=$W/fast-$p/run/solution.export
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
  for e in "$oe" "$fe"; do [ -s "$e" ] && echo "    $(basename $(dirname $(dirname $e)))/$(basename $(dirname $e)): $(stat -c %s $e) bytes sha256 $(sha256sum < $e | cut -c1-16), mentions name 'helper': $(grep -c '"str":"helper"' $e)"; done
  [ -s "$oe" ] && [ -s "$fe" ] && { cmp -s "$oe" "$fe" && echo "    exports IDENTICAL" || echo "    exports DIFFER"; }
done

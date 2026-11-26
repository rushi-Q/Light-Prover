#!/bin/bash
# 025 repro (~4 min): OFFICIAL flow (lake build 4.33.1 + official lean4export + lake comparator 4.36)
# vs FAST flow (fastverify/pipeline/pipeline.sh, then pchk run.sh). Harness = officialflow.sh/fastflow.sh (copied).
# Run: bash repro.sh [WORKDIR]   (16 CPUs)
# All three projects: src/Lemmas.lean = `import Lean.LibrarySuggestions.Default; def X (_n : Nat) : Prop := True;
# theorem X_holds (n) : X n := trivial` (gets the deny line); src/Main.lean (protected) uses `grind +suggestions`.
#  proj-export      : `theorem aux : X 5 ∨ True := by first | (left; grind +suggestions) | (right; trivial)` used by riemannHypothesis
#                     expected: both ACCEPT, exports DIFFER (official Or.inl via X_holds, fast Or.inr)
#  proj-falsereject : `have _h : X 5 := by grind +suggestions`  expected: OFFICIAL rc=0, FAST rc=1 (grind fails even after RETRY_PRISTINE)
#  proj-accept      : `fail_if_success (have _h : X 5 := by grind +suggestions)`  expected: OFFICIAL rc=1, FAST rc=0
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-025}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"
for p in proj-export proj-falsereject proj-accept; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/$p" "$W/official-$p" "$W/challenge"; orc=$?
  echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$W/challenge/challenge.export"; frc=$?
  oe=$W/official-$p/solution.export; fe=$W/fast-$p/run/solution.export
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
  for e in "$oe" "$fe"; do [ -s "$e" ] && echo "    $e: $(stat -c %s $e) bytes sha256 $(sha256sum < $e | cut -c1-16), names inl/inr/X_holds: $(grep -c '"str":"inl"' $e)/$(grep -c '"str":"inr"' $e)/$(grep -c '"str":"X_holds"' $e)"; done
  [ -s "$oe" ] && [ -s "$fe" ] && { cmp -s "$oe" "$fe" && echo "    exports IDENTICAL" || echo "    exports DIFFER"; }
done

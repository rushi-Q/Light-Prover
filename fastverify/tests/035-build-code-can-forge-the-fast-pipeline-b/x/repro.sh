#!/bin/bash
# Self-contained repro: OFFICIAL flow (lake build 4.33.1 + official lean4export + lake comparator 4.36)
# vs FAST flow (fastverify/pipeline/pipeline.sh + pchk run.sh) on the crafted project ./proj with the challenge ./challenge.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-035}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"
echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"
# (checked on release a17abf1) proj's default targets are [Main, Extra] and src/Extra.lean has a type error that
# Main does not import. The official comparator builds only its solution module (Lean 4.36 Lake/CLI/Check.lean:733,
# `lake build Main`), so Extra's error is NOT part of the official verdict: the OFFICIAL flow above (officialflow.sh, now
# `lake build Main`) ACCEPTS, like the package. This row keeps that visible: a default-target `lake build` does fail (on Extra),
# and both verdicts above are ACCEPTED all the same.
T33=${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
mkdir -p "$W/default" && cp -a "$D/proj" "$W/default/proj"
( cd "$W/default/proj" && PATH=$T33/bin:/usr/bin:/bin timeout 3600 lake build ) > "$W/default.log" 2>&1; drc=$?
echo "default-target lake build rc=$drc (not the comparator's build): $(grep -m1 -E 'error' "$W/default.log" | cut -c1-160)"
if [ $drc -ne 0 ] && grep -q 'Extra' "$W/default.log" && [ $orc -eq 0 ] && [ $frc -eq 0 ]; then res=PASS; else res=FAIL; fi
echo "=== RESULT case=extra-default-target-not-in-verdict official=$orc fast=$frc result=$res"

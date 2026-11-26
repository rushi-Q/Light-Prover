#!/bin/bash
# 035(a) repro: EARLY_RELEASE starts C against a B.olean forged by module A while B is still running.
# OFFICIAL = officialflow.sh (lake build + official lean4export + lake comparator), FAST = fastflow.sh (deployed pipeline copy,
# native off, pkgmode symlink, LEAN_TC unset) - harness from tests/063-*/x. Any test host, ~1 min.
D=$(cd "$(dirname "$0")" && pwd); H=$(ls -d $LIGHT_LEAN/fastverify/tests/063-*/x); W=${1:-${TMPDIR:-/tmp}/$USER-035a}
rm -rf "$W"; mkdir -p "$W"; cp -a "$H/challenge" "$W/challenge"; cp -a "$D/proj-forge" "$W/p"; unset LEAN_TC FAST_TC
echo "##### proj-forge"
bash "$H/officialflow.sh" "$W/p" "$W/off" "$W/challenge" > "$W/off.log" 2>&1; orc=$?
bash "$H/fastflow.sh" "$W/p" "$W/fast" "$W/challenge/challenge.export" > "$W/fast.log" 2>&1; frc=$?
grep -E '^OFFICIAL|official: lean4export' "$W/off.log" | sed 's/^/  /'; grep -E '^FAST|fast: export [0-9]' "$W/fast.log" | sed 's/^/  /'
grep -h "Built" "$W/fast/run/log/sched.log" | sed 's/^/  fast: /'
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; printf 'import C\nimport B\n#eval s!"cVal={cVal} bVal={bVal}"\n' > "$W/Q.lean"
for b in off/proj fast/run/proj; do echo "  $b: $(cd $W && LEAN_PATH=$W/$b/.lake/build/lib/lean:$T33/lib/lean $T33/bin/lean Q.lean 2>&1 | head -1)"; done
echo "=== SUMMARY proj-forge official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
oe=$W/off/solution.export; fe=$W/fast/run/solution.export
[ -s "$oe" ] && [ -s "$fe" ] && { cmp -s "$oe" "$fe" && echo "    exports IDENTICAL" || echo "    exports DIFFER"; }
rm -rf "$W"

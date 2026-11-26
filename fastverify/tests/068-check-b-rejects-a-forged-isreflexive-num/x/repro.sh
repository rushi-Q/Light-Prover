#!/bin/bash
# repro for 068 (~3 min, any x86-64 host): official Lean 4.33.1 build + official lean4export v4.33.0 of a
# valid toy (Challenge: main_thm : 2 + 2 = 4 := sorry; Main: same theorem proved through two SOLUTION-ONLY inductives Helper
# and Tree), then ONE exported InductiveVal flag of Helper/Tree is forged (flip.py) and each export goes through
#   OFFICIAL  = lake comparator 4.36 (cfg.json: Lean kernel + nanoda)      FAST = check B single and dual (run3.sh)
# plus every kernel alone (official leanchecker / pleanchecker-k / official nanoda / C07 nanoda / gruszka / nl-fast).
# Usage: bash repro.sh [WORKDIR]   (WORKDIR must be visible to the krun sandbox, which binds it read-only; default: a fresh dir work.PID
# inside this finding directory, removed at the end)
set -u
D=$(cd "$(dirname "$0")" && pwd); W=${1:-$D/work.$$}; mkdir -p "$W"
cp "$D"/Main.lean "$D"/Challenge.lean "$D"/mkexp.sh "$W"/ && cd "$W" || exit 2
bash mkexp.sh Challenge main_thm > /dev/null 2>&1; bash mkexp.sh Main main_thm 2>&1 | head -3
[ -s Main.export ] && [ -s Challenge.export ] || { echo "official build/export failed"; exit 2; }
python3 -I "$D/flip.py" Main.export "$W"
for f in Main.export sol_Helper_isReflexive.export sol_Tree_isReflexive.export sol_Tree_numNested.export sol_Tree_numNested0.export; do
  out=$(bash "$D/run3.sh" "$W/$f" "$W/Challenge.export"); echo "$out"
  o=$(echo "$out" | grep -o 'OFFICIAL lake comparator exit=[0-9]*' | grep -o '[0-9]*$')
  s=$(echo "$out" | grep -o 'FAST-B single (gruszka+kcompare) exit=[0-9]*' | grep -o '[0-9]*$')
  du=$(echo "$out" | grep -o 'FAST-B dual (gruszka AND nano-lean + kcompare) exit=[0-9]*' | grep -o '[0-9]*$')
  echo "=== SUMMARY ${f%.export} official_rc=$o fast_rc=$du (check B dual; single=$s) (0 = ACCEPTED)"
done
echo "--- every kernel alone (0 accept):"; bash "$D/run_kernels.sh" "$W"/Main.export "$W"/sol_*.export
[ -n "${1:-}" ] || rm -rf "$W"

#!/bin/bash
# challenge-config cases: non-RH challenge configuration (solution_module = Solution, theorem names foo/bar, definition_names = [myDef],
# permitted axioms WITHOUT Classical.choice). OFFICIAL = officialflow.sh (generic: solution module from comparator.json).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-fvtest-challenge-config}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
for p in ${CASES:-proj-honest proj-defbody proj-classical proj-stmt proj-sorry proj-extra-thm}; do
  cp -a "$D/$p" "$W/$p"; echo "##### $p"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export' "$W/off-$p.log" | head -4 | cut -c1-200 | sed 's/^/  /'
  grep -E '^FAST|fast: export [0-9]|fast: path' "$W/fast-$p.log" | cut -c1-250 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

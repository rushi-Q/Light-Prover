#!/bin/bash
# challenge-variants cases: more comparator.json shapes (enable_nanoda, definitions only, nested module names, «»-escaped and unicode
# theorem names, Quot.sound not permitted, sorryAx permitted). OFFICIAL = officialflow.sh (challenge-variants variant), FAST = the package.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-fvtest-challenge-variants}
rm -rf "$W"; mkdir -p "$W"
while read -r p c; do
  [ -n "$p" ] || continue
  echo "$CASES" | grep -qw -- "$p" || [ -z "${CASES:-}" ] || continue
  [ -d "$W/$c" ] || cp -a "$D/$c" "$W/$c"
  cp -a "$D/$p" "$W/$p"; echo "##### $p"; echo "  challenge: $c"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/$c" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$W/$c/challenge.export" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export|official: comparator' "$W/off-$p.log" | head -6 | cut -c1-200 | sed 's/^/  /'
  grep -E '^FAST|fast: export [0-9]|fast: path' "$W/fast-$p.log" | cut -c1-250 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done < "$D/cases.txt"
[ -n "${KEEP_WORK:-}" ] || rm -rf "$W"

#!/bin/bash
# odd-layouts cases: odd but valid project layouts (symlinked source file / directory / file outside the project, non-ASCII and deep
# module paths, guillemet module names, CRLF + BOM sources). OFFICIAL = officialflow.sh (lake build 4.33.1 + lean4export + comparator).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-fvtest-odd-layouts}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
for p in ${CASES:-proj-symlink-file proj-symlink-dir proj-unicode proj-guillemet proj-symlink-outside proj-crlf}; do
  cp -a "$D/$p" "$W/$p"; echo "##### $p"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export' "$W/off-$p.log" | head -4 | cut -c1-200 | sed 's/^/  /'
  grep -E '^FAST|fast: export [0-9]|fast: path' "$W/fast-$p.log" | cut -c1-250 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

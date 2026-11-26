#!/bin/bash
# repro: lean_lib globs given as a single string (Lake accepts array-or-singleton). Run with FAST_PIPELINE_DIR=<pipeline under test>.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-glob}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
unset LEAN_TC FAST_TC
for p in ${CASES:-proj-glob1 proj-mls}; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export' "$W/off-$p.log" | head -4 | cut -c1-200 | sed 's/^/  /'
  grep -E 'SUMMARY|^FAST|fast: export [0-9]|fast: check: Your' "$W/fast-$p.log" | cut -c1-200 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

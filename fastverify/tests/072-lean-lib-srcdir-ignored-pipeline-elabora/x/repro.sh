#!/bin/bash
# repro (011 class; checks the fix-final pipeline): lean_lib-level srcDir. Lake: LeanLib.srcDir = pkg.srcDir / lib.srcDir
# (Lake/Config/LeanLib.lean:34-35) -> module Main = src/real/Main.lean (uses sorry -> official comparator REJECTS).
# The pipeline (deployed and fix-final prep.py/mkargs) maps modules from PRISTINE/src only -> Main = decoy src/Main.lean (honest).
# proj-pkgsrc: package srcDir = "lib" (lib/Main.lean uses sorry), decoy src/Main.lean. proj-both: lakefile.lean (used by Lake when
# both exist) puts Main under src/real, lakefile.toml (what the pipeline/mkargs read) does not.
# Any x86-64 host, ~2 min. FAST_PIPELINE_DIR=<pipeline> tests a fix.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-libsrc}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
unset LEAN_TC FAST_TC
for p in ${CASES:-proj-libsrc proj-pkgsrc proj-both}; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export' "$W/off-$p.log" | head -4 | cut -c1-200 | sed 's/^/  /'
  grep -E 'SUMMARY|^FAST|fast: export [0-9]|fast: check: Your' "$W/fast-$p.log" | cut -c1-200 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

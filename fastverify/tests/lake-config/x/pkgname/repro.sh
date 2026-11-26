#!/bin/bash
# repro: the fix of 043 inside a proposed build-side fix (sched_r.py _pkg_name: regex name\s*=\s*"([^"]*)" on lakefile.toml).
# Lake parses TOML properly: name = 'mini' (literal string) and name = "mi\u006Ei" (escape) both give package id "mini".
# Main.lean: theorem pkg_is_none : pkg% = "none" := rfl (pkg% = Environment.getModulePackage?) -> official REJECTED.
# Expected with fix-final: sq -> regex finds nothing -> package none -> ACCEPTED; esc -> package 'mi\u006Ei' -> still REJECTED (but a
# different olean/package id than Lake's). Run with FAST_PIPELINE_DIR=<fix-final copy>.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-pkgname}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
unset LEAN_TC FAST_TC
for p in ${CASES:-proj-sq proj-esc proj-sq2}; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export' "$W/off-$p.log" | head -4 | cut -c1-200 | sed 's/^/  /'
  grep -E 'SUMMARY|^FAST|fast: export [0-9]|fast: check: Your' "$W/fast-$p.log" | cut -c1-200 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

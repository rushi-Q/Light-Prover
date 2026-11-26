#!/bin/bash
# repro: Lake-level lean argument semantics that the pipeline does not reproduce (011 family; also a gap in the fix-final mkargs.py).
# Lake 4.33.1 (src/lean/lake/Lake/Build/Module.lean:972, Config/LeanLib.lean:194-211, Config/LeanConfig.lean:142):
#  * buildType = "debug" adds the lean option debugAssertions = true  -> `debug_assert! c; b` elaborates to `if c then b else panic! ..`
#  * command line = weakLeanArgs ++ buildType.leanArgs ++ pkg.moreLeanArgs ++ lib.moreLeanArgs  (later -D wins)
#  * leanOptions go into the module setup JSON, which OVERRIDES command-line -D options (Lean/Elab/Frontend.lean:305-306)
# proj-debug  : buildType="debug"; theorem f_zero : f 0 = 5 := rfl with f n := debug_assert! n > 0; 5   -> official build error
# proj-debug-export: same lakefile, f used in the proof term of riemannHypothesis -> both ACCEPT, exports DIFFER (CRITICAL-EXPORT)
# proj-weak   : weakLeanArgs=-DautoImplicit=true, moreLeanArgs=-DautoImplicit=false; def idf (x : α) := x -> official build error
# proj-optweak: [leanOptions] autoImplicit=false + weakLeanArgs=-DautoImplicit=true; same def -> official build error
# proj-twolib : module Util in lean_lib A (first, default target) and lean_lib B (autoImplicit=false); Lake resolves the import to
#               the LAST lib (Package.findModule? = findSomeRev?, Lake/Config/Module.lean:59) -> official build error
# proj-extra  : non-compiling Extra in default-target lib A (Main does not import it) and in an earlier non-target lib C ->
#               lake builds all of A -> official REJECT; mkargs assigns Extra to C (first match) and never builds it
# OFFICIAL flow = officialflow.sh (lake build 4.33.1 + official lean4export + lake comparator); FAST = fastflow.sh (pipeline.sh +
# native exporter + pchk). Harness scripts copied from test 063. Any x86-64 host, ~2 min. FAST_PIPELINE_DIR=<pipeline dir> tests a fix.
# officialflow.sh runs the OFFICIAL comparator's build, `lake build Main`
# (Lean 4.36 Lake/CLI/Check.lean:733): proj-extra's non-compiling Extra (in default-target lib A, not imported by Main) is
# not part of the official verdict any more (ACCEPTED; EXPECT updated); proj-twolib still fails, Util is in Main's closure.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-lakeargs}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
unset LEAN_TC FAST_TC
for p in ${CASES:-proj-debug proj-debug-export proj-weak proj-optweak proj-twolib proj-extra}; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export' "$W/off-$p.log" | head -4 | cut -c1-200 | sed 's/^/  /'
  grep -E 'SUMMARY|^FAST|fast: export [0-9]|fast: check: Your' "$W/fast-$p.log" | cut -c1-200 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

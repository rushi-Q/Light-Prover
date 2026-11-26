#!/bin/bash
# repro for 063: the fast pipeline only elaborates Lean modules; `lake build` also compiles and LINKS the project's
# default targets (here a lean_exe whose @[extern] C symbol does not exist -> link error -> official build fails).
# OFFICIAL flow = officialflow.sh (lake build 4.33.1 + official lean4export + lake comparator 4.36);
# FAST flow = fastflow.sh = fastverify/pipeline/pipeline.sh + native lean4export + pchk run.sh with the challenge
# case b proj-pre: lean_lib with precompileModules = true (lake compiles the project tactic module to a shared library and
# loads it when elaborating Main: native execution) vs the pipeline (interpreted) under a tight maxHeartbeats.
# case c proj-target: defaultTargets names a target the package does not have; case d proj-config: an ill-typed lakefile
# field (moreServerArgs = 7, Lake expects an array). Lake rejects both before building; the pipeline never reads the lakefile.
# case e proj-nodefault: no defaultTargets -> `lake build` builds nothing ("Nothing to build", rc 0), the official export of
# Main then fails; the pipeline builds every src file.
# (harness scripts copied from tests 023/020). Any x86-64 host, ~2 min. FAST_PIPELINE_DIR=<fixed pipeline> tests a fix.
# officialflow.sh runs the OFFICIAL comparator's build, `lake build Main`
# (Lean 4.36 Lake/CLI/Check.lean:733: only the configured solution module), not a default-target `lake build`: proj-exe's
# lean_exe link error, proj-target's unknown default target and proj-nodefault's empty default build are not part of
# the official verdict any more (the official flow ACCEPTS those three, as the package does; EXPECT updated).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-063}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
unset LEAN_TC FAST_TC
for p in proj-exe proj-pre proj-target proj-config proj-nodefault; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  bash "$D/officialflow.sh" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|error|official: lean4export|Nothing to build' "$W/off-$p.log" | head -5 | sed 's/^/  /'
  grep -E 'SUMMARY|^FAST|fast: export [0-9]|fast: check: Your' "$W/fast-$p.log" | cut -c1-200 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

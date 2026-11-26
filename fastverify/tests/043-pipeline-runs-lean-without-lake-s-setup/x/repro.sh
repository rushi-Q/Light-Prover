#!/bin/bash
# repro (~3 min): OFFICIAL flow (lake build 4.33.1 + official lean4export + lake comparator 4.36) vs FAST
# flow (fastverify/pipeline/pipeline.sh, then pchk run.sh). Harness = officialflow.sh/fastflow.sh (copied here).
# Run: bash repro.sh [WORKDIR] (16 CPUs)
# src/Probe.lean: `def pkg : String := thisPackage` where the elaborator returns toString ((← getEnv).getModulePackage?)
#  proj-export: riemannHypothesis's proof mentions pkg     expected: both ACCEPT, exports differ ("(some mini)" vs "none")
#  proj-accept: Main has `#guard pkg == "none"`          expected: OFFICIAL rc=1 (build fails), FAST rc=0
# Part 0 shows the olean difference directly: same file, same args, `lake build` vs plain `lean -o` (what sched_r.py runs).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-pkg}
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
rm -rf "$W"; mkdir -p "$W/triv/src"; cp -a "$D/challenge" "$W/challenge"
( cd "$W/triv" && printf 'theorem t : (2:Nat)+2=4 := rfl\n' > src/Main.lean && cp "$D/proj-export/lean-toolchain" . &&
  printf 'name = "mini"\nsrcDir = "src"\ndefaultTargets = ["Main"]\nmoreLeanArgs = ["--tstack=400000"]\n[[lean_lib]]\nname = "Main"\nroots = ["Main"]\n' > lakefile.toml &&
  PATH=$T33/bin:/usr/bin:/bin lake build > /dev/null 2>&1 && mkdir d && $T33/bin/lean --tstack=400000 -R src src/Main.lean -o d/Main.olean &&
  { cmp -s .lake/build/lib/lean/Main.olean d/Main.olean && echo "=== part 0: oleans IDENTICAL" || echo "=== part 0: Main.olean lake ($(stat -c %s .lake/build/lib/lean/Main.olean) B) vs plain lean ($(stat -c %s d/Main.olean) B) DIFFER; package string 'mini' in lake olean: $(strings .lake/build/lib/lean/Main.olean | grep -c '^mini$'), in plain olean: $(strings d/Main.olean | grep -c '^mini$')"; } )
for p in proj-export proj-accept; do
  cp -a "$D/$p" "$W/$p"
  echo "##### $p"
  echo "=== OFFICIAL flow"; bash "$D/officialflow.sh" "$W/$p" "$W/official-$p" "$W/challenge"; orc=$?
  echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$W/challenge/challenge.export"; frc=$?
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
  for e in "$W/official-$p/solution.export" "$W/fast-$p/run/solution.export"; do [ -s "$e" ] && echo "    $e: $(stat -c %s $e) B, string literals: $(grep -o '"strVal":"[^"]*"' $e | head -3 | tr '\n' ' ')"; done
done

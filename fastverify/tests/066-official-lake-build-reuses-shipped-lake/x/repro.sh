#!/bin/bash
# repro for 066: a project directory that SHIPS build artifacts (.lake/build) whose Lake trace matches the current
# source, but whose Main.olean was produced from a DIFFERENT source. The official flow (`lake build` on the project as given)
# trusts the trace and keeps the shipped .olean; the fast pipeline copies only src/ (prep.py) and rebuilds from source.
# OFFICIAL flow = officialflow.sh (lake build 4.33.1 + official lean4export + lake comparator 4.36);
# FAST flow = fastflow.sh = fastverify/pipeline/pipeline.sh + native lean4export + pchk run.sh with the challenge
# (harness scripts copied from test 023). Any x86-64 host, ~1 min. OFFICIALFLOW=officialflow-clean.sh = the fixed official procedure
# (lake build on a copy WITHOUT the root .lake/build) -> both cases must AGREE. The projects are generated here (no binaries in the finding dir):
#   A = honest source (riemannHypothesis := rfl), B = same with `sorry`; both built once with the official lake 4.33.1;
#   shipped-good = B's source + B's .lake/build with A's Main.olean;  shipped-bad = A's source + A's .lake/build with B's Main.olean.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-066}
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
TAIL='theorem riemannZeta_eq_zero_re : (2 : Nat) + 1 = 3 := rfl
theorem LFunction_ne_zero_of_half_lt_re : (3 : Nat) + 1 = 4 := rfl
theorem LFunction_eq_zero_re : (4 : Nat) + 1 = 5 := rfl
theorem LFunction_eq_zero_re_of_isPrimitive : (5 : Nat) + 1 = 6 := rfl'
for v in A:rfl B:sorry; do n=${v%%:*}; pf=${v#*:}
  mkdir -p "$W/$n/src"; cp "$D/base/lakefile.toml" "$D/base/lean-toolchain" "$W/$n/"
  printf 'theorem riemannHypothesis : (2 : Nat) + 2 = 4 := %s\n%s\n' "$pf" "$TAIL" > "$W/$n/src/Main.lean"
  (cd "$W/$n" && PATH=$T33/bin:/usr/bin:/bin lake build > "$W/$n.build.log" 2>&1) || { echo "lake build of $n failed"; exit 2; }
done
cp -a "$W/B" "$W/shipped-good"; cp "$W/A/.lake/build/lib/lean/Main.olean" "$W/shipped-good/.lake/build/lib/lean/Main.olean"
cp -a "$W/A" "$W/shipped-bad";  cp "$W/B/.lake/build/lib/lean/Main.olean" "$W/shipped-bad/.lake/build/lib/lean/Main.olean"
unset LEAN_TC FAST_TC
for p in shipped-good shipped-bad; do
  echo "##### $p"
  echo "  (source: riemannHypothesis := $(grep -o ':= \(rfl\|sorry\)$' "$W/$p/src/Main.lean" | head -1 | cut -c4-); shipped Main.olean from the other source)"
  bash "$D/${OFFICIALFLOW:-officialflow.sh}" "$W/$p" "$W/off-$p" "$W/challenge" > "$W/off-$p.log" 2>&1; orc=$?
  bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/fast-$p.log" 2>&1; frc=$?
  grep -E '^OFFICIAL|official: lean4export|comparator: (Your|error)' "$W/off-$p.log" | head -4 | sed 's/^/  /'
  grep -E 'SUMMARY|^FAST|fast: export [0-9]|ccmp end|Illegal|sorry' "$W/fast-$p.log" | head -5 | cut -c1-200 | sed 's/^/  /'
  echo "=== SUMMARY $p official_rc=$orc fast_rc=$frc (0 = ACCEPTED)"
done
rm -rf "$W"

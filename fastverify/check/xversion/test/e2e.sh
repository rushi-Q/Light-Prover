#!/bin/bash
# check/xversion/test/e2e.sh [FASTVERIFY] [WORK] -- the cross-version gate wired into bin/fastverify --preset sound:
# toy projects (core only, no dependencies) on other official releases, challenge built + exported officially by the
# package (B0 + E0 of that release), judged by --preset sound, compared with the release's OWN official flow
# (lake build + bundled leanexport + bundled lake comparator):
#   v437-real-hole   : challenge keeps a real body for its definition_names hole -> official 4.37 REJECTS
#                      ("Challenge definition is not sorried"); the package must REJECT via the gate, before any build
#   v437-sorried-hole: the same with `sorry` -> ACCEPTED by both
#   v435-real-hole   : 4.35 has no such rule -> ACCEPTED by both
#   v435-axiom       : foo proved from an extra axiom -> REJECTED by both (the gate passes, CS rejects)
# A case is SKIPPED when the package does not list the release (config/components.json lean_toolchains).
# PASS iff every run case gives the official verdict. Prints PASS/FAIL/SKIP rows and RESULT.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${1:-$(cd "$H/../../.." && pwd)}; W=${2:-/tmp/xve2e.$$}
rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
fails=0; ran=0
tcpath() { python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1]))["lean_toolchains"]; t=c.get(sys.argv[2]); print(t["prefix"] if t else "")' "$FV/config/components.json" "$1"; }
mk() { # mk DIR LIB TOOLCHAIN FILE CONTENT
  mkdir -p "$1"; printf 'name = "%s"\ndefaultTargets = ["%s"]\n\n[[lean_lib]]\nname = "%s"\n' "$2" "$2" "$2" > "$1/lakefile.toml"
  echo "$3" > "$1/lean-toolchain"; printf '%b' "$5" > "$1/$4"; }
case_() { # case_ NAME VERSION HOLE_BODY SOLUTION_EXTRA [PROOF]
  local n=$1 v=$2 hole=$3 extra=$4 pf=${5:-rfl} tc d; tc=$(tcpath "leanprover/lean4:$v")
  if [ -z "$tc" ] || [ ! -x "$tc/bin/lake" ]; then echo "SKIP $n (package does not list leanprover/lean4:$v)"; return; fi
  d=$W/$n; ran=$((ran+1))
  mk "$d/chal" Challenge "leanprover/lean4:$v" Challenge.lean "def f (n : Nat) : Nat := $hole\ntheorem foo : f 2 = f 2 := sorry\n"
  echo '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":["foo"],"definition_names":["f"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}' > "$d/chal/comparator.json"
  mk "$d/sol" Main "leanprover/lean4:$v" Main.lean "def f (n : Nat) : Nat := n + 1\n${extra}theorem foo : f 2 = f 2 := $pf\n"
  # the release's own official flow
  local E=(env -i PATH="$tc/bin:/usr/bin:/bin" HOME="$d/home" LANG=C.UTF-8) orc
  local TG="foo f propext Quot.sound Classical.choice Quot Quot.mk Quot.lift Quot.ind Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
  for x in chal sol; do local m; m=$([ $x = chal ] && echo Challenge || echo Main); cp -a "$d/$x" "$d/off-$x"
    ( cd "$d/off-$x" && "${E[@]}" lake build > build.log 2>&1 && "${E[@]}" LEAN_PATH="$d/off-$x/.lake/build/lib/lean:$tc/lib/lean" LEAN_ABORT_ON_PANIC=1 leanexport $m -- $TG > "$d/off-$x.export" 2>/dev/null ); done
  ( cd "$d/off-chal" && "${E[@]}" lake comparator --config comparator.json --challenge-from-export "$d/off-chal.export" --solution-from-export "$d/off-sol.export" > "$d/official.log" 2>&1 ); orc=$?
  # the package
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$d/sol" "$d/chal" "$d/out" --preset sound --threads 4 > "$d/fv.log" 2>&1; local frc=$?
  local info; info=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); x=(r.get("inputs",{}).get("challenge_export") or {}).get("xversion") or {}
print(r.get("verdict"), "| build:", (r.get("build") or {}).get("option"), "| gate:", x.get("verdict"), x.get("lean_version"), "|", (r.get("verdict_basis") or "")[:110])' "$d/out/result.json" 2>/dev/null)
  if [ "$orc" = "$frc" ]; then echo "PASS $n: official exit $orc, package exit $frc ($info)"
  else echo "FAIL $n: official exit $orc ($(tail -n 1 "$d/official.log")), package exit $frc ($info)"; fails=$((fails+1)); fi
}
case_ v437-real-hole    v4.37.0-rc1 'n + 1' ''
case_ v437-sorried-hole v4.37.0-rc1 'sorry' ''
case_ v435-real-hole    v4.35.0     'n + 1' ''
case_ v435-axiom        v4.35.0     'sorry' 'axiom cheat : False\n' 'cheat.elim'
if [ $fails = 0 ]; then echo "RESULT: PASS ($ran run)"; rm -rf "$W"; exit 0; else echo "RESULT: FAIL ($fails) - work dir $W"; exit 1; fi

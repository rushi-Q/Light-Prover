#!/bin/bash
# tests/toolchain/v436.sh [WORK]  -- generality test: a project on a SECOND official Lean release (v4.36.0).
# Three toy projects pinned to leanprover/lean4:v4.36.0 (no dependencies) are judged against a toy challenge by
#   (a) the plain OFFICIAL 4.36 flow, run here by hand: `lake build` + the release's own `leanexport` + `lake comparator`
#   (b) the package: bin/fastverify PROJECT CHALLENGE OUT --check C3,C0
# PASS iff for every case the package verdict == the official verdict, and when the official export exists the package's
# solution.export is byte-identical to it. good -> ACCEPTED, sorry -> REJECTED (sorryAx), axiom -> REJECTED (cheat).
# The fast build must DECLINE for 4.36 (validated only for 4.33.1) -> official build; the native exporter declines
# (4.33.1 only) -> official leanexport. SKIP (exit 3) if the package does not list leanprover/lean4:v4.36.0.
main() {
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd)
T36=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/v436.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
if ! python3 -I -c 'import json,sys; sys.exit(0 if "leanprover/lean4:v4.36.0" in json.load(open(sys.argv[1]))["lean_toolchains"] else 1)' "$FV/config/components.json"; then
  echo "SKIP v436: config/components.json does not list leanprover/lean4:v4.36.0"; echo "RESULT: SKIP"; exit 3; fi
mk() { # mk DIR LIBNAME FILE CONTENT
  mkdir -p "$1"; printf 'name = "%s"\ndefaultTargets = ["%s"]\n\n[[lean_lib]]\nname = "%s"\n' "$2" "$2" "$2" > "$1/lakefile.toml"
  echo 'leanprover/lean4:v4.36.0' > "$1/lean-toolchain"; printf '%b' "$4" > "$1/$3"; }
mk "$W/chal" Challenge Challenge.lean 'theorem foo : 2 + 2 = 4 := sorry\n'
echo '{"challenge_module": "Challenge", "solution_module": "Main", "theorem_names": ["foo"], "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}' > "$W/chal/comparator.json"
mk "$W/good" Main Main.lean 'theorem foo : 2 + 2 = 4 := rfl\n'
mk "$W/sorry" Main Main.lean 'theorem foo : 2 + 2 = 4 := sorry\n'
mk "$W/axiom" Main Main.lean 'axiom cheat : False\ntheorem foo : 2 + 2 = 4 := cheat.elim\n'
TG="Quot Quot.mk Quot.lift Quot.ind foo propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
OENV=(env -i PATH="$T36/bin:/usr/bin:/bin" HOME="$W/home" LANG=C.UTF-8)
offexp() { # offexp DIR MODULE OUT  (official: lake build + leanexport) -> rc
  ( cd "$1" && "${OENV[@]}" lake build > "$1.build.log" 2>&1 ) || return 1
  ( cd "$1" && "${OENV[@]}" LEAN_PATH="$1/.lake/build/lib/lean:$T36/lib/lean" LEAN_ABORT_ON_PANIC=1 "$T36/bin/leanexport" "$2" -- $TG > "$3" 2> "$3.err" ) || return 1; }
offexp "$W/chal" Challenge "$W/challenge.export" || { echo "FAIL v436: official challenge build/export failed"; echo "RESULT: FAIL"; exit 1; }
rm -rf "$W/chal/.lake" "$W/chal/lake-manifest.json"; cp "$W/challenge.export" "$W/chal/challenge.export"
fails=0
for c in good sorry axiom; do
  cp -a "$W/$c" "$W/$c.off"
  if offexp "$W/$c.off" Main "$W/$c.off.export"; then
    ( cd "$W/chal" && "${OENV[@]}" timeout 600 lake comparator --config "$W/chal/comparator.json" --challenge-from-export "$W/challenge.export" \
        --solution-from-export "$W/$c.off.export" > "$W/$c.off.cmp" 2>&1 ); orc=$?
    osha=$(sha256sum < "$W/$c.off.export" | cut -c1-16)
  else orc=1; osha=-; fi
  env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FV/bin/fastverify" "$W/$c" "$W/chal" "$W/$c.out" --check C3,C0 --threads 8 > "$W/$c.fv.log" 2>&1; frc=$?
  read -r fsha fbuild fexp < <(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); e=r.get("export") or {}; b=r.get("build") or {}
print((e.get("sha256") or "-")[:16], b.get("mode"), e.get("mode"))' "$W/$c.out/result.json" 2>/dev/null || echo "- - -")
  ok=1; [ "$orc" = "$frc" ] || ok=0; [ "$orc" = 0 ] && [ "$osha" != "$fsha" ] && ok=0
  [ "$fbuild" = official ] || ok=0     # the fast build must decline for 4.36 (not validated)
  line="v436 $c: official rc=$orc sha=$osha | package rc=$frc sha=$fsha build=$fbuild export=$fexp"
  if [ $ok = 1 ]; then echo "PASS $line"; else echo "FAIL $line"; fails=$((fails+1))
    # diagnostics (the work dir may be removed by the caller): verdict basis, warnings and the run log tail
    python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print("  verdict_basis:", r.get("verdict_basis")); print("  warnings:", r.get("warnings")); print("  checks:", {k: (v or {}).get("verdict") for k, v in (r.get("checks") or {}).items()})' "$W/$c.out/result.json" 2>/dev/null
    tail -n 8 "$W/$c.fv.log" | sed 's/^/  log: /'; tail -n 5 "$W/$c.off.cmp" 2>/dev/null | sed 's/^/  official: /'; fi
done
[ $fails = 0 ] && { echo "RESULT: PASS"; exit 0; } || { echo "RESULT: FAIL ($fails)"; exit 1; }
}
main "$@"; exit $?

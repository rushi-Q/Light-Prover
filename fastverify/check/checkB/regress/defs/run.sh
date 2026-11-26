#!/bin/bash
# check/checkB/regress/defs/run.sh WORK [JOBS] -- definition_names regression for check B (kcompare patch 02, v4).
# Generates the corpus (gen.py: a challenge with 5 definition "holes" + 3 theorems, 25 solution projects), builds every
# project with the OFFICIAL Lean 4.33.1 `lake build` and exports it with the OFFICIAL lean4export (both pinned in
# config/components.json), then judges each export with
#   * the OFFICIAL comparator (check/official/check.sh = unmodified Lean 4.36 lake comparator, from exports) = reference,
#   * kcompare --definitions directly (pinned binary of check/checkB/components.json),
#   * check-b.sh --dual (C3) and --single (C4),
#   * optionally $REFCMPD (RefCmpD.lean compiled with the 4.36 toolchain: official Lake.Check compareAt + checkAxioms only).
# Row status: PASS = same verdict as the official comparator, DECL = check B declined (fail closed), FAIL-ACCEPT /
# FAIL-REJECT = wrong verdict. Exit 0 iff no FAIL row and every case built. ~3 min with JOBS=16.
# (whole body in main(): bash parses it completely before running)
main() {
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); ROOT=$(cd "$H/../../../.." && pwd)
W=$(mkdir -p "$1" && cd "$1" && pwd); J=${2:-8}
cfg() { python3 -I -c 'import json,sys; o=json.load(open(sys.argv[1]))
for k in sys.argv[2].split("|"): o=o[k]
print(o)' "$ROOT/config/components.json" "$1"; }
T33=$(cfg 'lean_toolchains|leanprover/lean4:v4.33.1|prefix'); EXP=$(cfg 'lean_toolchains|leanprover/lean4:v4.33.1|official_lean4export|path')
KC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["bin_dir"])' "$ROOT/check/checkB/components.json")/kcompare
THMS=foo,bar,baz; DEFS=myDef,myFun,idU,spare,pf; AXS=propext,Quot.sound
TARGETS="Quot Quot.mk Quot.lift Quot.ind foo bar baz propext Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam myDef myFun idU spare pf"
# WORK must be empty or a previous WORK of this script (marker file): never wipe a foreign directory
if [ -n "$(ls -A "$W")" ] && [ ! -f "$W/.fv-defs-work" ]; then echo "run.sh: $W is not empty and not a defs work dir"; exit 2; fi
rm -rf "$W"/*; touch "$W/.fv-defs-work"; python3 -I "$H/gen.py" "$W"
printf '{"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["foo", "bar", "baz"],\n "definition_names": ["myDef", "myFun", "idU", "spare", "pf"], "permitted_axioms": ["propext", "Quot.sound"]}\n' > "$W/comparator.json"
bexp() {  # DIR MODULE -> DIR/out.export, DIR/export.rc
  ( cd "$1" && env -i HOME="$HOME" PATH=$T33/bin:/usr/bin:/bin lake build > build.log 2>&1 ) || { echo build > "$1/export.rc"; return; }
  ( cd "$1" && env -i HOME="$HOME" PATH=$T33/bin:/usr/bin:/bin LEAN_PATH=$1/.lake/build/lib/lean:$T33/lib/lean "$EXP" $2 -- $TARGETS > out.export 2> export.err ) \
    && echo 0 > "$1/export.rc" || echo export > "$1/export.rc"
}
export -f bexp; export T33 EXP TARGETS HOME
bexp "$W/chal" Challenge; [ "$(cat "$W/chal/export.rc")" = 0 ] || { echo "challenge build failed"; exit 2; }
CH=$W/chal/out.export
cut -f1 "$W/cases.tsv" | xargs -P "$J" -I{} bash -c 'bexp "$0/{}" Solution' "$W"
vb() { python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])["exit"])' "$1" 2>/dev/null || echo E; }
st() { if [ "$2" = 2 ]; then echo DECL; elif [ "$2" = "$1" ]; then echo PASS; elif [ "$2" = 0 ]; then echo FAIL-ACCEPT; else echo FAIL-REJECT; fi; }
printf 'case\texpected\tofficial\tref\tkcompare\tC3\tC4\tstatus\n'
fails=0; n=0
while IFS=$'\t' read -r c exp; do
  d=$W/$c; n=$((n+1))
  if [ "$(cat "$d/export.rc")" != 0 ]; then printf '%s\t%s\tBUILD-FAILED\n' "$c" "$exp"; echo "RESULT defs-$c build-failed FAIL"; fails=$((fails+1)); continue; fi
  bash "$ROOT/check/official/check.sh" "$d/out.export" "$CH" "$W/comparator.json" --json "$d/off.json" > "$d/off.log" 2>&1 < /dev/null
  o=$(vb "$d/off.json")
  r=-; [ -n "${REFCMPD:-}" ] && { "$REFCMPD" "$CH" $THMS $DEFS $AXS "$d/out.export" > "$d/ref.log" 2>&1; r=$?; }
  "$KC" -j 2 --challenge "$CH" --theorems $THMS --definitions $DEFS --axioms $AXS "$d/out.export" > "$d/kc.log" 2>&1; k=$?
  bash "$ROOT/check/checkB/check-b.sh" "$d/out.export" "$CH" "$W/comparator.json" --threads 4 --dual --json "$d/c3.json" > /dev/null 2>&1 < /dev/null
  c3=$(vb "$d/c3.json")
  bash "$ROOT/check/checkB/check-b.sh" "$d/out.export" "$CH" "$W/comparator.json" --threads 4 --single --json "$d/c4.json" > /dev/null 2>&1 < /dev/null
  c4=$(vb "$d/c4.json")
  s="$(st "$o" "$k")/$(st "$o" "$c3")/$(st "$o" "$c4")"
  case "$s" in *FAIL*) fails=$((fails+1));; esac
  { [ "$o" = 0 ] || [ "$o" = 1 ]; } || { s="NO-OFFICIAL-VERDICT($o)"; fails=$((fails+1)); }
  [ "$r" = - ] || [ "$r" = "$o" ] || { s="$s REF-DIFFERS"; fails=$((fails+1)); }
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$c" "$exp" "$o" "$r" "$k" "$c3" "$c4" "$s"
  case "$s" in *FAIL*|*NO-OFFICIAL*|*REF-DIFFERS*) rs=FAIL;; *) rs=PASS;; esac
  echo "RESULT defs-$c official=$o kcompare=$k C3=$c3 C4=$c4 $rs"
done < "$W/cases.tsv"
# names case: config theorem_names ["main-thm"] (not a plain identifier: Lean's String.toName -> .anonymous) on exports that
# contain «main-thm»: official REJECTS; check B must not accept (n0) - before the name check it accepted
NT="Quot Quot.mk Quot.lift Quot.ind «main-thm» propext Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
TARGETS=$NT bexp "$W/n-chal" Challenge; TARGETS=$NT bexp "$W/n-sol" Solution
printf '{"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["main-thm"], "permitted_axioms": ["propext", "Quot.sound"]}\n' > "$W/names.json"
n=$((n+1))
if [ "$(cat "$W/n-chal/export.rc")" = 0 ] && [ "$(cat "$W/n-sol/export.rc")" = 0 ]; then
  bash "$ROOT/check/official/check.sh" "$W/n-sol/out.export" "$W/n-chal/out.export" "$W/names.json" --json "$W/n-off.json" > /dev/null 2>&1 < /dev/null
  o=$(vb "$W/n-off.json")
  bash "$ROOT/check/checkB/check-b.sh" "$W/n-sol/out.export" "$W/n-chal/out.export" "$W/names.json" --threads 4 --json "$W/n-c3.json" > /dev/null 2>&1 < /dev/null
  c3=$(vb "$W/n-c3.json")
  bash "$ROOT/check/checkB/check-b.sh" "$W/n-sol/out.export" "$W/n-chal/out.export" "$W/names.json" --threads 4 --single --json "$W/n-c4.json" > /dev/null 2>&1 < /dev/null
  c4=$(vb "$W/n-c4.json")
  if [ "$o" = 1 ] && [ "$c3" != 0 ] && [ "$c4" != 0 ]; then rs=PASS; else rs=FAIL; fails=$((fails+1)); fi
  printf 'names-unescaped\t1\t%s\t-\t-\t%s\t%s\tn0:%s\n' "$o" "$c3" "$c4" "$rs"
  echo "RESULT defs-names-unescaped official=$o C3=$c3 C4=$c4 (must not be 0) $rs"
else
  echo "RESULT defs-names-unescaped build-failed FAIL"; fails=$((fails+1))
fi
echo "RESULT defs: $n cases, $fails failing (status = kcompare/C3/C4 vs the official comparator)"
[ $fails = 0 ]
}
main "$@"; exit $?

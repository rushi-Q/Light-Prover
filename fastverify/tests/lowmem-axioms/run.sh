#!/bin/bash
# tests/lowmem-axioms/run.sh [FV_ROOT]: the axiom check and the comparison of the
# LOW-MEMORY sound check (check/lowmem/check-sound-lowmem.sh leg 1 = ccmp-lowmem: LowMemParse's fast-record pass-1 DAG +
# lowmem_arena.c's BFS, pass-2 selective materialization) and of the main sound check, on REAL official exports.
# Why: mutation testing found ccmp-lowmem mutants that no corpus kills (cmpx, self-test, the kernel-cves cases, the definition hole,
# 864 xfuzz variants, tests/lowmem-check): LMLowMemParse-0279 (LowMemParse.lean:460, the forall/lambda BODY edge of the pass-1
# DAG read from the wrong record field) makes the axiom BFS miss every constant that occurs only under a binder, and the FULL
# check-sound-lowmem.sh then ACCEPTS a solution whose proof reaches `sorry` inside a lambda body (the cmpx/self-test cases put
# the illegal axiom outside any binder); LMLowMemParse-0221..0225 (opaque declarations not kept / values dropped in pass 2)
# change verdicts only on exports with opaque constants, which no corpus compares.
# Cases (all exports built HERE with the official Lean 4.36 toolchain + its bundled leanexport, the comparator's targets;
# challenge = F.export, configuration = all theorems of F (or the single theorem `umb` whose statement mentions all of them):
#   F1, F1u, F2, F2u, F3            honest (structures/deriving, mutual + nested inductives, quotients, opaque, private names,
#                                   big literals, unicode strings, wf recursion, omega/simp/decide proofs, Std maps) -> ACCEPTED
#   F1-sorry-under-binder           F1 with `ack_test`'s proof reaching `sorry` inside a match arm (lambda body) -> REJECTED
#   F1-native                       F1 with one proof `by native_decide` (Lean.ofReduceBool) -> REJECTED
#   F1-sorry-in-let-value/-body/-type, F1-sorry-under-proj
#                                   `sorry` only in a let value / let body / let type annotation / the structure argument of a
#                                   raw projection (src/vp builds the Expr.proj with a 4-line term elaborator) -> REJECTED
#   (kill: LMLowMemParse-0279 lambda body, 0444/0445 let body, 0448/0449 let type, 0451 let value, 0468 proj struct - each
#    reads that edge of the pass-1 DAG from the wrong record field and the low-memory judges ACCEPT the matching case)
# each through check/lowmem/check-sound-lowmem.sh, check-sound-ultralowmem.sh (same leg 1) AND check/sound/check-sound.sh
# (exit + verdict). PASS iff all as expected.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${1:-$(cd "$H/../.." && pwd)}
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
W=$(mktemp -d "${TMPDIR:-/tmp}/lowmem-axioms.XXXXXX"); trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
pass=0; fail=0
B="Quot Quot.mk Quot.lift Quot.ind"; AX="propext Quot.sound Classical.choice"
PR="Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
thms() { grep -oP '^theorem \K\S+' "$1" | tr '\n' ' '; }
mkexp() {  # mkexp DIR MODULE TARGET_THEOREMS : official build + official export
  ( cd "$1" && env -i PATH="$TC/bin:/usr/bin:/bin" HOME="$W" lean -o "$2.olean" "$2.lean" > build.log 2>&1 \
    && env -i PATH="$TC/bin:/usr/bin:/bin" HOME="$W" LEAN_PATH="$TC/lib/lean:." LEAN_ABORT_ON_PANIC=1 leanexport "$2" -- $B $3 $AX $PR > "$2.export" 2> export.log )
}
cfg() {  # cfg OUT THEOREMS...
  local o=$1; shift
  python3 -I -c 'import json,sys; json.dump({"challenge_module": "Challenge", "solution_module": "Main", "theorem_names": sys.argv[2:],
    "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, open(sys.argv[1], "w"), indent=1)' "$o" "$@"
}
for m in F1 F2 F3; do mkdir -p "$W/$m"; cp "$H/src/$m.lean" "$W/$m/"; mkexp "$W/$m" "$m" "$(thms "$H/src/$m.lean")" || { echo "FAIL build $m: $(tail -3 "$W/$m/build.log" "$W/$m/export.log" | tr '\n' ' ')"; fail=$((fail+1)); }; done
for v in vs vn vl vb vt vp; do mkdir -p "$W/$v"; cp "$H/src/$v/F1.lean" "$W/$v/"; mkexp "$W/$v" F1 "$(thms "$H/src/F1.lean")" || { echo "FAIL build $v: $(tail -3 "$W/$v/build.log" | tr '\n' ' ')"; fail=$((fail+1)); }; done
cfg "$W/F1.json" $(thms "$H/src/F1.lean"); cfg "$W/F1u.json" umb; cfg "$W/F2.json" $(thms "$H/src/F2.lean"); cfg "$W/F2u.json" umb; cfg "$W/F3.json" $(thms "$H/src/F3.lean")
judge() {  # judge LABEL SCRIPT SOLUTION CHALLENGE CONFIG WANT_EXIT WANT_VERDICT [WANT_REASON_SUBSTRING]
  local l=$1 js=$2 s=$3 c=$4 g=$5 we=$6 wv=$7 wr=${8:-}
  "$js" "$s" "$c" "$g" --threads 8 --json "$W/$l.json" > "$W/$l.out" 2>&1; local rc=$?
  local v; v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); t=json.dumps(r); print(r.get("verdict"), int(sys.argv[2] in t))' "$W/$l.json" "$wr" 2>/dev/null)
  set -- $v
  if [ "$rc" = "$we" ] && [ "${1:-}" = "$wv" ] && [ "${2:-}" = 1 ]; then echo "PASS $l: exit $rc $1"; pass=$((pass+1))
  else echo "FAIL $l: expected exit $we $wv ${wr:+(~ '$wr')}, got exit $rc '$v' :: $(tail -1 "$W/$l.out" | cut -c1-200)"; fail=$((fail+1)); fi
}
export TMPDIR=$W
for J in lowmem:"$FV/check/lowmem/check-sound-lowmem.sh" ultralowmem:"$FV/check/lowmem/check-sound-ultralowmem.sh" sound:"$FV/check/sound/check-sound.sh"; do
  n=${J%%:*}; js=${J#*:}
  judge "$n-F1" "$js" "$W/F1/F1.export" "$W/F1/F1.export" "$W/F1.json" 0 ACCEPTED
  judge "$n-F1u" "$js" "$W/F1/F1.export" "$W/F1/F1.export" "$W/F1u.json" 0 ACCEPTED
  judge "$n-F2" "$js" "$W/F2/F2.export" "$W/F2/F2.export" "$W/F2.json" 0 ACCEPTED
  judge "$n-F2u" "$js" "$W/F2/F2.export" "$W/F2/F2.export" "$W/F2u.json" 0 ACCEPTED
  judge "$n-F3" "$js" "$W/F3/F3.export" "$W/F3/F3.export" "$W/F3.json" 0 ACCEPTED
  judge "$n-F1-sorry-under-binder" "$js" "$W/vs/F1.export" "$W/F1/F1.export" "$W/F1.json" 1 REJECTED sorryAx
  judge "$n-F1-native" "$js" "$W/vn/F1.export" "$W/F1/F1.export" "$W/F1.json" 1 REJECTED native_decide
  judge "$n-F1-sorry-in-let-value" "$js" "$W/vl/F1.export" "$W/F1/F1.export" "$W/F1.json" 1 REJECTED sorryAx
  judge "$n-F1-sorry-in-let-body" "$js" "$W/vb/F1.export" "$W/F1/F1.export" "$W/F1.json" 1 REJECTED sorryAx
  judge "$n-F1-sorry-in-let-type" "$js" "$W/vt/F1.export" "$W/F1/F1.export" "$W/F1.json" 1 REJECTED sorryAx
  judge "$n-F1-sorry-under-proj" "$js" "$W/vp/F1.export" "$W/F1/F1.export" "$W/F1.json" 1 REJECTED sorryAx
done
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]

#!/bin/bash
# tests/incr-reverify/run.sh [WORKDIR]  (kind: component, sound mode; ~3 min on one host, no Mathlib)
# Regression test of tools/incr (incremental re-verification after edits; untrusted build reuse + the trusted check):
#   base runs: x/tiny (Tiny.A <- Tiny.B <- Solution), x/tinymod (the same as Lean module-system files) and x/tiny2 (def tinyD <- theorem tinyB by simp [tinyD] <- Solution)
#   through bin/fastverify --preset sound (without merge) --keep-work; then tools/incr/incr-reverify.sh on edits:
#   have-full      tiny: a valid proof edit in Tiny.A, full incremental rebuild (3 dirty)             -> ACCEPTED
#   have-opt       same edit, --optimistic --reuse-plan (only Tiny.A rebuilt, plan reused): ACCEPTED, 1 dirty, inexact
#                  (EXPERIMENTAL) -> confirmed by an exact second attempt                                 -> ACCEPTED
#   have-iface     same edit, --interface (Lake-like propagation; plain non-module files -> every importer: 3 dirty)    -> ACCEPTED
#   iface-mod      tinymod: the same proof edit in Tiny.A, --interface: Tiny.A's public .olean/.ir/.ir.sig are unchanged ->
#                  its importers keep their outputs (1 module rebuilt, like Lake); inexact -> confirmed exactly  -> ACCEPTED
#   have-warm      same, + --warm base export (warm pleanchecker_incr; the server re-checks 3 dirty)  -> ACCEPTED
#   sorry-opt      tiny: 'have ... := sorry' in Tiny.B, --optimistic                                  -> REJECTED (both attempts)
#   break-opt      tiny: an ill-typed 'have' in Tiny.B                                                -> build fails (exit 1)
#   poison         tiny: Solution.lean rewrites Tiny/A.olean of its own incremental tree in place at elaboration time
#                  -> the base tree's Tiny/A.olean must keep its bytes (default copy mode = reflink/full copy)
#   kbad-warm      tiny: Tiny.B gains `v05bad : 2 + 2 = 5 := by decide +kernel` (passes the skip-kernel-tc build) and foo is
#                  proved from it; optimistic + WARM server: the fresh kernel-invalid constant must make the check REJECT
#   crash          a corrupt base plan makes incr-build.py raise -> must be exit 2 (no verdict), never 1
#   stale-opt      tiny2: tinyD := 3 (a definition's value changes; the stale importer used its unfolding), --optimistic
#                  -> attempt 1 (stale tinyB) REJECTED by the official-kernel leg, attempt 2 (importers rebuilt) ACCEPTED
#   cold-*         the DEFAULT path: incr-reverify = the cold sound path; exit + verdict equal bin/fastverify's on
#                  the same tree (have / sorry / break / kbad), summary mode "cold", incremental options ignored
# every row above the cold-* rows runs with --experimental-incremental (the machinery is EXPERIMENTAL, never counted).
# Prints 'PASS|FAIL case detail' rows and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/incr-reverify-work.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"; fails=0; T=${EVAL_THREADS:-8}
row() { echo "$1 $2: $3"; [ "$1" = PASS ] || fails=$((fails+1)); }
# incr-reverify.sh takes the official 4.33.1 toolchain from INCR_TC (default $HOME/.elan/...): give it the one this
# package registered (config/components.json), so the rows do not depend on HOME
[ -n "${INCR_TC:-}" ] || INCR_TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
[ -n "${INCR_TC:-}" ] && export INCR_TC
# the incremental rows run the EXPERIMENTAL machinery explicitly (where the package has the flag)
XINC=; grep -q -- '--experimental-incremental' "$FV/tools/incr/incr-reverify.sh" && XINC=--experimental-incremental
U="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,check-tail"
cp -r "$H/x/challenge" "$W/ch"
for p in tiny tinymod tiny2; do
  "$FV/bin/fastverify" "$H/x/$p" "$W/ch" "$W/base-$p" --preset sound --unsafe "$U" --threads "$T" --keep-work > "$W/base-$p.log" 2>&1
  rc=$?; [ $rc = 0 ] && row PASS "base-$p" ACCEPTED || row FAIL "base-$p" "exit $rc"
done
cp "$W/base-tiny/challenge.export" "$W/ch/"; CSHA=$(sha256sum "$W/ch/challenge.export" | cut -d' ' -f1)
# the caller's comparator pin (both pins required), where the incr-reverify under test takes it
CMPIN=; grep -q -- '--comparator-sha256' "$FV/tools/incr/incr-reverify.sh" && CMPIN="--comparator-sha256 $(sha256sum < "$W/ch/comparator.json" | cut -c1-64)"
mk() { python3 -I "$FV/tools/incr/mk-edit.py" "$H/x/$1" "$W/e-$2" "$3" "$4" > /dev/null; }
mk tiny have Tiny.A have; mk tinymod hmod Tiny.A have; mk tiny sorry Tiny.B sorry; mk tiny brk Tiny.B break
cp -r "$H/x/tiny2" "$W/e-stale"; echo 'def tinyD : Nat := 3' > "$W/e-stale/Tiny/A.lean"
run() {  # run CASE BASE EDIT WANT_EXIT CHECK_PY [ARGS] - the EXPERIMENTAL incremental machinery (behind
  # --experimental-incremental; its ACCEPTED is reported as NO VERDICT + "provisional": "ACCEPTED", which counts here as the
  # machinery's own exit 0 - the rows test the machinery, not a counted verdict)
  local c=$1 b=$2 e=$3 want=$4 py=$5; shift 5
  "$FV/tools/incr/incr-reverify.sh" "$W/base-$b" "$W/e-$e" "$W/ch" "$W/o-$c" --challenge-sha256 "$CSHA" $CMPIN --threads "$T" "$@" \
    $XINC > "$W/o-$c.log" 2>&1; local rc=$?
  [ "$rc" = 2 ] && [ -n "$XINC" ] && grep -q '"provisional": "ACCEPTED"' "$W/o-$c/summary.json" 2>/dev/null && rc=0
  [ "$rc" = 2 ] && [ -n "$XINC" ] && grep -q '"provisional": "REJECTED"' "$W/o-$c/summary.json" 2>/dev/null && rc=1
  local ok; ok=$(python3 -I -c "import json,sys; r=json.load(open(sys.argv[1])); a=r['attempts']; print('yes' if ($py) else 'no')" \
    "$W/o-$c/summary.json" 2>/dev/null)
  if [ "$rc" = "$want" ] && { [ "$ok" = yes ] || [ "$py" = - ]; }; then row PASS "$c" "exit $rc"; else row FAIL "$c" "exit $rc (want $want), check=$ok"; fi
}
run have-full tiny have 0 "a[0]['dirty']==3 and a[0]['check']['verdict']=='ACCEPTED'"
run have-opt tiny have 0 "a[0]['dirty']==1 and a[0]['optimistic'] and a[0]['plan_reused'] and len(a)==2 and a[0].get('exact') is False and a[1].get('exact') is True" --optimistic --reuse-plan
run have-iface tiny have 0 "a[0]['dirty']==3 and a[0].get('interface_waves',0)>=1 and a[0]['check']['verdict']=='ACCEPTED'" --interface --reuse-plan
run iface-mod tinymod hmod 0 "a[0]['dirty']==1 and a[0].get('dirty_full')==3 and a[0].get('interface_waves')==1 and a[0]['check']['verdict']=='ACCEPTED' and len(a)==2 and a[1].get('exact') is True" --interface --reuse-plan
run have-warm tiny have 0 "r['warm'] and any('3 dirty re-checked' in l for l in r.get('server_tail',[]))" --optimistic --reuse-plan --warm "$W/base-tiny/solution.export"
run sorry-opt tiny sorry 1 "len(a)==2 and all('sorryAx' in x['check'].get('reason','') for x in a)" --optimistic --reuse-plan
run break-opt tiny brk 1 - --optimistic --reuse-plan
cp -r "$H/x/tiny" "$W/e-poison"; cp "$H/x/poison/Solution.lean" "$W/e-poison/Solution.lean"
B0=$(sha256sum "$W/base-tiny/work/proj/.lake/build/lib/lean/Tiny/A.olean" | cut -c1-16)
"$FV/tools/incr/incr-reverify.sh" "$W/base-tiny" "$W/e-poison" "$W/ch" "$W/o-poison" --challenge-sha256 "$CSHA" $CMPIN --threads "$T" $XINC > "$W/o-poison.log" 2>&1
B1=$(sha256sum "$W/base-tiny/work/proj/.lake/build/lib/lean/Tiny/A.olean" | cut -c1-16)
[ "$B0" = "$B1" ] && row PASS poison "base Tiny/A.olean unchanged ($B0)" || row FAIL poison "base Tiny/A.olean changed $B0 -> $B1"
cp -r "$H/x/tiny" "$W/e-kbad"; cp "$H/x/kbad/Tiny/B.lean" "$W/e-kbad/Tiny/B.lean"; cp "$H/x/kbad/Solution.lean" "$W/e-kbad/Solution.lean"
run kbad-warm tiny kbad 1 "a[-1]['check']['verdict']=='REJECTED'" --optimistic --reuse-plan --warm "$W/base-tiny/solution.export"
cp -a "$W/base-tiny" "$W/base-bad" && echo '{"garbage": ' > "$W/base-bad/log/build-fast/plan.jsonl"
"$FV/tools/incr/incr-reverify.sh" "$W/base-bad" "$W/e-have" "$W/ch" "$W/o-crash" --challenge-sha256 "$CSHA" $CMPIN --threads "$T" $XINC > "$W/o-crash.log" 2>&1
rc=$?; [ $rc = 2 ] && row PASS crash "exit 2 (no verdict)" || row FAIL crash "exit $rc (want 2)"
run stale-opt tiny2 stale 0 "len(a)==2 and a[0]['check']['verdict']=='REJECTED' and a[1]['check']['verdict']=='ACCEPTED'" --optimistic --reuse-plan
# the DEFAULT path is the cold sound path: incr-reverify answers exactly as bin/fastverify --preset sound on NEW
cold() {  # cold CASE EDIT : default incr-reverify vs bin/fastverify on the same tree (exit + verdict equal, mode cold)
  local c=$1 e=$2
  "$FV/tools/incr/incr-reverify.sh" "$W/base-tiny" "$W/e-$e" "$W/ch" "$W/oc-$c" --challenge-sha256 "$CSHA" $CMPIN --threads "$T" --optimistic \
    > "$W/oc-$c.log" 2>&1; local rc=$?
  "$FV/bin/fastverify" "$W/e-$e" "$W/ch" "$W/fc-$c" --preset sound --threads "$T" --challenge-sha256 "$CSHA" --export-dir none \
    --comparator-sha256 "$(sha256sum < "$W/ch/comparator.json" | cut -c1-64)" \
    > "$W/fc-$c.log" 2>&1; local frc=$?
  local v fv; v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["verdict"], r["mode"])' "$W/oc-$c/summary.json" 2>/dev/null)
  fv=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$W/fc-$c/result.json" 2>/dev/null)
  [ "$rc" = "$frc" ] && [ "$v" = "$fv cold" ] && row PASS "$c" "exit $rc, $v = bin/fastverify $fv" || row FAIL "$c" "exit $rc '$v' vs bin/fastverify exit $frc '$fv'"
}
cold cold-have have
cold cold-sorry sorry
cold cold-break brk
cold cold-kbad kbad
for d in "$W"/base-*; do E=$(readlink -f "$d/solution.export"); case "$E" in /dev/shm/fastverify-export.*) rm -rf "$(dirname "$E")";; esac; done
[ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"
echo "RESULT $([ $fails = 0 ] && echo PASS || echo FAIL) fails=$fails"
[ $fails = 0 ]

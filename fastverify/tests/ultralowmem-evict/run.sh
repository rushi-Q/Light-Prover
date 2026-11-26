#!/bin/bash
# tests/ultralowmem-evict/run.sh [FASTVERIFY_ROOT]  -- regression test: the ultra-low-
# memory judge (check/lowmem/check-sound-ultralowmem.sh; Lean leg pleanchecker_lowmem --low-mem --evict=smart,
# check/lowmem/src-ultralowmem/.../PChk/LowMem.lean) falsely REJECTED a valid official Lean 4.36.0 export: the targeted
# pin-set retry did not follow recursor rules / inductive ctors, so the theorem the kernel must unfold (Demo.lem, reached
# through Demo.Box.rec -> Demo.Box.mk : Box Demo.f -> Demo.f := Acc.rec .. Demo.lem) was never pinned and the empty pin set
# was taken for a fixed point ("genuine kernel rejection"). Fails on the earlier binary (e60fa011), passes with the fixed one.
# Inputs (data/, SHA256SUMS): the false-reject case (challenge,
# solution = official v4.36.0 leanexport of a kernel-checked olean, comparator.json, the Lean sources) + solution_bad.export
# (Demo.helper's value replaced by expr 286 = @Eq.refl Nat 42, a GENUINE type error: the official leanchecker rejects
# it) to show that a genuine kernel rejection on the same retry path is still REJECTED.
# Reference rows (official Lean 4.36 leanchecker, when present): solution.export rc 0, solution_bad.export rc 1.
# chain rows: chain_good / chain_bad = a chain of 11 theorems (ChainBase.lean:
# Chain.f := Acc.rec .. lem10, lem10 := lem9 ... lem0; Chain.t : f = 42 / f = 43, the bad one added with skipKernelTC;
# build_chain_olean.lean), exported with the official 4.36 leanexport (`leanexport Chain -- Chain.t`: Chain.t and its closure).
# The smart retry needs more than 6 iterations (pin set 22 -> 47 -> ... -> 131), so the complete-closure pass decides:
# chain_good ACCEPTED, chain_bad REJECTED (official 4.36: rc 0 / rc 1). They run with the binary d27c3bdd - the pinned
# pleanchecker_lowmem when it is d27c3bdd, else a locally installed copy of it - and are SKIPPED (with a
# message) when neither is present. Note: tests/lowmem-check does not run pleanchecker_lowmem at all.
set -u
FV=$(readlink -f "${1:-$(dirname "$(readlink -f "$0")")/../..}")
D=$(cd "$(dirname "$(readlink -f "$0")")/data" && pwd)
( cd "$D" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL inputs: data/SHA256SUMS"; echo "RESULT pass=0 fail=1"; exit 1; }
WB=; for d in ${F2_TEST_WORKDIR:-} /scratch /var/tmp; do [ -d "$d" ] && [ -w "$d" ] && { WB=$d; break; }; done
W=$(mktemp -d "${WB:-/tmp}/f2-ulm-evict.XXXXXX"); trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1"; pass=$((pass+1)); }
no() { echo "FAIL $1: $2"; fail=$((fail+1)); }
PLM=$(awk '$1=="PIN" && $2=="pleanchecker_lowmem" {print $4}' "$FV/check/lowmem/pins-ultralowmem.env")
TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
judge() {  # judge NAME WANT_RC WANT_VERDICT SCRIPT EXPORT
  local n=$1 wrc=$2 wv=$3 s=$4 e=$5
  "$s" "$e" "$D/challenge.export" "$D/comparator.json" --threads 4 --workdir "$W" > "$W/j.out" 2> "$W/j.err"; local rc=$?
  local v; v=$(tail -n 1 "$W/j.out" | /usr/bin/python3 -I -c 'import json,sys
try: d=json.loads(sys.stdin.read()); print(d.get("verdict"), "|", str(d.get("reason"))[:160])
except Exception: print("BADJSON |")')
  if [ "$rc" = "$wrc" ] && [ "${v%% |*}" = "$wv" ]; then ok "$n"; else no "$n" "rc=$rc $v (want $wrc $wv)"; fi
}
leg() {  # leg NAME EVICT EXPORT WANT_RC WANT_REGEX : the Lean leg ALONE (as check-sound-ultralowmem.sh runs it)
  local n=$1 ev=$2 e=$3 wrc=$4 re=$5
  [ -x "$PLM" ] || { no "$n" "pinned pleanchecker_lowmem $PLM missing"; return; }
  LEAN_ABORT_ON_PANIC=1 LEAN_STACK_SIZE_KB=917376 "$PLM" -j4 -v --low-mem "--evict=$ev" --from-export "$e" > "$W/l.out" 2>&1; local rc=$?
  if [ "$rc" = "$wrc" ] && grep -qE "$re" "$W/l.out"; then ok "$n"
  else no "$n" "rc=$rc (want $wrc /$re/): $(grep -E 'pchk-lowmem\]|kernel (accepts|rejects)' "$W/l.out" | tail -n 3 | tr '\n' ' ')"; fi
}
# pin-aware: the expectation follows the ACTIVE PIN pleanchecker_lowmem; with the v0.1 pin e60fa011 the unfold rows
# expect its documented false REJECT ("known v0.1 limitation", check/lowmem/README.md);
# with any other pin the official ACCEPT. No row expects an ACCEPT where the official checker rejects, under any pin.
PLMSHA=$(awk '$1=="PIN" && $2=="pleanchecker_lowmem" {print $3}' "$FV/check/lowmem/pins-ultralowmem.env")
E60=e60fa01170048fb1197d923c09487963c5659214043873de282aaa74e133a9ae
echo "INFO active pin pleanchecker_lowmem ${PLMSHA:0:16}"
if [ "$PLMSHA" = "$E60" ]; then
  LIM="[e60fa011: false REJECTED (the smart retry's pin set misses the theorem the kernel must unfold); known v0.1 limitation, check/lowmem/README.md]"
  judge "unfold/check-sound-ultralowmem/valid $LIM" 1 REJECTED "$FV/check/lowmem/check-sound-ultralowmem.sh" "$D/solution.export"
  leg "unfold/leanleg-smart/valid $LIM" smart "$D/solution.export" 1 '^Lean default kernel rejects the solution'
else
  judge unfold/check-sound-ultralowmem/valid 0 ACCEPTED "$FV/check/lowmem/check-sound-ultralowmem.sh" "$D/solution.export"
  leg unfold/leanleg-smart/valid smart "$D/solution.export" 0 '^Lean default kernel accepts the solution$'
fi
leg unfold/leanleg-strict/valid-needs-unfolding strict "$D/solution.export" 1 'rejects the solution'   # control: the case needs theorem unfolding
judge unfold/check-sound-ultralowmem/genuine-error 1 REJECTED "$FV/check/lowmem/check-sound-ultralowmem.sh" "$D/solution_bad.export"
leg unfold/leanleg-smart/genuine-error smart "$D/solution_bad.export" 1 '^Lean default kernel rejects the solution'
leg unfold/leanleg-off/genuine-error off "$D/solution_bad.export" 1 '^Lean default kernel rejects the solution'
judge unfold/check-sound-lowmem/valid 0 ACCEPTED "$FV/check/lowmem/check-sound-lowmem.sh" "$D/solution.export"
judge unfold/check-sound/valid 0 ACCEPTED "$FV/check/sound/check-sound.sh" "$D/solution.export"
judge unfold/check-sound/genuine-error 1 REJECTED "$FV/check/sound/check-sound.sh" "$D/solution_bad.export"
# the chain exports with the PINNED binary (every pin gives the official outcome here)
leg chain/leanleg-smart/valid smart "$D/chain_good.ndjson" 0 '^Lean default kernel accepts the solution$'
leg chain/leanleg-smart/genuine-error smart "$D/chain_bad.ndjson" 1 '^Lean default kernel rejects the solution'
ALTSHA=d27c3bddaf31e1a402d67d92ae9ab21899a1b2a433652e836a51f0459b170a41; ALT=
for c in "$PLM" /scratch/fastverify-next/lowmem/d27c3bdd/pleanchecker-lowmem; do
  [ -x "$c" ] && [ "$(sha256sum < "$c" | cut -d' ' -f1)" = "$ALTSHA" ] && { ALT=$c; break; }; done
if [ -n "$ALT" ]; then
  altleg() {  # altleg NAME EXPORT WANT_RC WANT_REGEX : the d27c3bdd Lean leg alone, --evict=smart
    LEAN_ABORT_ON_PANIC=1 LEAN_STACK_SIZE_KB=917376 "$ALT" -j4 -v --low-mem --evict=smart --from-export "$2" > "$W/l.out" 2>&1; local rc=$?
    if [ "$rc" = "$3" ] && grep -qE "$4" "$W/l.out"; then ok "$1"
    else no "$1" "rc=$rc (want $3 /$4/): $(grep -E 'closure|kernel (accepts|rejects|could)' "$W/l.out" | tail -n 2 | tr '\n' ' ')"; fi
  }
  altleg closure-pass/chain-good-accepted "$D/chain_good.ndjson" 0 'ACCEPTED via the complete-closure pass'
  altleg closure-pass/chain-bad-rejected "$D/chain_bad.ndjson" 1 'complete-closure pass: genuine kernel rejection'
  altleg closure-pass/unfold-bad-rejected "$D/solution_bad.export" 1 'complete-closure pass: genuine kernel rejection'
else echo "SKIP closure-pass/*: pleanchecker-lowmem d27c3bdd is neither pinned nor deployed at /scratch/fastverify-next/lowmem/d27c3bdd/"; fi
if [ -x "$TC36/bin/leanchecker" ]; then
  for c in chain_good.ndjson:0 chain_bad.ndjson:1; do
    LEAN_ABORT_ON_PANIC=1 "$TC36/bin/leanchecker" --from-export "$D/${c%%:*}" > "$W/r.out" 2>&1; rc=$?
    [ "$rc" = "${c#*:}" ] && ok "ref/official-leanchecker-436/${c%%:*}" || no "ref/official-leanchecker-436/${c%%:*}" "rc=$rc"
  done
  for c in solution:0 solution_bad:1; do
    LEAN_ABORT_ON_PANIC=1 "$TC36/bin/leanchecker" --from-export "$D/${c%%:*}.export" > "$W/r.out" 2>&1; rc=$?
    [ "$rc" = "${c#*:}" ] && ok "ref/official-leanchecker-436/${c%%:*}" || no "ref/official-leanchecker-436/${c%%:*}" "rc=$rc"
  done
else echo "SKIP ref/*: official Lean 4.36 toolchain not found"; fi
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit $?

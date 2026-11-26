#!/bin/bash
# tests/ultralowmem-lean-leg/run.sh [FASTVERIFY_ROOT]  -- regression test of the ultra-low-memory
# Lean leg pleanchecker-lowmem (check/lowmem/src-ultralowmem/.../PChk/LowMem.lean). Inputs: crafted exports
# (sha256 in data/SHA256SUMS) + literal-bytes-late-ofList (String.ofList's record moved
# after the theorem). Rows that differ from the official 4.36 replay are POLICY rows (a v0.1 policy decision):
# the ultra-low-memory judge replays in dependency-correct
# file order with the literal-triggered implicit lookups (Nat, String.ofList, Char.ofNat) present before use, as S1(4)
# requires; it does not reproduce Lean.Replay's NameSet order. check-sound.sh (pleanchecker e0d4ae8b) does.
#   literal-bytes            official leanchecker 4.36 REJECTS (unknown constant String.ofList: NameSet-order artifact), 4.37
#                            ACCEPTS; the ultra-low-memory Lean leg ACCEPTS, check-sound.sh's Lean leg (pleanchecker e0d4ae8b)
#                            REJECTS like 4.36 (both recorded; the kernel legs are where the two judges differ)
#   literal-bytes-late-ofList the theorem precedes String.ofList in the file: the Lean leg defers it (deferred=1) and accepts
#                            (an earlier build checked it before String.ofList and rejected)
#   regrouped                A.rec exported in the group of B: official accepts; the leg goes to the official path, accepts
#   mixed-safety-group       a safe A.rec record inside the group of unsafe B: official accepts; official path, accepts
#   recursion-flag           empty inductive with isRec=true: official 4.36 accepts; C2 record veto REJECTS (documented
#                            veto, fail-closed: the standard judge rejects it too)
#   worker-error, sparse-expression: controls (accepted)
# Resource errors (no verdict instead of REJECTED) are covered by the fault-injection records of the ultra-low-memory leg
# (not shipped): they need a modified build.
# Further rows: mutual-lit-cycle-both (sha256 4492ebc2...); p-ctor-nocycle, p-ctor-early-ref-ok
# (official 4.36 rejects, 4.37 accepts).
# Also: string-type, mutual-literal, literal-cycle, nat-predicate
# (official 4.36 and 4.37 ACCEPT; an earlier build rejected), resource-named-bad, bvar-2p40-unused.
set -u
ulimit -c 0 2>/dev/null   # the bvar-2p40 rows abort by design (official panic); no core files
FV=$(readlink -f "${1:-$(dirname "$(readlink -f "$0")")/../..}")
D=$(cd "$(dirname "$(readlink -f "$0")")/data" && pwd)
( cd "$D" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL inputs: data/SHA256SUMS"; echo "RESULT pass=0 fail=1"; exit 1; }
WB=; for d in ${F2_TEST_WORKDIR:-} /scratch /var/tmp; do [ -d "$d" ] && [ -w "$d" ] && { WB=$d; break; }; done
W=$(mktemp -d "${WB:-/tmp}/ultralowmem-lean-leg.XXXXXX"); trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1"; pass=$((pass+1)); }
no() { echo "FAIL $1: $2"; fail=$((fail+1)); }
PLM=$(awk '$1=="PIN" && $2=="pleanchecker_lowmem" {print $4}' "$FV/check/lowmem/pins-ultralowmem.env")
TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
TC37=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.37.0-rc1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
leg() {  # leg NAME EXPORT EVICT WANT_RC WANT_REGEX : the Lean leg ALONE, as check-sound-ultralowmem.sh runs it
  local n=$1 e=$2 ev=$3 wrc=$4 re=$5
  [ -x "$PLM" ] || { no "$n" "pinned pleanchecker_lowmem $PLM missing"; return; }
  LEAN_ABORT_ON_PANIC=1 LEAN_STACK_SIZE_KB=917376 "$PLM" -j4 -v --low-mem "--evict=$ev" --from-export "$D/$e" > "$W/l.out" 2>&1; local rc=$?
  if [ "$rc" = "$wrc" ] && grep -qE "$re" "$W/l.out"; then ok "$n"
  else no "$n" "rc=$rc (want $wrc /$re/): $(grep -E 'deferred=|kernel' "$W/l.out" | tail -n 2 | tr '\n' ' ' | cut -c1-240)"; fi
}
# pin-aware: the rows below follow the ACTIVE PIN pleanchecker_lowmem of check/lowmem/pins-ultralowmem.env.
# With the v0.1 pin e60fa011 the rows for its DOCUMENTED limitations expect e60fa011's documented outcome and say so ("known
# v0.1 limitation", check/lowmem/README.md); with any other pin (07309da5, d27c3bdd, ...)
# they expect the official outcome. Hard rule, checked for every such row under every pin: no row may expect an ACCEPT where
# the official checker REJECTS (rc 1) - the test FAILS its own setup otherwise.
PLMSHA=$(awk '$1=="PIN" && $2=="pleanchecker_lowmem" {print $3}' "$FV/check/lowmem/pins-ultralowmem.env")
E60=e60fa01170048fb1197d923c09487963c5659214043873de282aaa74e133a9ae
PINMODE=official; [ "$PLMSHA" = "$E60" ] && PINMODE=e60fa011
echo "INFO active pin pleanchecker_lowmem ${PLMSHA:0:16} -> expectations: $PINMODE"
LIMDOC="known v0.1 limitation of e60fa011, check/lowmem/README.md"
lim() {  # lim NAME EXPORT EVICT OFFICIAL_RC OFFICIAL_REGEX E60_RC E60_REGEX WHY : leg() with the expectation of the active pin
  local n=$1 e=$2 ev=$3 orc=$4 ore=$5 erc=$6 ere=$7 why=$8
  if [ "$orc" = 1 ] && [ "$erc" = 0 ]; then no "$n" "TEST SETUP ERROR: the e60fa011 expectation would accept what the official checker rejects"; return; fi
  if [ "$PINMODE" = e60fa011 ]; then leg "$n [e60fa011: $why; $LIMDOC]" "$e" "$ev" "$erc" "$ere"
  else leg "$n" "$e" "$ev" "$orc" "$ore"; fi
}
ref() {  # ref NAME TOOLCHAIN EXPORT WANT_RC : official leanchecker --from-export (recorded oracle)
  local n=$1 tc=$2 e=$3 wrc=$4
  [ -x "$tc/bin/leanchecker" ] || { echo "SKIP $n: $tc/bin/leanchecker missing"; return; }
  LEAN_ABORT_ON_PANIC=1 "$tc/bin/leanchecker" --from-export "$D/$e" > "$W/r.out" 2>&1; local rc=$?
  [ "$rc" = "$wrc" ] && ok "$n (rc=$rc)" || no "$n" "rc=$rc (want $wrc): $(tail -c 160 "$W/r.out" | tr '\n' ' ')"
}
# literal-bytes: the policy difference, recorded on both judges and both official releases
ref ref/leanchecker-4.36/literal-bytes "$TC36" literal-bytes.ndjson 1
ref ref/leanchecker-4.37/literal-bytes "$TC37" literal-bytes.ndjson 0
leg leanleg/literal-bytes/smart literal-bytes.ndjson smart 0 '^Lean default kernel accepts the solution$'
leg leanleg/literal-bytes/off literal-bytes.ndjson off 0 '^Lean default kernel accepts the solution$'
# the standard judge's Lean leg (check/sound/pins.env PIN pleanchecker = e0d4ae8b, Lean.Replay order) rejects like 4.36.
# (Full-judge rows need a challenge export that contains the comparator's primitive targets; this one-theorem export does
# not, so both judges stop at leg 1 with 'Const not found in challenge' - the kernel legs are what differ.)
PLC=$(awk '$1=="PIN" && $2=="pleanchecker" {print $4}' "$FV/check/sound/pins.env")
LEAN_ABORT_ON_PANIC=1 LEAN_STACK_SIZE_KB=917376 "$PLC" -j4 --from-export "$D/literal-bytes.ndjson" > "$W/p.out" 2>&1; rc=$?
[ "$rc" = 1 ] && grep -q "unknown constant 'String.ofList'" "$W/p.out" && ok "check-sound-leanleg/literal-bytes REJECTED like 4.36 (rc=1)" \
  || no "check-sound-leanleg/literal-bytes" "rc=$rc: $(tail -c 160 "$W/p.out" | tr '\n' ' ')"
# implicit dependency later in the file: deferred, never checked without String.ofList
ref ref/leanchecker-4.36/literal-bytes-late-ofList "$TC36" literal-bytes-late-ofList.ndjson 1
lim leanleg/literal-bytes-late-ofList/deferred literal-bytes-late-ofList.ndjson smart 0 'deferred=1 .*' 1 "unknown constant 'String.ofList'" "REJECTED like official 4.36 (no deferral; 4.37 and the fixed build accept)"
lim leanleg/literal-bytes-late-ofList/accepted literal-bytes-late-ofList.ndjson smart 0 '^Lean default kernel accepts the solution$' 1 '^Lean default kernel rejects the solution' "REJECTED like official 4.36"
# inductive groups with foreign-owner / mixed-safety records: official path (= official verdict)
for f in regrouped mixed-safety-group; do
  ref "ref/leanchecker-4.36/$f" "$TC36" "$f.ndjson" 0
  lim "leanleg/$f/smart" "$f.ndjson" smart 0 'falling back to official LeanExport.parseStream' 1 '^Lean default kernel rejects the solution' "false REJECTED (foreign-owner / mixed-safety inductive group)"
  lim "leanleg/$f/off" "$f.ndjson" off 0 '^Lean default kernel accepts the solution$' 1 '^Lean default kernel rejects the solution' "false REJECTED (foreign-owner / mixed-safety inductive group)"
done
# the C2 record veto (documented, fail-closed): official 4.36 accepts, the Lean leg rejects
ref ref/leanchecker-4.36/recursion-flag "$TC36" recursion-flag.ndjson 0
leg leanleg/recursion-flag/record-veto recursion-flag.ndjson smart 1 "Export record of A differs from the kernel's constant"
# ---------- literal dependencies, resource-named theorem, unused bvar ----------
# three false rejects + nat-predicate: the kernel's own lookups (string literal -> String, "" needs no Char.ofNat,
# literal dependencies of every type of a deferred mutual block, Nat.beq/Nat.ble -> Bool.true/Bool.false) are now exact
# dependencies with a cycle-free deferred order; both official releases accept all four, so does the Lean leg (every mode)
for f in string-type mutual-literal literal-cycle nat-predicate; do
  ref "ref/leanchecker-4.36/$f" "$TC36" "$f.ndjson" 0
  ref "ref/leanchecker-4.37/$f" "$TC37" "$f.ndjson" 0
  case $f in
    literal-cycle) for m in smart off strict; do leg "leanleg/literal-deps/$f/$m" "$f.ndjson" $m 0 '^Lean default kernel accepts the solution$'; done;;   # every pin accepts
    *) for m in smart off strict; do lim "leanleg/literal-deps/$f/$m" "$f.ndjson" $m 0 '^Lean default kernel accepts the solution$' 1 '^Lean default kernel rejects the solution' "false REJECTED (literal-triggered kernel lookup not a dependency)"; done;;
  esac
done
# the no-verdict decision comes from the kernel exception, not from text: an ill-typed theorem NAMED like a
# resource message is a plain rejection (an earlier build gave rc 2 "could not decide"); official 4.36 rejects it too
ref ref/leanchecker-4.36/resource-named-bad "$TC36" resource-named-bad.ndjson 1
for m in smart off strict; do leg "leanleg/literal-deps/resource-named-bad/$m" resource-named-bad.ndjson $m 1 '^Lean default kernel rejects the solution'; done
# an unused bvar index 2^40 makes the official reader panic; the Lean leg's fast path declines it and the
# official path gives the official behaviour (panic, exit 134 -> the judge has no verdict); an earlier build accepted
ref ref/leanchecker-4.36/bvar-2p40-unused "$TC36" bvar-2p40-unused.ndjson 134
# bvar-2p40-unused: the official tools PANIC (no verdict) on this unused, malformed expression record; every declaration of the
# export is valid, so this is not "accepting what official rejects": the fixed builds decline to the official path (= the same
# panic, exit 134 -> the judge has no verdict); e60fa011's Lean leg ACCEPTS it (documented INFO item of the v0.1 release state)
for m in smart off; do lim "leanleg/literal-deps/bvar-2p40-unused/$m" bvar-2p40-unused.ndjson $m 134 'too many bound variables' 0 '^Lean default kernel accepts the solution$' "Lean leg ACCEPTS an unused bvar index above 2^20 where the official tools panic (no official verdict)"; done
# a deferred mutual block whose sibling depends on a declaration with an unused literal
# whose expansion helper mentions the block - the block's members must stay pending until the block is added (e6f80235
# REJECTED with 'unknown constant Left'); both official releases accept
f=mutual-lit-cycle-both
ref "ref/leanchecker-4.36/$f" "$TC36" "$f.ndjson" 0
ref "ref/leanchecker-4.37/$f" "$TC37" "$f.ndjson" 0
for m in smart off strict; do leg "leanleg/mutual-order/$f/$m" "$f.ndjson" $m 0 '^Lean default kernel accepts the solution$'; done
# INFO: official 4.36 rejects valid mutual blocks whose sibling / constructor type mentions a later
# definition (Lean.Replay starts from one member); 4.37 and the Lean leg accept (dependency-correct order, S1(4))
for f in p-ctor-nocycle p-ctor-early-ref-ok; do
  ref "ref/leanchecker-4.36/$f" "$TC36" "$f.ndjson" 1
  ref "ref/leanchecker-4.37/$f" "$TC37" "$f.ndjson" 0
  for m in smart off strict; do leg "leanleg/mutual-order/$f/$m" "$f.ndjson" $m 0 '^Lean default kernel accepts the solution$'; done
done
# controls
for f in worker-error sparse-expression; do
  ref "ref/leanchecker-4.36/$f" "$TC36" "$f.ndjson" 0
  leg "leanleg/$f/smart" "$f.ndjson" smart 0 '^Lean default kernel accepts the solution$'
done
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit $?

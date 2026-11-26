#!/bin/bash
# tests/frontier-conditional/test.sh - regression test of the CONDITIONAL check modulo a sorry frontier (check/frontier/check-frontier.sh
# + tools/frontier: the redirect construction, the wrapper and the fast preparer).    test.sh [--quick] [WORKDIR]   (~2-3 min, no Mathlib)
# (scan rows show the preparer's raw view: Prop-sorries inside a target / definition are listed as blockers there; the
#  end-to-end path then ABSTRACTS them into open lemmas closed over their local context: sketch / letsketch / auxproof /
#  wfsorry are CONDITIONAL; data sorries (defsorry, stmtsorry) stay REJECTED; a subgoal whose statement IS the
#  target's type modulo metadata and lets ("T follows from T": wholesorry, idsorry, and targetsorry, whose final `sorry`
#  after a `have` has exactly the target statement) is never abstracted: REJECTED.)
# Builds the Init-only cases in cases/ with the OFFICIAL Lean 4.36 toolchain and its bundled exporter (the comparator's export
# targets), then
#   (1) scan rows: the untrusted fast preparer's frontier / blockers per case (fvfrontier-prep scan) and the Python preparer
#       (FRONTIER_NO_FAST=1) giving the same frontier;
#   (2) e2e rows: check-frontier.sh verdict + exit code per case (0 ACCEPTED, 3 CONDITIONAL, 1 REJECTED, 2 no verdict);
#   (3) wiring rows with LYING preparers (a package copy whose tools/frontier/frontier.py tampers with its outputs): a
#       forged frontier challenge (C' := S') -> never CONDITIONAL; a target listed as frontier -> no verdict; a
#       preparation that drops a frontier lemma -> REJECTED; a preparation that writes permissive configs -> ignored.
#   (4) ledger rows: tools/frontier/ledger.py diff/gate with check-frontier.sh --base (proved / dropped / drift).
# Every row: 'PASS|FAIL <case>: ...'; last line 'RESULT pass=N fail=M'; exit 0 iff all PASS.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=$(cd "$HERE/../.." && pwd)
QUICK=0; [ "${1:-}" = --quick ] && { QUICK=1; shift; }
PREP=$(awk '$1=="PIN" && $2=="fvfrontier_prep" {print $4}' "$PKG/check/frontier/pins.env")
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$PKG/config/components.json")
W=${1:-$(mktemp -d "${SCRATCH:-${TMPDIR:-/tmp}}/frontier-conditional-test.XXXXXX")}; mkdir -p "$W"
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
TARGETS="Quot Quot.mk Quot.lift Quot.ind target1 propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
mkexp() {  # mkexp DIR MODULE : official build + official export (the comparator's targets) of DIR/MODULE.lean
  ( cd "$1" && PATH=$TC/bin:/usr/bin:/bin lean -o "$2.olean" "$2.lean" > build.log 2>&1 \
    && PATH=$TC/bin:/usr/bin:/bin LEAN_PATH=$TC/lib/lean:. LEAN_ABORT_ON_PANIC=1 leanexport "$2" -- $TARGETS > "$2.export" 2> export.log )
}
CFG=$W/comparator.json
printf '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":["target1"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}' > "$CFG"
mkdir -p "$W/challenge"; cp "$HERE/cases/Challenge.lean" "$W/challenge/"; mkexp "$W/challenge" Challenge || { ko setup "challenge build/export failed"; echo "RESULT pass=$pass fail=$fail"; exit 1; }
CHAL=$W/challenge/Challenge.export
# case | frontier | sorry in targets | sorry in definitions | other axioms | e2e exit | e2e verdict
CASES="decomp helperA,helperB - - - 3 CONDITIONAL
nosorry - - - - 0 ACCEPTED
partial helperA,helperB - - - 3 CONDITIONAL
havesorry helperA,helperB - - - 3 CONDITIONAL
defsorry helperA,helperB - myBound2 - 1 REJECTED
targetsorry helperA target1 - - 1 REJECTED
stmtsorry helperA target1 - - 1 REJECTED
extraaxiom helperB - - myAx 1 REJECTED
stmtchanged helperA,helperB - - - 1 REJECTED
instsorry helperB,smallInst - - - 3 CONDITIONAL
auxproof helperB - pos - 3 CONDITIONAL
univpoly helperB,helperU - - - 3 CONDITIONAL
nested helperB,helperC - - - 3 CONDITIONAL
nativedecide helperB - - helperN._native.native_decide.ax_1_1 1 REJECTED
wfsorry helperB - halve - 3 CONDITIONAL
sketch - target1 - - 3 CONDITIONAL
letsketch - target1 - - 3 CONDITIONAL
wholesorry - target1 - - 1 REJECTED
idsorry - target1 - - 1 REJECTED"
CF=$PKG/check/frontier/check-frontier.sh
while read -r c wf wt wd wx wex wv; do
  mkdir -p "$W/$c"; cp "$HERE/cases/$c.lean" "$W/$c/Main.lean"
  mkexp "$W/$c" Main || { ko "$c/build" "$(head -c 300 "$W/$c/build.log")"; continue; }
  got=$("$PREP" scan "$CFG" "$W/$c/Main.export" 2>/dev/null | python3 -I -c '
import json,sys; j=json.loads(sys.stdin.read()); f=lambda xs: ",".join(x if isinstance(x,str) else x["name"] for x in xs) or "-"
print(f(j["frontier"]), f(j["sorry_in_targets"]), f(j["sorry_in_definitions"]), f(j["other_axioms"]))' 2>/dev/null) || got=unparsable
  [ "$got" = "$wf $wt $wd $wx" ] && ok "scan/$c" "$got" || ko "scan/$c" "got '$got' want '$wf $wt $wd $wx'"
  py=$(FRONTIER_NO_FAST=1 FASTVERIFY_ROOT=$PKG python3 -I "$PKG/tools/frontier/frontier.py" scan "$W/$c/Main.export" "$CFG" 2>/dev/null | python3 -I -c 'import json,sys; print(",".join(json.loads(sys.stdin.read())["frontier"]) or "-")' 2>/dev/null) || py=unparsable
  [ "$py" = "$wf" ] && ok "scan-python/$c" "$py" || ko "scan-python/$c" "python preparer: '$py' want '$wf'"
  if [ "$QUICK" = 0 ]; then
    out=$("$CF" "$W/$c/Main.export" "$CHAL" "$CFG" --threads 4 2>"$W/$c/cf.err"); rc=$?
    v=$(printf '%s' "$out" | tail -1 | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); print(j["verdict"], ",".join(f["name"] for f in j.get("frontier") or []) or "-", (j.get("reason") or "")[:90])' 2>/dev/null) || v=unparsable
    if [ "$rc" = "$wex" ] && [ "${v%% *}" = "$wv" ]; then ok "e2e/$c" "exit $rc $v"; else ko "e2e/$c" "exit $rc '$v' want $wex $wv :: $(tail -c 300 "$W/$c/cf.err")"; fi
  fi
done <<< "$CASES"
[ "$QUICK" = 1 ] && { [ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"; echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit; }
# allowed lists (CI ledger mode)
printf 'helperA\nhelperB\nhelperZ\n' > "$W/allowed-ok"; printf 'helperA\n' > "$W/allowed-short"
out=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-ok" 2>/dev/null); rc=$?
[ $rc = 3 ] && printf '%s' "$out" | grep -q '"frontier_closed": \["helperZ"\]' && ok e2e/allowed-ok "exit 3, helperZ reported closed" || ko e2e/allowed-ok "exit $rc $(printf '%s' "$out" | cut -c1-200)"
out=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-short" 2>/dev/null); rc=$?
[ $rc = 1 ] && ok e2e/allowed-short "exit 1 (helperB outside the allowed frontier keeps its sorry)" || ko e2e/allowed-short "exit $rc"
# a let-bound context variable stays a let in the subgoal: the subgoal must mention the let, not quantify it
out=$("$CF" "$W/letsketch/Main.export" "$CHAL" "$CFG" --threads 4 2>/dev/null)
printf '%s' "$out" | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); t=j["frontier"][0]["type"]; sys.exit(0 if "let m" in t or "let m :=" in t else 1)' \
  && ok e2e/letsketch-keeps-let "subgoal keeps the let" || ko e2e/letsketch-keeps-let "$(printf '%s' "$out" | cut -c1-300)"
# sketch verification with an allowed list: an abstracted subgoal must be listed by its generated name
printf 'target1._fv_sorry_1\ntarget1._fv_sorry_2\n' > "$W/allowed-sketch"; printf 'target1._fv_sorry_1\n' > "$W/allowed-sketch-short"
out=$("$CF" "$W/sketch/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-sketch" 2>/dev/null); rc=$?
[ $rc = 3 ] && printf '%s' "$out" | grep -q '"name": "target1._fv_sorry_2"' && ok e2e/sketch-allowed "exit 3, both subgoals open" || ko e2e/sketch-allowed "exit $rc $(printf '%s' "$out" | cut -c1-200)"
"$CF" "$W/sketch/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-sketch-short" > /dev/null 2>&1; rc=$?
[ $rc = 1 ] && ok e2e/sketch-allowed-short "exit 1 (a subgoal outside the allowed list keeps its sorry)" || ko e2e/sketch-allowed-short "exit $rc"
# pinned frontier challenge: pin decomp; the same export -> CONDITIONAL against the pin; nested (helperC not pinned) -> REJECTED
FASTVERIFY_ROOT=$PKG python3 -I "$PKG/tools/frontier/frontier.py" pin "$W/decomp/Main.export" "$CHAL" "$CFG" "$W/pin" --threads 4 > "$W/pin.log" 2>&1; prc=$?
[ $prc = 3 ] && [ -f "$W/pin/challenge.export" ] && ok pin/create "exit 3, pinned" || ko pin/create "exit $prc $(tail -3 "$W/pin.log")"
out=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --pinned "$W/pin" 2>/dev/null); rc=$?
[ $rc = 3 ] && ok pin/same "exit 3" || ko pin/same "exit $rc $(printf '%s' "$out" | cut -c1-200)"
out=$("$CF" "$W/nested/Main.export" "$CHAL" "$CFG" --threads 4 --pinned "$W/pin" 2>/dev/null); rc=$?
[ $rc = 1 ] && ok pin/new-open-lemma "exit 1 (helperC outside the pinned frontier)" || ko pin/new-open-lemma "exit $rc $(printf '%s' "$out" | cut -c1-200)"
# a blueprint-style challenge that itself contains a sorried helper lemma (aux_lemma) which stays open in the solution:
# the redirect rewrite keeps aux_lemma a theorem (its kind still matches the challenge's) -> CONDITIONAL
mkdir -p "$W/challenge2" "$W/bluehelper"; cp "$HERE/cases/Challenge2.lean" "$W/challenge2/Challenge.lean"; cp "$HERE/cases/bluehelper.lean" "$W/bluehelper/Main.lean"
if mkexp "$W/challenge2" Challenge && mkexp "$W/bluehelper" Main; then
  out=$("$CF" "$W/bluehelper/Main.export" "$W/challenge2/Challenge.export" "$CFG" --threads 4 2>/dev/null); rc=$?
  [ $rc = 3 ] && printf '%s' "$out" | grep -q '"name": "aux_lemma"' && ok e2e/blueprint-challenge-helper "exit 3, aux_lemma open" \
    || ko e2e/blueprint-challenge-helper "exit $rc $(printf '%s' "$out" | cut -c1-250)"
else ko e2e/blueprint-challenge-helper "build failed"; fi
# regression: an open lemma inside the target STATEMENT's closure (a definition value mentioned by the statement cites it):
# compared by value with the official challenge, so never CONDITIONAL; the reason names the lemma and its path
mkdir -p "$W/challenge3" "$W/stmtclosure"; cp "$HERE/cases/Challenge3.lean" "$W/challenge3/Challenge.lean"; cp "$HERE/cases/stmtclosure.lean" "$W/stmtclosure/Main.lean"
if mkexp "$W/challenge3" Challenge && mkexp "$W/stmtclosure" Main; then
  out=$("$CF" "$W/stmtclosure/Main.export" "$W/challenge3/Challenge.export" "$CFG" --threads 4 2>/dev/null); rc=$?
  [ $rc = 1 ] && printf '%s' "$out" | grep -q "open lemma inside a target statement's closure: citation (target1 > Inputs.default > citation)" \
    && ok e2e/open-lemma-in-statement-named "exit 1, lemma + path named" || ko e2e/open-lemma-in-statement-named "exit $rc $(printf '%s' "$out" | cut -c1-300)"
else ko e2e/open-lemma-in-statement-named "build failed"; fi
# a PRIVATE open lemma: kernel name _private.Main.0.Foo.helperP; an allowed list must name it EXACTLY by that kernel name
# (regression, see tests/frontier-allowed: the source spelling Foo.helperP matched a private helperP of ANY module); a sorried theorem outside the allowed
# list is named in the REJECTED reason (usability)
mkdir -p "$W/privsorry"; cp "$HERE/cases/privsorry.lean" "$W/privsorry/Main.lean"
if mkexp "$W/privsorry" Main; then
  printf '_private.Main.0.Foo.helperP\nFoo.helperB\n' > "$W/allowed-priv"; printf 'Foo.helperB\n' > "$W/allowed-priv-short"
  printf 'Foo.helperP\nFoo.helperB\n' > "$W/allowed-priv-spelling"
  out=$("$CF" "$W/privsorry/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-priv-spelling" 2>/dev/null); rc=$?
  [ $rc = 1 ] && printf '%s' "$out" | grep -q 'outside the allowed frontier: _private.Main.0.Foo.helperP' && ok e2e/private-source-spelling-not-allowed "exit 1 (Foo.helperP does not allow _private.Main.0.Foo.helperP)" \
    || ko e2e/private-source-spelling-not-allowed "exit $rc $(printf '%s' "$out" | cut -c1-300)"
  out=$("$CF" "$W/privsorry/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-priv" 2>/dev/null); rc=$?
  [ $rc = 3 ] && printf '%s' "$out" | grep -q '_private.Main.0.Foo.helperP' && ok e2e/private-allowed "exit 3" || ko e2e/private-allowed "exit $rc $(printf '%s' "$out" | cut -c1-250)"
  out=$("$CF" "$W/privsorry/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-priv-short" 2>/dev/null); rc=$?
  [ $rc = 1 ] && printf '%s' "$out" | grep -q 'outside the allowed frontier: _private.Main.0.Foo.helperP' && ok e2e/private-outside-allowed-named "exit 1, blocker named" \
    || ko e2e/private-outside-allowed-named "exit $rc $(printf '%s' "$out" | cut -c1-300)"
else ko e2e/private "build failed"; fi
# the open lemmas stay theorems in S' (redirect): the rewritten export still has a thm record for every open lemma
out=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --keep "$W/keep-decomp" 2>/dev/null); rc=$?
nthm=$(grep -c '^{"thm":' "$W/keep-decomp/fr/solution.frontier.export" 2>/dev/null); nthm0=$(grep -c '^{"thm":' "$W/decomp/Main.export")
nax=$(grep -c '"str":"_fv_frontier_axiom"' "$W/keep-decomp/fr/solution.frontier.export" 2>/dev/null)
[ $rc = 3 ] && [ "$nthm" = "$nthm0" ] && [ "$nax" = 2 ] && ok e2e/redirect-keeps-theorems "thm records $nthm = $nthm0, 2 fresh axioms" \
  || ko e2e/redirect-keeps-theorems "exit $rc thm $nthm vs $nthm0, axioms $nax"
# progress ledger: base = decomp (helperA, helperB open); halfproved (helperB proved, still used) -> closed_proved;
# nosorry (a different proof, both lemmas gone from the closure) -> closed_dropped + warning; partial (helperB restated)
# -> statement drift, the gate blocks it
L=$PKG/tools/frontier/ledger.py
mkdir -p "$W/halfproved"; cp "$HERE/cases/halfproved.lean" "$W/halfproved/Main.lean"
if mkexp "$W/halfproved" Main; then
  "$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 > "$W/base.json" 2>/dev/null
  "$CF" "$W/halfproved/Main.export" "$CHAL" "$CFG" --threads 4 --base "$W/base.json" > "$W/half.json" 2>/dev/null; r1=$?
  "$CF" "$W/nosorry/Main.export" "$CHAL" "$CFG" --threads 4 --base "$W/base.json" > "$W/nos.json" 2>/dev/null; r2=$?
  "$CF" "$W/partial/Main.export" "$CHAL" "$CFG" --threads 4 --base "$W/base.json" > "$W/par.json" 2>/dev/null
  d1=$(python3 -I "$L" diff "$W/base.json" "$W/half.json" 2>/dev/null | python3 -I -c 'import json,sys; d=json.loads(sys.stdin.read()); print(",".join(d["closed_proved"]) or "-", ",".join(d["closed_dropped"]) or "-", ",".join(d["remaining"]) or "-")')
  [ "$r1" = 3 ] && [ "$d1" = "helperB - helperA" ] && ok ledger/proved "closed_proved helperB, remaining helperA" || ko ledger/proved "exit $r1 got '$d1'"
  d2=$(python3 -I "$L" diff "$W/base.json" "$W/nos.json" 2>/dev/null | python3 -I -c 'import json,sys; d=json.loads(sys.stdin.read()); print(",".join(d["closed_dropped"]) or "-", len(d["warnings"]))')
  [ "$r2" = 0 ] && [ "$d2" = "helperA,helperB 1" ] && ok ledger/dropped "closed_dropped helperA,helperB + warning" || ko ledger/dropped "exit $r2 got '$d2'"
  python3 -I "$L" gate "$W/base.json" "$W/nos.json" --block-dropped > /dev/null 2>&1; g1=$?
  python3 -I "$L" gate "$W/base.json" "$W/half.json" --require-progress > /dev/null 2>&1; g2=$?
  python3 -I "$L" gate "$W/base.json" "$W/par.json" > /dev/null 2>&1; g3=$?
  [ "$g1:$g2:$g3" = "1:0:1" ] && ok ledger/gate "dropped blocked, progress mergeable, statement drift blocked" || ko ledger/gate "gates $g1:$g2:$g3 want 1:0:1"
else ko ledger/build "halfproved build failed"; fi
# --a-cache (service option): the second run with the same frontier challenge skips check A; a record whose content is not
# its key is ignored; a cache dir with group/other access is refused (no verdict); a forged C' never hits an honest record
AC=$W/acache; mkdir -p "$AC"; chmod 700 "$AC"
c1=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --a-cache "$AC" 2>/dev/null | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); print(j["exit"], j["checks"]["A"].get("cached", False))')
c2=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --a-cache "$AC" 2>/dev/null | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); print(j["exit"], j["checks"]["A"].get("cached", False))')
[ "$c1|$c2" = "3 False|3 True" ] && ok acache/hit "first run checks A, second run uses the record" || ko acache/hit "got '$c1|$c2'"
for r in "$AC"/A-*.ok; do echo "0000" > "$r"; done
c3=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --a-cache "$AC" 2>/dev/null | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read()); print(j["exit"], j["checks"]["A"].get("cached", False))')
[ "$c3" = "3 False" ] && ok acache/bad-record-ignored "exit 3, A re-run" || ko acache/bad-record-ignored "got '$c3'"
chmod 750 "$AC"; "$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --a-cache "$AC" > /dev/null 2>&1; rc=$?; chmod 700 "$AC"
[ $rc = 2 ] && ok acache/group-access-refused "exit 2" || ko acache/group-access-refused "exit $rc"
# ---- lying preparers: a package copy whose frontier.py wraps the real one and tampers with its outputs ----
# --hide FILE (availability only; the encapsulated-replay list of the Lean-kernel leg) goes to BOTH sound checks; with a
# sound check that lacks --hide the wrapper refuses it up front (no verdict, reason named)
if grep -q -- '--hide) HIDE=' "$CF"; then
  printf 'Nat.add\nmyBound\n' > "$W/hide.txt"; IC=$W/icache-hide; mkdir -p "$IC"; chmod 700 "$IC"
  if grep -q -- '--hide)' "$PKG/check/sound/check-sound-svc.sh"; then
    got=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --integrity-cache "$IC" --hide "$W/hide.txt" 2>/dev/null | python3 -I -c '
import json, sys
j = json.loads(sys.stdin.read().strip().splitlines()[-1]); ch = j.get("checks") or {}
print("%s|%s" % (j["exit"], ",".join(sorted("%s:%s" % (k, bool((ch[k] or {}).get("hide_sha256"))) for k in ch))))')
    [ "$got" = "3|A:True,B:True" ] && ok hide/svc-both-checks "exit 3, hide list recorded by checks A and B" || ko hide/svc-both-checks "got '$got'"
  fi
  out=$("$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --hide "$W/hide.txt" 2>/dev/null); rc=$?
  if grep -q -- '--hide)' "$PKG/check/sound/check-sound.sh"; then want=3; else want=2; fi
  [ $rc = $want ] && ok hide/plain-sound-check "exit $rc (check-sound.sh $( [ $want = 3 ] && echo accepts || echo lacks) --hide)" || ko hide/plain-sound-check "exit $rc want $want $(printf '%s' "$out" | cut -c1-200)"
else echo "SKIP hide: check-frontier.sh without --hide"; fi
# --axioms FILE (declared PROJECT axioms as listed hypotheses, e.g. FLT's knownin1980s): extraaxiom (axiom myAx used by
# the target) is REJECTED without it, CONDITIONAL with 'myAx' listed (F = helperB's axiom + myAx); a compiler-trust axiom
# listed there is refused like any F name (no verdict); the option is only accepted where it is supported (capability probe)
if "$CF" --preflight > /dev/null 2>&1 && grep -q -- '--axioms) AXIOMS=' "$CF"; then
  printf 'myAx\n' > "$W/axioms-myax"; printf 'helperN._native.native_decide.ax_1_1\n' > "$W/axioms-trust"
  got=$("$CF" "$W/extraaxiom/Main.export" "$CHAL" "$CFG" --threads 4 --axioms "$W/axioms-myax" 2>/dev/null | python3 -I -c '
import json, sys
j = json.loads(sys.stdin.read().strip().splitlines()[-1]); print("%s|%s" % (j["exit"], ",".join(sorted(e["name"] for e in j.get("frontier") or []))))')
  [ "$got" = "3|helperB,myAx" ] && ok axioms/declared-project-axiom "exit 3, frontier helperB + myAx" || ko axioms/declared-project-axiom "got '$got'"
  out=$("$CF" "$W/nativedecide/Main.export" "$CHAL" "$CFG" --threads 4 --axioms "$W/axioms-trust" 2>/dev/null); rc=$?
  [ $rc = 2 ] && printf '%s' "$out" | grep -q "compiler / native_decide trust axiom" && ok axioms/trust-axiom-refused "exit 2, config refused" \
    || ko axioms/trust-axiom-refused "exit $rc $(printf '%s' "$out" | cut -c1-200)"
else echo "SKIP axioms: check-frontier.sh without --axioms"; fi
# --pins (another pinned pins file of the sound check; here check/sound/pins-437.env = the Lean 4.37.0-rc1 trusted check):
# cases built + exported with the OFFICIAL 4.37.0-rc1 toolchain and its bundled exporter; BOTH checks must run with the
# selected pins (toolchain recorded in each check's JSON), the pins sha256 is in the result and in the --a-cache key
P437=$PKG/check/sound/pins-437.env
TC437=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.37.0-rc1"]["prefix"])' "$PKG/config/components.json" 2>/dev/null)
if [ "$QUICK" = 0 ] && [ -f "$P437" ] && [ -n "$TC437" ] && [ -x "$TC437/bin/lean" ] && "$CF" --preflight --pins "$P437" > /dev/null 2>&1; then
  ok pins437/preflight "check-frontier.sh --preflight --pins pins-437.env"
  mkexp437() { ( cd "$1" && PATH=$TC437/bin:/usr/bin:/bin lean -o "$2.olean" "$2.lean" > build.log 2>&1 \
    && PATH=$TC437/bin:/usr/bin:/bin LEAN_PATH=$TC437/lib/lean:. LEAN_ABORT_ON_PANIC=1 leanexport "$2" -- $TARGETS > "$2.export" 2> export.log ); }
  V=$W/v437; mkdir -p "$V/challenge"; cp "$HERE/cases/Challenge.lean" "$V/challenge/"
  P437SHA=$(sha256sum "$P437" | cut -d' ' -f1)
  if mkexp437 "$V/challenge" Challenge; then
    for c in decomp:3:helperA,helperB sketch:3:target1._fv_sorry_1,target1._fv_sorry_2 nosorry:0: defsorry:1:helperA,helperB; do
      n=${c%%:*}; rest=${c#*:}; want=${rest%%:*}; wf=${rest#*:}
      mkdir -p "$V/$n"; cp "$HERE/cases/$n.lean" "$V/$n/Main.lean"
      if mkexp437 "$V/$n" Main; then
        got=$("$CF" "$V/$n/Main.export" "$V/challenge/Challenge.export" "$CFG" --threads 4 --pins "$P437" 2>/dev/null | python3 -I -c '
import json, sys
j = json.loads(sys.stdin.read().strip().splitlines()[-1]); ch = j.get("checks") or {}
tcs = sorted(set((ch.get(k) or {}).get("toolchain") or "-" for k in ch if not (ch.get(k) or {}).get("cached") and (ch.get(k) or {}).get("verdict") != "STOPPED"))
print("%s|%s|%s|%s" % (j["exit"], ",".join(e["name"] for e in j.get("frontier") or []), ",".join(tcs), j.get("pins_sha256")))')
        exp="$want|$wf|leanprover/lean4:v4.37.0-rc1|$P437SHA"
        [ "$got" = "$exp" ] && ok "pins437/$n" "exit $want, frontier '${wf:--}', every check that ran (a check A stopped after a B reject has none) on the 4.37.0-rc1 judge" || ko "pins437/$n" "got '$got' want '$exp'"
      else ko "pins437/$n" "4.37 build/export failed"; fi
    done
    AC2=$W/acache437; mkdir -p "$AC2"; chmod 700 "$AC2"
    acr() { "$CF" "$V/decomp/Main.export" "$V/challenge/Challenge.export" "$CFG" --threads 4 --a-cache "$AC2" "$@" 2>/dev/null | python3 -I -c 'import json,sys; j=json.loads(sys.stdin.read().strip().splitlines()[-1]); print(j["exit"], (j.get("checks") or {}).get("A", {}).get("cached", False))'; }
    a1=$(acr --pins "$P437"); a2=$(acr --pins "$P437"); a3=$(acr)
    case "$a1|$a2|$a3" in "3 False|3 True|"*" False") ok pins437/acache-key "a record made with pins-437 serves pins-437 only (default pins: A re-run)";;
      *) ko pins437/acache-key "got '$a1|$a2|$a3'";; esac
  else ko pins437/setup "4.37 challenge build/export failed"; fi
  "$CF" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --pins "$W/no-such-pins.env" > /dev/null 2>&1; rc=$?
  [ $rc = 2 ] && ok pins/missing-file "exit 2 (no verdict)" || ko pins/missing-file "exit $rc"
else echo "SKIP pins437: no 4.37.0-rc1 toolchain / pins-437.env / preflight on this host (or --quick)"; fi
d=$W/pkgcopy; mkdir -p "$d/check" "$d/lib" "$d/config" "$d/tools"; cp -r "$PKG/check/frontier" "$PKG/check/sound" "$PKG/check/xversion" "$d/check/"
cp "$PKG/lib/toolchain.py" "$d/lib/"; cp -r "$PKG/toolchains" "$d/"; cp "$PKG/config/components.json" "$d/config/"; cp -r "$PKG/tools/frontier" "$d/tools/"
mv "$d/tools/frontier/frontier.py" "$d/tools/frontier/frontier_real.py"
cat > "$d/tools/frontier/frontier.py" <<'PY'
import json, os, shutil, subprocess, sys
here = os.path.dirname(os.path.realpath(__file__))
mode = open(os.path.join(here, "MODE")).read().strip()
argv = sys.argv[1:]
if mode == "noallow" and "--frontier" in argv:   # the preparer ignores the allowed list (frontier = every open lemma)
    argv[argv.index("--frontier") + 1] = "auto"
r = subprocess.run([sys.executable, "-I", os.path.join(here, "frontier_real.py")] + argv, env={"FASTVERIFY_ROOT": os.path.dirname(os.path.dirname(here)), "PATH": "/usr/bin:/bin"})
outdir = sys.argv[5]
fj = os.path.join(outdir, "frontier.json"); info = json.load(open(fj))
cp = os.path.join(outdir, "frontier", "challenge.export"); sp = os.path.join(outdir, "solution.frontier.export")
if mode == "forge":            # the frontier challenge is the rewritten solution itself (pins nothing)
    os.chmod(cp, 0o644); shutil.copyfile(sp, cp)
elif mode == "target":         # a target smuggled into the frontier
    info["frontier"] = info["frontier"] + ["target1"]
elif mode == "drop":           # a frontier lemma silently not reported (its axiom stays in S')
    info["frontier"] = info["frontier"][:-1]
elif mode == "permissive":     # the preparer's own configs permit everything (must be ignored)
    for k in ("comparator.frontier.json", "comparator.compare.json"):
        c = json.load(open(os.path.join(outdir, k))); c["permitted_axioms"] += ["sorryAx", "myAx"]; json.dump(c, open(os.path.join(outdir, k), "w"))
json.dump(info, open(fj, "w"))
sys.exit(r.returncode)
PY
lie() {  # lie MODE CASE WANT_EXIT
  echo "$1" > "$d/tools/frontier/MODE"
  out=$("$d/check/frontier/check-frontier.sh" "$W/$2/Main.export" "$CHAL" "$CFG" --threads 4 2>"$W/lie-$1-$2.err"); rc=$?
  [ "$rc" = "$3" ] && ok "lie/$1/$2" "exit $rc $(printf '%s' "$out" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read())["reason"][:110])' 2>/dev/null)" \
    || ko "lie/$1/$2" "exit $rc want $3 :: $(printf '%s' "$out" | cut -c1-250)"
}
lie forge decomp 2          # check A rejects the forged C' (frontier axioms not permitted there) -> no verdict, never 3
lie forge stmtchanged 2     # forged C' would let the changed target through check B; check A rejects -> no verdict
lie target decomp 2         # config refused
lie drop decomp 1           # check B: the unreported frontier axiom (or sorry) is not permitted -> REJECTED
lie permissive defsorry 1   # the wrapper builds its own configs: sorry in a definition still rejected
lie permissive decomp 3     # ... and an honest case still CONDITIONAL
# regression (see tests/frontier-allowed): a preparer that ignores --allowed (helperB open although only helperA is allowed): the wrapper's own trusted
# F <= --allowed check refuses (no verdict, never CONDITIONAL); with the full list the same lie is harmless (CONDITIONAL)
echo noallow > "$d/tools/frontier/MODE"
out=$("$d/check/frontier/check-frontier.sh" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-short" 2>/dev/null); rc=$?
[ $rc = 2 ] && printf '%s' "$out" | grep -q 'frontier outside the --allowed list' && ok lie/noallow/decomp-short "exit 2 (trusted F <= --allowed)" \
  || ko lie/noallow/decomp-short "exit $rc want 2 :: $(printf '%s' "$out" | cut -c1-250)"
out=$("$d/check/frontier/check-frontier.sh" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-ok" 2>/dev/null); rc=$?
[ $rc = 3 ] && ok lie/noallow/decomp-ok "exit 3 (every open lemma listed)" || ko lie/noallow/decomp-ok "exit $rc want 3 :: $(printf '%s' "$out" | cut -c1-250)"
# entries naming the reserved redirect axioms (helperA._fv_frontier_axiom ...) name nothing: still no verdict
printf 'helperA._fv_frontier_axiom\nhelperB._fv_frontier_axiom\n' > "$W/allowed-axnames"
out=$("$d/check/frontier/check-frontier.sh" "$W/decomp/Main.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-axnames" 2>/dev/null); rc=$?
[ $rc = 2 ] && printf '%s' "$out" | grep -q 'frontier outside the --allowed list' && ok lie/noallow/reserved-suffix-entries "exit 2 (redirect-axiom names do not allow the lemma)" \
  || ko lie/noallow/reserved-suffix-entries "exit $rc want 2 :: $(printf '%s' "$out" | cut -c1-250)"
# a forged frontier challenge with the honest run's --a-cache: its digest differs from every honest record -> check A runs
echo forge > "$d/tools/frontier/MODE"
out=$("$d/check/frontier/check-frontier.sh" "$W/stmtchanged/Main.export" "$CHAL" "$CFG" --threads 4 --a-cache "$AC" 2>/dev/null); rc=$?
[ $rc = 2 ] && ok lie/forge-with-acache "exit 2 (check A ran and rejected the forged C')" || ko lie/forge-with-acache "exit $rc $(printf '%s' "$out" | cut -c1-200)"
[ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]

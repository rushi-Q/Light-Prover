#!/bin/bash
# tests/frontier-allowed/run.sh [PKGROOT] - regression test of the frontier --allowed list and anti-vacuity (HIGH):
#   (1) --allowed FILE bypass via a private theorem: the preparer matched an allowed `Helper.open_lemma` against a private
#       `_private.<ANY module>.0.Helper.open_lemma`, and check-frontier.sh did not enforce F <= --allowed itself;
#   (2) target-sorry anti-vacuity bypass: `theorem target_thm : False := id (by sorry)` was abstracted into the open lemma
#       `target_thm._fv_sorry_1 : False` ("T follows from T") -> CONDITIONAL, while a bare `by sorry` is REJECTED.
# Expected (fixed): (1) source spelling -> REJECTED (exit 1, the private lemma named outside the allowed frontier); the exact
# kernel name `_private.Evil.0.Helper.open_lemma` allowed -> CONDITIONAL; a preparer that ignores --allowed -> no verdict
# (trusted check, exit 2); frontier.py's own exact check refuses a loose preparer (exit 2); bin/fastverify --preset sound
# --modulo-frontier -> REJECTED. (2) every `id (by sorry)`-style wrapper -> REJECTED; a genuine sketch subgoal (statement
# != the target's type) stays CONDITIONAL.
# Inputs are built with the OFFICIAL Lean 4.36 toolchain (the comparator's) and its bundled exporter, as tests/frontier-conditional.
# Rows 'PASS|FAIL name: ...'; last line 'RESULT pass=N fail=M'; exit 0 iff all PASS. (On the pre-fix tree the bug rows FAIL.)
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKG=$(cd "${1:-$HERE/../..}" && pwd)
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$PKG/config/components.json")
W=$(mktemp -d "${SCRATCH:-${TMPDIR:-/tmp}}/frontier-allowed-test.XXXXXX"); trap '[ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
CF=$PKG/check/frontier/check-frontier.sh
TARGETS="Quot Quot.mk Quot.lift Quot.ind target_thm propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
lc() { ( cd "$1" && PATH=$TC/bin:/usr/bin:/bin LEAN_PATH=$TC/lib/lean:. lean -o "$2.olean" "$2.lean" >> build.log 2>&1 ); }
ex() { ( cd "$1" && PATH=$TC/bin:/usr/bin:/bin LEAN_PATH=$TC/lib/lean:. LEAN_ABORT_ON_PANIC=1 leanexport "$2" -- $TARGETS > "$2.export" 2> export.log ); }
js() { python3 -I -c 'import json,sys
t=[l for l in sys.stdin.read().splitlines() if l.strip()]
j=json.loads(t[-1]) if t else {}
print(j.get("verdict"), ",".join(f.get("name","?") for f in j.get("frontier") or []) or "-", (j.get("reason") or "")[:400].replace("\n"," "))' 2>/dev/null || echo "unparsable - -"; }
# challenge (official 4.36): theorem target_thm : False := by sorry
C=$W/chal; mkdir -p "$C"; printf 'theorem target_thm : False := by sorry\n' > "$C/Challenge.lean"
lc "$C" Challenge && ex "$C" Challenge || { ko setup "challenge build/export failed: $(tail -c 300 "$C/build.log")"; echo "RESULT pass=$pass fail=$fail"; exit 1; }
CFG=$W/comparator.json
printf '{"challenge_module":"Challenge","solution_module":"Solution","theorem_names":["target_thm"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' > "$CFG"
CHAL=$C/Challenge.export
# (1) solution A (the evidence): Helper.open_lemma proved (True) in Helper; a PRIVATE Helper.open_lemma : False in Evil
A=$W/solA; mkdir -p "$A"
printf 'namespace Helper\ntheorem open_lemma : True := trivial\nend Helper\n' > "$A/Helper.lean"
printf 'namespace Helper\nprivate theorem open_lemma : False := by sorry\nend Helper\ntheorem target_thm : False := Helper.open_lemma\n' > "$A/Evil.lean"
printf 'import Helper\nimport Evil\n' > "$A/Solution.lean"
if lc "$A" Helper && lc "$A" Evil && lc "$A" Solution && ex "$A" Solution; then
  printf 'Helper.open_lemma\n' > "$W/allowed-spelling"; printf '_private.Evil.0.Helper.open_lemma\n' > "$W/allowed-exact"
  out=$("$CF" "$A/Solution.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-spelling" 2>/dev/null); rc=$?; v=$(printf '%s\n' "$out" | js)
  [ $rc = 1 ] && case "$v" in *"outside the allowed frontier: _private.Evil.0.Helper.open_lemma"*) true;; *) false;; esac \
    && ok private/source-spelling "exit 1 REJECTED, private lemma named outside the allowed frontier" || ko private/source-spelling "exit $rc '$v' (want 1 REJECTED)"
  out=$("$CF" "$A/Solution.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-exact" 2>/dev/null); rc=$?; v=$(printf '%s\n' "$out" | js)
  [ $rc = 3 ] && [ "$(echo "$v" | cut -d' ' -f1-2)" = "CONDITIONAL _private.Evil.0.Helper.open_lemma" ] \
    && ok private/exact-kernel-name "exit 3 CONDITIONAL, frontier _private.Evil.0.Helper.open_lemma" || ko private/exact-kernel-name "exit $rc '$v' (want 3)"
  # the TRUSTED check alone: a package copy whose preparer ignores --allowed (frontier = every open lemma)
  d=$W/pkgcopy; mkdir -p "$d/check" "$d/lib" "$d/config" "$d/tools"; cp -r "$PKG/check/frontier" "$PKG/check/sound" "$PKG/check/xversion" "$d/check/"
  cp "$PKG/lib/toolchain.py" "$d/lib/"; cp -r "$PKG/toolchains" "$d/"; cp "$PKG/config/components.json" "$d/config/"; cp -r "$PKG/tools/frontier" "$d/tools/"
  mv "$d/tools/frontier/frontier.py" "$d/tools/frontier/frontier_real.py"
  cat > "$d/tools/frontier/frontier.py" <<'PY'
import os, subprocess, sys
here = os.path.dirname(os.path.realpath(__file__))
argv = sys.argv[1:]
if "--frontier" in argv:
    argv[argv.index("--frontier") + 1] = "auto"
sys.exit(subprocess.run([sys.executable, "-I", os.path.join(here, "frontier_real.py")] + argv,
                        env={"FASTVERIFY_ROOT": os.path.dirname(os.path.dirname(here)), "PATH": "/usr/bin:/bin"}).returncode)
PY
  out=$("$d/check/frontier/check-frontier.sh" "$A/Solution.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-spelling" 2>/dev/null); rc=$?; v=$(printf '%s\n' "$out" | js)
  [ $rc = 2 ] && case "$v" in *"frontier outside the --allowed list"*) true;; *) false;; esac \
    && ok trusted/preparer-ignores-allowed "exit 2 (check-frontier.sh's own F <= --allowed check)" || ko trusted/preparer-ignores-allowed "exit $rc '$v' (want 2, never 3)"
  out=$("$d/check/frontier/check-frontier.sh" "$A/Solution.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-exact" 2>/dev/null); rc=$?
  [ $rc = 3 ] && ok trusted/exact-name-passes "exit 3 (the exactly listed private lemma)" || ko trusted/exact-name-passes "exit $rc (want 3)"
  # a list naming only the reserved redirect axiom of the lemma allows nothing (lying preparer:
  # no verdict; honest: REJECTED); a list line with a trailing no-break space is no Lean name for the preparer, frontier.py
  # and the trusted step alike (no verdict)
  printf '_private.Evil.0.Helper.open_lemma._fv_frontier_axiom\n' > "$W/allowed-axname"
  out=$("$d/check/frontier/check-frontier.sh" "$A/Solution.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-axname" 2>/dev/null); rc=$?
  [ $rc = 2 ] && ok trusted/reserved-suffix-entry "exit 2 (lying preparer)" || ko trusted/reserved-suffix-entry "exit $rc (want 2)"
  "$CF" "$A/Solution.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-axname" > /dev/null 2>&1; rc=$?
  [ $rc = 1 ] && ok private/reserved-suffix-entry-honest "exit 1 REJECTED" || ko private/reserved-suffix-entry-honest "exit $rc (want 1)"
  printf '_private.Evil.0.Helper.open_lemma\xc2\xa0\n' > "$W/allowed-nbsp"
  "$CF" "$A/Solution.export" "$CHAL" "$CFG" --threads 4 --allowed "$W/allowed-nbsp" > /dev/null 2>&1; rc=$?
  [ $rc = 2 ] && ok private/nbsp-line-no-name "exit 2 (not a Lean name anywhere)" || ko private/nbsp-line-no-name "exit $rc (want 2)"
  # frontier.py's own exact check: the pre-fix (loose) preparer binary, when present on this host
  OLDP=/scratch/fastverify-next/frontier/bd1c7a2d/fvfrontier-prep
  if [ -x "$OLDP" ] && [ "$(sha256sum < "$OLDP" | cut -d' ' -f1)" = bd1c7a2d0582756fc5311074924f2c10a28612a303526d22e5024b09212df989 ]; then
    d2=$W/pkgold; mkdir -p "$d2/check/frontier" "$d2/tools"; cp -r "$PKG/tools/frontier" "$d2/tools/"
    printf 'PIN fvfrontier_prep bd1c7a2d0582756fc5311074924f2c10a28612a303526d22e5024b09212df989 %s\n' "$OLDP" > "$d2/check/frontier/pins.env"
    FASTVERIFY_ROOT=$d2 python3 -I "$d2/tools/frontier/frontier.py" prepare "$A/Solution.export" "$CHAL" "$CFG" "$W/prep-old" --frontier "@$W/allowed-spelling" > "$W/prep-old.out" 2>&1; rc=$?
    [ $rc = 2 ] && grep -q "frontier outside the allowed / pinned list" "$W/prep-old.out" && ok driver/loose-preparer-refused "frontier.py exit 2 (exact-name check)" \
      || ko driver/loose-preparer-refused "exit $rc $(tail -c 300 "$W/prep-old.out")"
  else echo "SKIP driver/loose-preparer-refused: pre-fix fvfrontier-prep bd1c7a2d not on this host"; fi
  # the Python preparer (no fast binary) has always matched exactly
  py=$(FRONTIER_NO_FAST=1 FASTVERIFY_ROOT=$PKG python3 -I "$PKG/tools/frontier/frontier.py" prepare "$A/Solution.export" "$CHAL" "$CFG" "$W/prep-py" --frontier "@$W/allowed-spelling" > /dev/null 2>&1; python3 -I -c 'import json,sys; print(",".join(json.load(open(sys.argv[1]))["frontier"]) or "-")' "$W/prep-py/frontier.json" 2>/dev/null)
  [ "$py" = "-" ] && ok python-preparer/exact "empty frontier (the private lemma is not allowed)" || ko python-preparer/exact "got '$py'"
else ko solA/build "$(tail -c 300 "$A/build.log")"; fi
# (2) target-sorry wrappers: each must be REJECTED like a bare `by sorry`; a genuine sketch subgoal stays CONDITIONAL
mkcase() {  # mkcase NAME LEAN_VALUE
  mkdir -p "$W/$1"; printf 'theorem target_thm : False := %s\n' "$2" > "$W/$1/Solution.lean"; lc "$W/$1" Solution && ex "$W/$1" Solution; }
row() {  # row NAME WANT_EXIT WANT_VERDICT VALUE
  if mkcase "$1" "$4"; then
    out=$("$CF" "$W/$1/Solution.export" "$CHAL" "$CFG" --threads 4 2>/dev/null); rc=$?; v=$(printf '%s\n' "$out" | js)
    [ "$rc" = "$2" ] && [ "${v%% *}" = "$3" ] && ok "vacuity/$1" "exit $rc $v" || ko "vacuity/$1" "exit $rc '$v' want $2 $3 (value: $4)"
  else ko "vacuity/$1" "build failed: $(tail -c 300 "$W/$1/build.log")"; fi
}
row bare-sorry 1 REJECTED 'by sorry'
row id-sorry 1 REJECTED 'id (by sorry)'
row ascribed-sorry 1 REJECTED '(id (by sorry : False) : False)'
row fun-applied-sorry 1 REJECTED '(fun (h : False) => h) (by sorry)'
row let-sorry 1 REJECTED 'let x := 0; id (by sorry)'
row show-from-sorry 1 REJECTED 'show False from id (by sorry)'
row genuine-sketch 3 CONDITIONAL 'absurd (by sorry : 1 = 1) (by sorry : ¬ (1 = 1))'
# end to end: bin/fastverify --preset sound --modulo-frontier ALLOWED (the evidence's last step), challenge pinned
if [ -d "$A" ] && [ -x "$PKG/bin/fastverify" ]; then
  P=$W/projA; mkdir -p "$P"; cp "$A"/{Helper,Evil,Solution}.lean "$P/"; printf 'leanprover/lean4:v4.36.0\n' > "$P/lean-toolchain"
  printf 'name = "solA"\ndefaultTargets = ["Solution"]\n[[lean_lib]]\nname = "Helper"\n[[lean_lib]]\nname = "Evil"\n[[lean_lib]]\nname = "Solution"\n' > "$P/lakefile.toml"
  CD=$W/chaldir; mkdir -p "$CD"; cp "$CHAL" "$CD/challenge.export"; cp "$CFG" "$CD/comparator.json"; cp "$C/Challenge.lean" "$CD/"; printf 'leanprover/lean4:v4.36.0\n' > "$CD/lean-toolchain"
  printf 'name = "chal"\ndefaultTargets = ["Challenge"]\n[[lean_lib]]\nname = "Challenge"\n' > "$CD/lakefile.toml"
  PIN=$(sha256sum "$CD/challenge.export" | cut -d' ' -f1)
  CPIN=$(sha256sum "$CD/comparator.json" | cut -d' ' -f1)   # comparator pin required with the challenge pin
  timeout 1800 "$PKG/bin/fastverify" "$P" "$CD" "$W/fv_out" --preset sound --modulo-frontier "$W/allowed-spelling" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --threads 4 > "$W/fv.out" 2>&1; rc=$?
  [ $rc = 1 ] && ok e2e/fastverify-modulo-frontier "exit 1 REJECTED" || ko e2e/fastverify-modulo-frontier "exit $rc (want 1): $(tail -1 "$W/fv.out" | cut -c1-300)"
fi
# frontier.py run requires --comparator-sha256 with --challenge-sha256 (exit 2 before
# anything runs) and refuses a wrong one
if [ -d "${P:-}" ] && [ -f "${CD:-}/comparator.json" ]; then
  python3 -I "$PKG/tools/frontier/frontier.py" run "$P" "$CD" "$W/frun1" --challenge-sha256 "$PIN" --threads 4 > "$W/frun1.log" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q -- '--comparator-sha256' "$W/frun1.log" && [ ! -e "$W/frun1/fv" ] && ok pin/frontier-run-missing-comparator-pin "exit 2, nothing ran" || ko pin/frontier-run-missing-comparator-pin "exit $rc $(tail -c 200 "$W/frun1.log")"
  python3 -I "$PKG/tools/frontier/frontier.py" run "$P" "$CD" "$W/frun2" --challenge-sha256 "$PIN" --comparator-sha256 0000000000000000000000000000000000000000000000000000000000000000 --threads 4 > "$W/frun2.log" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q 'differs from --comparator-sha256' "$W/frun2.log" && ok pin/frontier-run-wrong-comparator-pin "exit 2" || ko pin/frontier-run-wrong-comparator-pin "exit $rc $(tail -c 200 "$W/frun2.log")"
  # every malformed input is a refusal (exit 2), never a crash (exit 1)
  CPIN=$(sha256sum "$CD/comparator.json" | cut -d' ' -f1)
  mkdir -p "$W/nocfg" "$W/dircfg/comparator.json"; cp "$CD/challenge.export" "$W/nocfg/"; cp "$CD/challenge.export" "$W/dircfg/"
  for case in "nocfg|run $P $W/nocfg $W/frun3 --challenge-sha256 $PIN --comparator-sha256 $CPIN" \
              "dircfg|run $P $W/dircfg $W/frun4 --challenge-sha256 $PIN --comparator-sha256 $CPIN" \
              "novalue|run $P $CD $W/frun5 --challenge-sha256 $PIN --comparator-sha256" \
              "extra-positional|run $P $CD $W/frun6 extra --challenge-sha256 $PIN --comparator-sha256 $CPIN" \
              "verify-nocfg|verify $CHAL $CHAL $W/nocfg/comparator.json $W/fv7 --challenge-sha256 $PIN --comparator-sha256 $CPIN" \
              "verify-challenge-pin-only|verify $CHAL $CHAL $CFG $W/fv8 --challenge-sha256 $PIN"; do
    n=${case%%|*}; args=${case#*|}
    python3 -I "$PKG/tools/frontier/frontier.py" $args > "$W/exit-$n.log" 2>&1; rc=$?
    [ $rc = 2 ] && ! grep -q Traceback "$W/exit-$n.log" && ok "pin/exit-$n" "exit 2, no traceback" || ko "pin/exit-$n" "exit $rc $(tail -c 200 "$W/exit-$n.log")"
  done
  python3 -I "$PKG/tools/frontier/frontier.py" run "$P" "$CD" "$W/frun9" --challenge-sha256="$PIN" --comparator-sha256=0000000000000000000000000000000000000000000000000000000000000000 > "$W/frun9.log" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q 'differs from --comparator-sha256' "$W/frun9.log" && ok pin/equals-form-parsed "--opt=HEX read (wrong pin -> exit 2)" || ko pin/equals-form-parsed "exit $rc $(tail -c 200 "$W/frun9.log")"
  # an EMPTY pin is a malformed pin, never "no pin" (verify ran unpinned before); pins on a subcommand
  # that cannot enforce them are refused; a wrong challenge digest is refused before bin/fastverify starts; pin into a
  # non-empty PINDIR is exit 2
  for case in "verify-empty-comparator|verify|$CHAL|$CHAL|$CFG|$W/fv10|--challenge-sha256|$PIN|--comparator-sha256|@E@" \
              "verify-empty-both|verify|$CHAL|$CHAL|$CFG|$W/fv11|--challenge-sha256|@E@|--comparator-sha256|@E@" \
              "verify-empty-comparator-only|verify|$CHAL|$CHAL|$CFG|$W/fv12|--comparator-sha256|@E@" \
              "scan-with-pin|scan|$CHAL|$CFG|--comparator-sha256|abc" \
              "check-with-pin|check|$W/fv12|--challenge-sha256|$PIN" \
              "prepare-with-pin|prepare|$CHAL|$CHAL|$CFG|$W/fv13|--comparator-sha256|$CPIN" \
              "pin-with-pin|pin|$CHAL|$CHAL|$CFG|$W/pin14|--challenge-sha256|$PIN"; do
    n=${case%%|*}; IFS='|' read -r -a av <<< "${case#*|}"; av=("${av[@]/#@E@/}")   # @E@ = an explicitly EMPTY argument
    python3 -I "$PKG/tools/frontier/frontier.py" "${av[@]}" > "$W/exit-$n.log" 2>&1; rc=$?
    v=$(tail -1 "$W/exit-$n.log" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("verdict"))' 2>/dev/null)
    [ $rc = 2 ] && [ "$v" = NO_VERDICT ] && ! grep -q Traceback "$W/exit-$n.log" && ok "pin/exit-$n" "exit 2 NO_VERDICT: $(tail -1 "$W/exit-$n.log" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("why","")[:90])' 2>/dev/null)" \
      || ko "pin/exit-$n" "exit $rc $v $(tail -c 200 "$W/exit-$n.log")"
  done
  python3 -I "$PKG/tools/frontier/frontier.py" run "$P" "$CD" "$W/frun15" --challenge-sha256 0000000000000000000000000000000000000000000000000000000000000000 --comparator-sha256 "$CPIN" --threads 4 > "$W/frun15.log" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q 'differs from --challenge-sha256' "$W/frun15.log" && [ ! -e "$W/frun15/fv" ] && ok pin/wrong-challenge-pin-refused-before-child "exit 2, bin/fastverify not started" || ko pin/wrong-challenge-pin-refused-before-child "exit $rc $(tail -c 200 "$W/frun15.log")"
  mkdir -p "$W/pin16"; echo x > "$W/pin16/occupied"
  python3 -I "$PKG/tools/frontier/frontier.py" pin "$CHAL" "$CHAL" "$CFG" "$W/pin16" > "$W/pin16.log" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q 'exists and is not empty' "$W/pin16.log" && ok pin/pin-into-nonempty-dir "exit 2" || ko pin/pin-into-nonempty-dir "exit $rc $(tail -c 200 "$W/pin16.log")"
  # run clears only its OWN earlier outputs: a non-empty OUT that is not a frontier.py run output is refused, untouched
  mkdir -p "$W/frun17/frontier"; echo keep > "$W/frun17/frontier/user-file"
  python3 -I "$PKG/tools/frontier/frontier.py" run "$P" "$CD" "$W/frun17" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --threads 4 > "$W/frun17.log" 2>&1; rc=$?
  [ $rc = 2 ] && grep -q 'not a frontier.py run output' "$W/frun17.log" && [ "$(cat "$W/frun17/frontier/user-file")" = keep ] && [ ! -e "$W/frun17/fv" ] \
    && ok pin/run-foreign-out-refused "exit 2, nothing removed" || ko pin/run-foreign-out-refused "exit $rc $(tail -c 200 "$W/frun17.log")"
  # every non-completion is NO_VERDICT exit 2 (never 1); the OUT marker
  # is never followed; one run per OUT
  FR="$PKG/tools/frontier/frontier.py"; RUNP=(--challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --threads 4)
  x2() {  # x2 ROW LOGFILE RC : exit 2 + NO_VERDICT JSON + no traceback
    local v; v=$(tail -1 "$2" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("verdict"))' 2>/dev/null)
    [ "$3" = 2 ] && [ "$v" = NO_VERDICT ] && ! grep -q Traceback "$2" && ok "exit2/$1" "NO_VERDICT: $(tail -1 "$2" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("why","")[:80])' 2>/dev/null)" \
      || ko "exit2/$1" "exit $3 $v $(tail -c 200 "$2")"; }
  mkdir -p "$W/ro1"; chmod 555 "$W/ro1"
  python3 -I "$FR" run "$P" "$CD" "$W/ro1/out" "${RUNP[@]}" > "$W/x1.log" 2>&1; x2 run-out-in-readonly-parent "$W/x1.log" $?
  mkdir -p "$W/ro10"; chmod 555 "$W/ro10"
  python3 -I "$FR" run "$P" "$CD" "$W/ro10" "${RUNP[@]}" > "$W/x10.log" 2>&1; x2 run-empty-readonly-out "$W/x10.log" $?
  chmod 755 "$W/ro1" "$W/ro10"
  mkdir -p "$W/x2out"; echo x > "$W/x2out/pinned"
  python3 -I "$FR" verify "$CHAL" "$CHAL" "$CFG" "$W/x2out" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" > "$W/x2.log" 2>&1; x2 verify-pinned-is-a-file "$W/x2.log" $?
  python3 -I "$FR" verify "$CHAL" "$CHAL" "$CFG" "$W/x3out" --pinned "$W/no-such-pin-dir" > "$W/x3.log" 2>&1; x2 verify-missing-pinned-dir "$W/x3.log" $?
  python3 -I "$FR" run "$P" "$CD" "$W/x9out" --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --threads abc > "$W/x9.log" 2>&1; x2 run-bad-threads "$W/x9.log" $?
  [ ! -e "$W/x9out/fv" ] && ok exit2/run-bad-threads-nothing-started "bin/fastverify not started" || ko exit2/run-bad-threads-nothing-started "OUT/fv exists"
  python3 -I "$FR" verify "$CHAL" "$CHAL" "$CFG" "$W/x9v" --threads abc > "$W/x9v.log" 2>&1; x2 verify-bad-threads "$W/x9v.log" $?
  mkdir -p "$W/x5out"; echo precious > "$W/x5victim"; ln -s "$W/x5victim" "$W/x5out/.frontier-run-out"
  python3 -I "$FR" run "$P" "$CD" "$W/x5out" "${RUNP[@]}" > "$W/x5.log" 2>&1; rc=$?
  [ "$rc" = 2 ] && [ "$(cat "$W/x5victim")" = precious ] && ok marker/symlink-not-followed "exit 2, link target untouched" || ko marker/symlink-not-followed "exit $rc victim '$(cat "$W/x5victim")'"
  mkdir -p "$W/x11out"; : > "$W/x11out/.frontier-run-out"
  python3 -I -c 'import fcntl,os,sys,time; fd=os.open(sys.argv[1], os.O_RDWR); fcntl.flock(fd, fcntl.LOCK_EX); open(sys.argv[2],"w").close(); time.sleep(60)' "$W/x11out/.frontier-run-out" "$W/x11.locked" &
  LP=$!; for _ in $(seq 1 100); do [ -e "$W/x11.locked" ] && break; sleep 0.1; done
  python3 -I "$FR" run "$P" "$CD" "$W/x11out" "${RUNP[@]}" > "$W/x11.log" 2>&1; rc=$?; kill $LP 2>/dev/null; wait $LP 2>/dev/null
  [ "$rc" = 2 ] && grep -q 'in use by another frontier.py run' "$W/x11.log" && [ ! -e "$W/x11out/fv" ] && ok lock/out-in-use-refused "exit 2, nothing started" || ko lock/out-in-use-refused "exit $rc $(tail -c 200 "$W/x11.log")"
  # run never forwards --export-dir / --extra-kernel / --require-kernel (the export
  # must stay in OUT/fv; the deciding checks do not take extra kernels): refused before bin/fastverify starts
  for xo in "--export-dir $W/elsewhere" "--require-kernel con-leche" "--extra-kernel con-leche" "--export-dir=$W/elsewhere"; do
    n=$(echo "$xo" | cut -d' ' -f1 | tr -c 'A-Za-z0-9\n' _)
    python3 -I "$FR" run "$P" "$CD" "$W/xe$n" "${RUNP[@]}" -- $xo > "$W/xe$n.log" 2>&1; rc=$?
    [ "$rc" = 2 ] && grep -q 'not allowed' "$W/xe$n.log" && [ ! -e "$W/xe$n/fv" ] && ok "extra/$n-refused" "exit 2, bin/fastverify not started" \
      || ko "extra/$n-refused" "exit $rc $(tail -c 200 "$W/xe$n.log")"
  done
  # a missing export is refused at once (no fvfrontier-prep hang); an earlier verdict.json in
  # OUTDIR never survives a failed verify; the comparator pin alone is refused; an unknown option is refused
  timeout 120 python3 -I "$FR" verify "$W/no-such.export" "$CHAL" "$CFG" "$W/x12" > "$W/x12.log" 2>&1; x2 verify-missing-export "$W/x12.log" $?
  mkdir -p "$W/x13"; echo '{"verdict": "ACCEPTED", "exit": 0}' > "$W/x13/verdict.json"
  python3 -I "$FR" verify "$CHAL" "$CHAL" "$CFG" "$W/x13" --challenge-sha256 "$PIN" --comparator-sha256 0000000000000000000000000000000000000000000000000000000000000000 > "$W/x13.log" 2>&1; rc=$?
  [ "$rc" = 2 ] && [ ! -e "$W/x13/verdict.json" ] && ok verify/stale-verdict-removed "exit 2, no earlier verdict.json left" || ko verify/stale-verdict-removed "exit $rc $(ls "$W/x13")"
  python3 -I "$FR" verify "$CHAL" "$CHAL" "$CFG" "$W/x14" --comparator-sha256 "$CPIN" > "$W/x14.log" 2>&1; x2 verify-comparator-pin-alone "$W/x14.log" $?
  python3 -I "$FR" verify "$CHAL" "$CHAL" "$CFG" "$W/x15" --challenge-sha "$PIN" > "$W/x15.log" 2>&1; rc=$?
  [ "$rc" = 2 ] && grep -q 'unknown option --challenge-sha' "$W/x15.log" && ok exit2/unknown-option "exit 2" || ko exit2/unknown-option "exit $rc $(tail -c 200 "$W/x15.log")"
fi
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]

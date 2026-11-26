#!/bin/bash
# tests/fvwork/run.sh [WORKDIR]  (kind: component, sound mode; ~3-5 min on a test host, no Mathlib)
# Regression test of tools/fvwork (the persistent per-repository verification daemon; untrusted orchestration around the
# UNCHANGED trusted check). Fixture x/tiny (Tiny.A <- Tiny.B <- Solution, target foo) + x/challenge:
#   base        bin/fastverify --preset sound (no merge) --keep-work                                 -> ACCEPTED
#   init/serve  fvwork init --adopt BASE; serve --warm 1 --reuse-identical (background)
#   have        files: a valid proof edit in Tiny/A.lean                                              -> ACCEPTED (exact, 3 dirty)
#   have-again  the identical state again: same export sha256 -> verdict re-reported (reused), no check run
#   warm        at least one of the requests used a pre-warmed Lean-kernel leg
#   sorry       files: Tiny/B.lean gains 'have ... := sorry'                                           -> REJECTED (sorryAx)
#   break       files: an ill-typed step in Tiny/B.lean -> build fails, diagnostics name Tiny.B       -> REJECTED (build1)
#   kbad        files: Tiny/B.lean gains a kernel-invalid 'decide +kernel' theorem used by foo (passes the
#               skip-kernel-tc build)                                                                  -> REJECTED by the kernel leg
#   stmt        files: the statement of the target foo changes                                         -> REJECTED (compareAt)
#   fixed       files: back to the original sources                                                    -> ACCEPTED
#   tree        tree: a full copy of x/tiny                                                            -> ACCEPTED
#   git         git: a repository with x/tiny committed, rev HEAD                                      -> ACCEPTED
#   order       Tiny.A + Solution edited, Tiny.B clean in between, --mode optimistic (EXPERIMENTAL): the optimistic
#               pass builds A first -> ACCEPTED (provisional, confirmed by an exact attempt)
#   watch       fvwork watch on a working tree: initial ACCEPTED, then a breaking save -> REJECTED + 'Tiny/B.lean:L:C: error'
#   badrev      git: an option-like rev '-o<file>' (option injection into git archive)                   -> no verdict, no file
#   badpath     files: '../escape.lean'                                                                -> no verdict (exit 2), daemon alive
#   farm        serve --copy-mode farm: --no-advance --files candidates (valid / sorry / kernel-bad) on a symlink farm over
#               the base -> ACCEPTED / REJECTED / REJECTED, copy_mode farm, every base file unchanged (sha256 over the tree)
#   symlink     incr-build --changed (fvwork's sparse sync of a --files request) on a base tree holding a symlinked
#               directory that points outside: a write through it is refused (exit 2), nothing is written outside
#   concurrent  serve --jobs 2: two --no-advance requests at once (valid edits)                         -> both ACCEPTED, base unchanged
#   guard       serve --guard 'wall=25': an elaboration that sleeps 90 s                                -> no verdict after 25 s, daemon alive
#   lake-*      init --build lake (official incremental lake build + official exporter): have / sorry / break / fixed
#   warm-delta  (with check/warm) the valid edit above was judged by check_delta from the delta of the rebuilt module (the
#               tools/delta-export), without a full export
#   delta-drift with --check warm and --drift: statement drift from the delta (exphash): proof edit -> 0 statement changes,
#               restated target -> STATEMENT-CHANGED foo (and REJECTED)
#   frontier-acache  the same frontier again (candidate): CONDITIONAL with check A taken from check-frontier --a-cache
#   pins        (only if check-sound-svc.sh takes --pins, check-sound v3 wiring) serve --pins check/sound/pins.env (the default
#               pins given explicitly): proof edit ACCEPTED, sorry REJECTED, no pre-warmed leg used
#   frontier    (only if check/frontier/check-frontier.sh preflights) serve --check frontier: tinyB := by sorry
#               -> CONDITIONAL with frontier [tinyB] (source Tiny/B.lean); with a frontier pin (frontier.py pin)
#               a restated open lemma (still builds) -> REJECTED; then the original proof -> ACCEPTED, ledger closed [tinyB]
# the main, concurrency, guard and pins daemons take the DEFAULT cold sound path (every request = bin/fastverify
# --preset sound on the submitted tree: outcome cold0/cold1, no memo reuse, no pre-warmed legs, no per-module diagnostics);
# the farm, lake, warm and frontier daemons run with --experimental-incremental, whose ACCEPTED / CONDITIONAL is never counted
# (NO-VERDICT + "provisional"): their rows read the provisional verdict (ask() marks it counted: false).
# Prints 'PASS|FAIL|SKIP case: detail' rows and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
FW=${FVWORK:-$FV/tools/fvwork/fvwork.py}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/fvwork.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"; fails=0; T=${EVAL_THREADS:-8}
row() { echo "$1 $2: $3"; if [ "$1" = FAIL ]; then fails=$((fails+1)); fi; return 0; }
U="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo-portable lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo-portable lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo,skip-kernel-tc${FVTEST_KTC:+=$FVTEST_KTC},linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,check-tail"
cp -r "$H/x/challenge" "$W/ch"
"$FV/bin/fastverify" "$H/x/tiny" "$W/ch" "$W/base" --preset sound --unsafe "$U" --threads "$T" --keep-work --overlap-targets none > "$W/base.log" 2>&1
rc=$?; [ $rc = 0 ] && row PASS base ACCEPTED || { row FAIL base "exit $rc (see $W/base.log)"; echo "RESULT FAIL"; exit 1; }
cp "$W/base/challenge.export" "$W/ch/"; CSHA=$(sha256sum "$W/ch/challenge.export" | cut -d' ' -f1)
# the caller's comparator pin, where the fvwork under test takes it
CMPIN=; grep -q -- '--comparator-sha256' "$FW" && CMPIN="--comparator-sha256 $(sha256sum < "$W/ch/comparator.json" | cut -c1-64)"
TC=${INCR_TC:-$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); print(c["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json")}
WS=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["inputs"]["packages_workspace"] or "")' "$W/base/result.json")
init() {  # init STATE
  python3 -I "$FW" init --state "$1" --project "$H/x/tiny" --challenge "$W/ch" --challenge-sha256 "$CSHA" $CMPIN --threads "$T" \
    --fv "$FV" --tc "$TC" ${WS:+--packages "$WS"} --adopt "$W/base" > "$1.init.log" 2>&1
}
# the farm / lake / warm / frontier daemons use the EXPERIMENTAL incremental machinery explicitly
XINC=; grep -q -- '--experimental-incremental' "$FW" && XINC=--experimental-incremental
serve() {  # serve STATE ARGS... (background; waits for the socket)
  local st=$1; shift
  python3 -I "$FW" serve --state "$st" "$@" > "$st.serve.log" 2>&1 &
  for i in $(seq 1 100); do [ -S "$st/sock" ] && break; sleep 0.1; done
  [ -S "$st/sock" ]
}
stop() { python3 -I "$FW" stop --state "$1" > /dev/null 2>&1; for i in $(seq 1 100); do [ -S "$1/sock" ] || break; sleep 0.1; done; }
# edited file contents (relative to x/tiny)
A_HAVE=$'theorem tinyA (n : Nat) : n + 0 = n := by\n  have _fvw : (2 : Nat) + 2 = 4 := rfl\n  rfl\n'
B_ORIG=$(cat "$H/x/tiny/Tiny/B.lean"); A_ORIG=$(cat "$H/x/tiny/Tiny/A.lean"); S_ORIG=$(cat "$H/x/tiny/Solution.lean")
B_SORRY=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  have _fvw : (2 : Nat) + 2 = 4 := sorry\n  rw [tinyA]\n'
B_BREAK=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  have _fvw : (2 : Nat) + 2 = 5 := rfl\n  rw [tinyA]\n'
B_KBAD=$(cat "$H/x/kbad/Tiny/B.lean" 2>/dev/null || printf '%s\n%s\n' "$B_ORIG" 'theorem v05bad : (2 : Nat) + 2 = 5 := by decide +kernel')
S_KBAD=$(cat "$H/x/kbad/Solution.lean" 2>/dev/null || printf 'import Tiny.B\ntheorem foo : (2 : Nat) + 2 = 4 := by\n  have h := v05bad\n  omega\n')
S_STMT=$'import Tiny.B\ntheorem foo : (2 : Nat) + 2 = 4 \xe2\x88\xa7 True := by\n  have h := tinyB\n  rw [tinyA] at h\n  exact \xe2\x9f\xa8h, trivial\xe2\x9f\xa9\n'
B_FSORRY=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  sorry\n'
files() {  # files OUT.json REL CONTENT [REL CONTENT ...]
  local o=$1; shift
  python3 -I -c 'import json,sys; a=sys.argv[2:]; json.dump({a[i]: a[i+1] for i in range(0, len(a), 2)}, open(sys.argv[1], "w"))' "$o" "$@"
}
ask() {  # ask STATE NAME ARGS... -> $W/NAME.json (final answer), returns the exit
  local st=$1 n=$2; shift 2
  python3 -I "$FW" verify --state "$st" "$@" > "$W/$n.out" 2>&1; local rc=$?
  tail -1 "$W/$n.out" > "$W/$n.json"
  # a daemon started with --experimental-incremental never counts an ACCEPTED / CONDITIONAL: it answers NO-VERDICT
  # + "provisional"; the rows on those daemons test the machinery, so they read the provisional verdict (counted: false)
  local pv; pv=$(python3 -I -c 'import json,sys
try: r=json.load(open(sys.argv[1]))
except Exception: sys.exit()
p=r.get("provisional")
if p and r.get("verdict") == "NO-VERDICT":
    r["verdict"], r["counted"] = p, False; json.dump(r, open(sys.argv[1], "w")); print({"ACCEPTED": 0, "REJECTED": 1, "CONDITIONAL": 3}[p])' "$W/$n.json" 2>/dev/null)
  [ -n "$pv" ] && rc=$pv
  return $rc
}
jq_() { python3 -I -c "import json,sys; r=json.load(open(sys.argv[1])); print($2)" "$W/$1.json" 2>/dev/null; }

ST=$W/st; init "$ST" || { row FAIL init "$(tail -3 "$ST.init.log")"; echo "RESULT FAIL"; exit 1; }
row PASS init "$(tail -1 "$ST.init.log" | cut -c1-120)"
serve "$ST" --warm 1 --threads "$T" --reuse-identical || { row FAIL serve "no socket ($(tail -3 "$ST.serve.log"))"; echo "RESULT FAIL"; exit 1; }
sleep 3   # first warm leg ingests the base export
files "$W/have.files" Tiny/A.lean "$A_HAVE"
ask "$ST" have --files "$W/have.files"; rc=$?
v=$(jq_ have 'r["verdict"], r["attempts"][0]["mode"], len(r["attempts"])')
[ $rc = 0 ] && [ "$v" = "ACCEPTED cold 1" ] && row PASS have "$v" || row FAIL have "exit $rc: $v"
ask "$ST" have-again --files "$W/have.files"; rc=$?
v=$(jq_ have-again 'r["verdict"], r["attempts"][-1]["outcome"], r["export_sha256"] == json.load(open(sys.argv[1].replace("have-again", "have")))["export_sha256"]')
[ $rc = 0 ] && [ "$v" = "ACCEPTED cold0 True" ] && row PASS have-again "$v (re-judged cold, same export)" || row FAIL have-again "exit $rc: $v"
# regression (tools/incr/incr-build.py): Tiny.A and Solution edited together, Tiny.B (clean) in between -> the optimistic pass
# must still build Tiny.A before Solution (before the fix: 'failed to open .../Tiny/A.olean' -> false build failure)
S_HAVE=$'import Tiny.B\ntheorem foo : (2 : Nat) + 2 = 4 := by\n  have _fvw2 : True := trivial\n  have h := tinyB\n  rw [tinyA] at h\n'
A_HAVE2=$'theorem tinyA (n : Nat) : n + 0 = n := by\n  have _fvw3 : (3 : Nat) + 3 = 6 := rfl\n  rfl\n'
files "$W/order.files" Tiny/A.lean "$A_HAVE2" Solution.lean "$S_HAVE"
ask "$ST" order --files "$W/order.files" --mode optimistic; rc=$?
v=$(jq_ order 'r["verdict"], r["attempts"][0]["outcome"], r["attempts"][0]["build"].get("dirty")')
[ $rc = 0 ] && [ "$v" = "ACCEPTED cold0 None" ] && row PASS order "$v (--mode ignored by the cold path)" || row FAIL order "exit $rc: $v $(jq_ order 'r.get("why")')"
files "$W/sorry.files" Tiny/B.lean "$B_SORRY"
ask "$ST" sorry --files "$W/sorry.files"; rc=$?
v=$(jq_ sorry 'r["verdict"], "sorryAx" in (r.get("why") or "")')
[ $rc = 1 ] && [ "$v" = "REJECTED True" ] && row PASS sorry "$v" || row FAIL sorry "exit $rc: $v $(jq_ sorry 'r.get("why")')"
files "$W/break.files" Tiny/B.lean "$B_BREAK"
ask "$ST" break --files "$W/break.files"; rc=$?
v=$(jq_ break 'r["verdict"], r["attempts"][0]["outcome"], [d["module"] for d in r["attempts"][0].get("diagnostics", [])]')
[ $rc = 1 ] && case "$v" in "REJECTED cold1 []") true;; *) false;; esac && row PASS break "$v" || row FAIL break "exit $rc: $v"
files "$W/kbad.files" Tiny/B.lean "$B_KBAD" Solution.lean "$S_KBAD"
ask "$ST" kbad --files "$W/kbad.files"; rc=$?
v=$(jq_ kbad 'r["verdict"], r["attempts"][-1]["outcome"]')
[ $rc = 1 ] && case "$v" in "REJECTED cold1") true;; *) false;; esac && row PASS kbad "$v ($(jq_ kbad 'r.get("why")' | cut -c1-80))" || row FAIL kbad "exit $rc: $v"
files "$W/stmt.files" Tiny/B.lean "$B_ORIG"$'\n' Solution.lean "$S_STMT"
ask "$ST" stmt --files "$W/stmt.files"; rc=$?
v=$(jq_ stmt 'r["verdict"], "foo" in (r.get("why") or "")')
[ $rc = 1 ] && [ "$v" = "REJECTED True" ] && row PASS stmt "$v ($(jq_ stmt 'r.get("why")' | cut -c1-80))" || row FAIL stmt "exit $rc: $v $(jq_ stmt 'r.get("why")')"
files "$W/fixed.files" Tiny/A.lean "$A_ORIG"$'\n' Tiny/B.lean "$B_ORIG"$'\n' Solution.lean "$S_ORIG"$'\n'
ask "$ST" fixed --files "$W/fixed.files"; rc=$?
v=$(jq_ fixed 'r["verdict"]'); [ $rc = 0 ] && [ "$v" = ACCEPTED ] && row PASS fixed "$v" || row FAIL fixed "exit $rc: $v $(jq_ fixed 'r.get("why")')"
cp -r "$H/x/tiny" "$W/tree"; ask "$ST" tree --tree "$W/tree"; rc=$?
v=$(jq_ tree 'r["verdict"]'); [ $rc = 0 ] && [ "$v" = ACCEPTED ] && row PASS tree "$v" || row FAIL tree "exit $rc: $v $(jq_ tree 'r.get("why")')"
cp -r "$H/x/tiny" "$W/repo" && git -C "$W/repo" init -q && git -C "$W/repo" add -A && \
  git -C "$W/repo" -c user.email=t@t -c user.name=t commit -qm base
ask "$ST" git --git "$W/repo" --rev HEAD; rc=$?
v=$(jq_ git 'r["verdict"], r["source"]["kind"]'); [ $rc = 0 ] && [ "$v" = "ACCEPTED git" ] && row PASS git "$v" || row FAIL git "exit $rc: $v $(jq_ git 'r.get("why")')"
ask "$ST" badrev --git "$W/repo" "--rev=-o$W/injected.tar"; rc=$?
v=$(jq_ badrev 'r["verdict"]')
[ $rc = 2 ] && [ "$v" = NO-VERDICT ] && [ ! -e "$W/injected.tar" ] && row PASS badrev "$v (option-like rev refused)" || row FAIL badrev "exit $rc: $v"
files "$W/bad.files" ../escape.lean "theorem x : True := trivial"
ask "$ST" badpath --files "$W/bad.files"; rc=$?
v=$(jq_ badpath 'r["verdict"]'); alive=$(python3 -I "$FW" status --state "$ST" > /dev/null 2>&1 && echo alive || echo dead)
[ $rc = 2 ] && [ "$v" = NO-VERDICT ] && [ "$alive" = alive ] && [ ! -e "$ST/runs/escape.lean" ] && row PASS badpath "$v, daemon $alive" || row FAIL badpath "exit $rc: $v, daemon $alive"
mkdir -p "$W/outside" "$W/symbase/Tiny" "$W/symsrc/Evil"; ln -s "$W/outside" "$W/symbase/Evil"
printf 'theorem pwn : True := trivial\n' > "$W/symsrc/Evil/pwn.lean"; echo '{"write": ["Evil/pwn.lean"], "delete": []}' > "$W/sym.json"
python3 -I "$FV/tools/incr/incr-build.py" --base "$W/symbase" --base-plan /dev/null --src "$W/symsrc" --work "$W/symwork" \
  --packages "$W" --tc "$TC" --changed "$W/sym.json" --json "$W/symwork.json" > /dev/null 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("detail", ""))' "$W/symwork.json" 2>/dev/null)
[ $rc = 2 ] && [ -z "$(ls -A "$W/outside")" ] && case "$v" in *"bad path"*) true;; *) false;; esac \
  && row PASS symlink "exit 2: $v; nothing written outside" || row FAIL symlink "exit $rc: $v; outside: $(ls "$W/outside")"
# watch: an editor-style loop on a working tree (initial verdict, then a breaking save -> REJECTED with a file:line message)
cp -r "$H/x/tiny" "$W/wtree"
python3 -I "$FW" watch --state "$ST" --tree "$W/wtree" --interval 0.5 --initial > "$W/watch.out" 2>&1 & WP=$!
for i in $(seq 1 240); do grep -q 'watch #1\]' "$W/watch.out" && break; sleep 0.5; done
printf '%s' "$B_BREAK" > "$W/wtree/Tiny/B.lean"
for i in $(seq 1 240); do grep -q 'watch #2\]' "$W/watch.out" && break; sleep 0.5; done
kill $WP 2>/dev/null; wait $WP 2>/dev/null
w1=$(grep -o 'watch #1\] [A-Z-]*' "$W/watch.out" | head -1); w2=$(grep -o 'watch #2\] [A-Z-]*' "$W/watch.out" | head -1)
grep -q '^Tiny/B.lean:[0-9]*:[0-9]*: error' "$W/watch.out" && wd=diag || wd=nodiag
[ "$w1" = "watch #1] ACCEPTED" ] && [ "$w2" = "watch #2] REJECTED" ] && row PASS watch "$w1 / $w2, $wd (cold path: no per-module diagnostics)" \
  || row FAIL watch "$w1 / $w2 / $wd ($(tail -3 "$W/watch.out" | tr '\n' ' '))"
w=$(grep -h -o '"warm": true' "$W"/have.json "$W"/sorry.json "$W"/kbad.json "$W"/stmt.json "$W"/fixed.json "$W"/tree.json "$W"/git.json 2>/dev/null | wc -l)
c=$(grep -l '"mode": "cold"' "$W"/have.json "$W"/sorry.json "$W"/kbad.json "$W"/stmt.json "$W"/fixed.json "$W"/tree.json "$W"/git.json 2>/dev/null | wc -l)
[ "$w" = 0 ] && [ "$c" = 7 ] && row PASS warm "cold path: $c of 7 requests answered by bin/fastverify, no pre-warmed leg" || row FAIL warm "$w warm, $c cold of 7"
stop "$ST"
# ---- concurrency: two candidates judged at once against the same base, base not advanced
ST2=$W/st2; init "$ST2" && serve "$ST2" --jobs 2 --warm 0 --threads "$T" || row FAIL concurrent "init/serve"
B_ALT=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  simp\n'
files "$W/c1.files" Tiny/A.lean "$A_HAVE"; files "$W/c2.files" Tiny/B.lean "$B_ALT"
b0=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["run"])' "$ST2/base.json")
ask "$ST2" c1 --files "$W/c1.files" --no-advance & p1=$!
ask "$ST2" c2 --files "$W/c2.files" --no-advance & p2=$!
wait $p1; r1=$?; wait $p2; r2=$?
b1=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["run"])' "$ST2/base.json")
ov=$(python3 -I - "$W/c1.json" "$W/c2.json" <<'EOF'
import json, sys
a, b = (json.load(open(p)) for p in sys.argv[1:3])
# the two requests overlapped in time (both started before either finished)
print("overlap" if a["queue_s"] < 1 and b["queue_s"] < 1 else "serial")
EOF
)
[ $r1 = 0 ] && [ $r2 = 0 ] && [ "$b0" = "$b1" ] && row PASS concurrent "both ACCEPTED, base unchanged ($b0), $ov" \
  || row FAIL concurrent "exits $r1/$r2, base $b0 -> $b1, $(jq_ c2 'r.get("why")')"
stop "$ST2"
# ---- --copy-mode farm: sparse candidates get a symlink farm over the fixed base (no tree copy); the base is untouched
ST8=$W/st8; init "$ST8" && serve "$ST8" --warm 0 --threads "$T" --copy-mode farm $XINC || row FAIL farm "init/serve"
bp=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["proj"])' "$ST8/base.json")
h0=$(cd "$bp" && find . -type f -o -type l | LC_ALL=C sort | xargs -d '\n' sha256sum 2>/dev/null | sha256sum | cut -c1-16)
ask "$ST8" f1 --files "$W/c1.files" --no-advance; r1=$?
ask "$ST8" f2 --files "$W/sorry.files" --no-advance; r2=$?
ask "$ST8" f3 --files "$W/kbad.files" --no-advance; r3=$?
h1=$(cd "$bp" && find . -type f -o -type l | LC_ALL=C sort | xargs -d '\n' sha256sum 2>/dev/null | sha256sum | cut -c1-16)
cm=$(python3 -I -c 'import json,glob,sys; print(" ".join(sorted({json.load(open(f)).get("copy_mode","?") for f in glob.glob(sys.argv[1] + "/runs/*/a*.build.json")})))' "$ST8")
[ $r1 = 0 ] && [ $r2 = 1 ] && [ $r3 = 1 ] && [ "$h0" = "$h1" ] && [ "$cm" = farm ] \
  && row PASS farm "candidates ACCEPTED / REJECTED (sorry) / REJECTED (kernel), copy_mode $cm, base tree unchanged" \
  || row FAIL farm "exits $r1/$r2/$r3, copy_mode '$cm', base $h0 -> $h1 ($(jq_ f1 'r.get("why")'))"
stop "$ST8"
# ---- --guard: resource limits on the untrusted build (fvguard): an elaboration that sleeps past the wall limit
# must end in NO-VERDICT (never a verdict) and the daemon must stay alive
if [ -f "$FV/tools/guard/fvguard.py" ]; then
  ST5=$W/st5; init "$ST5" && serve "$ST5" --warm 0 --threads "$T" --guard "wall=25,procs=4096" || row FAIL guard "init/serve"
  B_SLEEP=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 := by\n  sleep 90000\n  rw [tinyA]\n'
  files "$W/guard.files" Tiny/B.lean "$B_SLEEP"
  ask "$ST5" guard --files "$W/guard.files"; rc=$?
  v=$(jq_ guard 'r["verdict"], r["attempts"][0]["build"].get("guard_violation")')
  alive=$(python3 -I "$FW" status --state "$ST5" > /dev/null 2>&1 && echo alive || echo dead)
  [ $rc = 2 ] && [ "$v" = "NO-VERDICT wall" ] && [ "$alive" = alive ] && row PASS guard "$v ($(jq_ guard 'r["total_s"]') s), daemon $alive" \
    || row FAIL guard "exit $rc: $v, daemon $alive"
  stop "$ST5"
else
  row SKIP guard "tools/guard/fvguard.py not available"
fi
# ---- --build lake: the official incremental lake build + the release's official exporter (any supported release)
ST4=$W/st4
python3 -I "$FW" init --state "$ST4" --project "$H/x/tiny" --challenge "$W/ch" --challenge-sha256 "$CSHA" $CMPIN --threads "$T" \
  --fv "$FV" --tc "$TC" ${WS:+--packages "$WS"} --build lake > "$ST4.init.log" 2>&1 && serve "$ST4" --warm 1 --threads "$T" $XINC \
  || row FAIL lake-init "$(tail -2 "$ST4.init.log")"
if [ -S "$ST4/sock" ]; then
  sleep 2
  ask "$ST4" lake-have --files "$W/have.files"; rc=$?
  v=$(jq_ lake-have 'r["verdict"], r["attempts"][0]["mode"]')
  [ $rc = 0 ] && [ "$v" = "ACCEPTED lake" ] && row PASS lake-have "$v ($(jq_ lake-have 'r["build_s"], r["export_s"], r["check_s"]'))" || row FAIL lake-have "exit $rc: $v $(jq_ lake-have 'r.get("why")')"
  ask "$ST4" lake-sorry --files "$W/sorry.files"; rc=$?
  v=$(jq_ lake-sorry 'r["verdict"], "sorryAx" in (r.get("why") or "")')
  [ $rc = 1 ] && [ "$v" = "REJECTED True" ] && row PASS lake-sorry "$v" || row FAIL lake-sorry "exit $rc: $v $(jq_ lake-sorry 'r.get("why")')"
  ask "$ST4" lake-break --files "$W/break.files"; rc=$?
  v=$(jq_ lake-break 'r["verdict"], r["attempts"][0]["outcome"], len(r["attempts"][0].get("diagnostics", [])) > 0')
  [ $rc = 1 ] && [ "$v" = "REJECTED build1 True" ] && row PASS lake-break "$v" || row FAIL lake-break "exit $rc: $v"
  ask "$ST4" lake-fixed --files "$W/fixed.files"; rc=$?
  v=$(jq_ lake-fixed 'r["verdict"]'); [ $rc = 0 ] && [ "$v" = ACCEPTED ] && row PASS lake-fixed "$v" || row FAIL lake-fixed "exit $rc: $v $(jq_ lake-fixed 'r.get("why")')"
  stop "$ST4"
fi
# ---- another release's trusted check (check-sound v3 --pins FILE); here the default pins given explicitly
if grep -q -- '--pins)' "$FV/check/sound/check-sound-svc.sh" 2>/dev/null; then
  ST7=$W/st7; init "$ST7" && serve "$ST7" --threads "$T" --pins "$FV/check/sound/pins.env" || row FAIL pins "init/serve"
  ask "$ST7" p1 --files "$W/have.files" --no-advance; rc=$?
  ask "$ST7" p2 --files "$W/sorry.files" --no-advance; rc2=$?
  v=$(jq_ p1 'r["verdict"], any(a.get("warm") for a in r["attempts"])'); v2=$(jq_ p2 'r["verdict"]')   # (cold path: no warm leg)
  [ $rc = 0 ] && [ "$v" = "ACCEPTED False" ] && [ $rc2 = 1 ] && [ "$v2" = REJECTED ] && row PASS pins "$v / $v2" \
    || row FAIL pins "exit $rc: $v / exit $rc2: $v2 $(jq_ p1 'r.get("why")')"
  stop "$ST7"
else
  row SKIP pins "check-sound-svc.sh has no --pins (the v3 wiring with --pins is not published)"
fi
# ---- warm check backend (check/warm/fvcheckd.py sidecar), if published
if [ -f "$FV/check/warm/fvcheckd.py" ]; then
  ST6=$W/st6; init "$ST6" && serve "$ST6" --warm 0 --threads "$T" --check warm $XINC || row FAIL warm-backend "init/serve"
  for i in $(seq 1 240); do python3 -I "$FW" status --state "$ST6" 2>/dev/null | grep -q '"warmd": {"ready": true' && break; sleep 1; done
  ask "$ST6" wb-have --files "$W/have.files" --no-advance; rc=$?
  v=$(jq_ wb-have 'r["verdict"], r["attempts"][-1]["outcome"]')
  ask "$ST6" wb-kbad --files "$W/kbad.files" --no-advance; rc2=$?
  v2=$(jq_ wb-kbad 'r["verdict"], r["attempts"][-1]["outcome"]')
  ask "$ST6" wb-sorry --files "$W/sorry.files" --no-advance; rc3=$?
  v3=$(jq_ wb-sorry 'r["verdict"], r["attempts"][-1]["outcome"]')
  [ $rc = 0 ] && case "$v" in "ACCEPTED check0-warmd"*) true;; *) false;; esac && [ $rc2 = 1 ] \
    && case "$v2" in "REJECTED check1"*) true;; *) false;; esac && [ $rc3 = 1 ] && case "$v3" in "REJECTED"*) true;; *) false;; esac \
    && row PASS warm-backend "$v / $v2 / $v3" || row FAIL warm-backend "exit $rc: $v / exit $rc2: $v2 / exit $rc3: $v3 ($(tail -2 "$ST6/warmd.log" 2>/dev/null | tr '\n' ' '))"
  # warm DELTA path (4.33.1 base): the valid edit was judged from the rebuilt module's delta, without a full export
  d=$(jq_ wb-have 'r["attempts"][0].get("warmdelta", {}).get("verdict"), r["attempts"][0].get("export_bytes") is None')
  [ "$d" = "ACCEPTED True" ] && row PASS warm-delta "valid edit ACCEPTED by check_delta ($(jq_ wb-have 'r["attempts"][0]["warmdelta"].get("modules"), r["attempts"][0]["warmdelta"].get("delta_bytes"), r["attempts"][0]["warmdelta"].get("check_s")')), no full export" \
    || row FAIL warm-delta "warmdelta: $d $(jq_ wb-have 'r["attempts"][0].get("warmdelta")')"
  # tier 2: the sorry edit references sorryAx, absent from the base export -> the transitive delta minus the base's names
  d2=$(jq_ wb-sorry 'r["attempts"][0].get("warmdelta", {}).get("tier2_verdict"), "sorryAx" in str(r["attempts"][0].get("warmdelta", {}).get("tier2_reason"))')
  [ "$d2" = "REJECTED True" ] && row PASS warm-delta-t2 "sorry edit REJECTED (sorryAx) by check_delta after the tier-2 delta" \
    || row FAIL warm-delta-t2 "$(jq_ wb-sorry 'r["attempts"][0].get("warmdelta")')"
  # delta drift (exphash statement hashes of the delta vs the base): proof-only edit = value-changed, 0 statement changes;
  # a restated target = STATEMENT-CHANGED (and the delta check REJECTS it)
  ask "$ST6" wb-hdrift --files "$W/have.files" --no-advance --drift; rc=$?
  ask "$ST6" wb-sdrift --files "$W/stmt.files" --no-advance --drift; rc2=$?
  v=$(jq_ wb-hdrift 'r["verdict"], r.get("drift", {}).get("statement_changed"), "tinyA" in str(r.get("drift", {}).get("names", {}).get("value-changed"))')
  v2=$(jq_ wb-sdrift 'r["verdict"], r.get("drift", {}).get("statement_changed"), "foo" in str(r.get("drift", {}).get("names", {}).get("STATEMENT-CHANGED"))')
  [ $rc = 0 ] && [ "$v" = "ACCEPTED 0 True" ] && [ $rc2 = 1 ] && [ "$v2" = "REJECTED 1 True" ] \
    && row PASS delta-drift "proof edit: $v / restated target: $v2 ($(jq_ wb-hdrift 'r.get("drift", {}).get("tool")'))" \
    || row FAIL delta-drift "exit $rc: $v / exit $rc2: $v2 $(jq_ wb-sdrift 'r.get("drift")')"
  stop "$ST6"
else
  row SKIP warm-backend "check/warm/fvcheckd.py not published"
fi
# ---- frontier mode (the conditional check), if available
if [ -x "$FV/check/frontier/check-frontier.sh" ] && "$FV/check/frontier/check-frontier.sh" --preflight > "$W/frontier-preflight.log" 2>&1; then
  ST3=$W/st3; init "$ST3" && serve "$ST3" --warm 0 --threads "$T" --check frontier $XINC || row FAIL frontier "init/serve"
  files "$W/f1.files" Tiny/B.lean "$B_FSORRY"
  ask "$ST3" f1 --files "$W/f1.files"; rc=$?
  v=$(jq_ f1 'r["verdict"], [e["name"] for e in r.get("frontier", [])], r.get("ledger", {}).get("new_since_base"), [(e.get("source") or {}).get("file") for e in r.get("frontier", [])]')
  [ $rc = 3 ] && [ "$v" = "CONDITIONAL ['tinyB'] ['tinyB'] ['Tiny/B.lean']" ] && row PASS frontier-open "$v" || row FAIL frontier-open "exit $rc: $v $(jq_ f1 'r.get("why")')"
  # the same frontier again as a candidate: check A is skipped through check-frontier.sh --a-cache (fvwork's private dir)
  ask "$ST3" f1b --files "$W/f1.files" --no-advance; rc=$?
  ac=$(python3 -I -c 'import json,glob,sys; r=json.load(open(sys.argv[1])); f=glob.glob(sys.argv[2] + "/runs/%05d/x/solution*.export.check.json" % r["id"]); c=json.load(open(f[-1])) if f else {}; print(r["verdict"], ((c.get("checks") or {}).get("A") or {}).get("cached"))' "$W/f1b.json" "$ST3" 2>/dev/null)
  [ $rc = 3 ] && [ "$ac" = "CONDITIONAL True" ] && row PASS frontier-acache "same frontier again: CONDITIONAL, check A from --a-cache" || row FAIL frontier-acache "exit $rc: $ac"
  # pinned frontier (goalposts fixed): pin the open lemma's statement from f1's export, then an agent restates the open
  # lemma (a different statement that still builds) -> REJECTED with the pin, CONDITIONAL without it
  FX=$(jq_ f1 'r["export"]')
  python3 -I "$FV/tools/frontier/frontier.py" pin "$FX" "$W/ch/challenge.export" "$W/ch/comparator.json" "$W/pin" > "$W/pin.log" 2>&1
  stop "$ST3"; serve "$ST3" --warm 0 --threads "$T" --check frontier --pinned "$W/pin" $XINC || row FAIL frontier-pinned "serve"
  B_RESTATE=$'import Tiny.A\ntheorem tinyB : (2 : Nat) + 2 + 0 = 4 + 0 := by\n  sorry\n'
  S_RESTATE=$'import Tiny.B\ntheorem foo : (2 : Nat) + 2 = 4 := by\n  have h := tinyB\n  simpa using h\n'
  files "$W/f3.files" Tiny/B.lean "$B_RESTATE" Solution.lean "$S_RESTATE"
  ask "$ST3" f3 --files "$W/f3.files" --no-advance; rc=$?
  v=$(jq_ f3 'r["verdict"]')
  [ -d "$W/pin" ] && [ $rc = 1 ] && [ "$v" = REJECTED ] && row PASS frontier-pinned "restated open lemma $v with the pin ($(jq_ f3 'r.get("why")' | cut -c1-70))" \
    || row FAIL frontier-pinned "exit $rc: $v $(jq_ f3 'r.get("why")') (pin: $(tail -1 "$W/pin.log"))"
  files "$W/f2.files" Tiny/B.lean "$B_ORIG"$'\n' Solution.lean "$S_ORIG"$'\n'
  ask "$ST3" f2 --files "$W/f2.files"; rc=$?
  v=$(jq_ f2 'r["verdict"], r.get("ledger", {}).get("closed_since_base")')
  [ $rc = 0 ] && [ "$v" = "ACCEPTED ['tinyB']" ] && row PASS frontier-closed "$v" || row FAIL frontier-closed "exit $rc: $v $(jq_ f2 'r.get("why")')"
  stop "$ST3"
else
  row SKIP frontier "check/frontier/check-frontier.sh not available or its preflight failed"
fi
[ $fails = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL ($fails)"
[ $fails = 0 ]

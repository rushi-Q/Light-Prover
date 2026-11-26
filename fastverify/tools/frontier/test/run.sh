#!/bin/bash
# tools/frontier/test/run.sh [WORK] : regression + adversarial tests of tools/frontier. Core-only projects (no Mathlib),
# official Lean 4.33.1 build/export via bin/fastverify --preset sound, then frontier.py. Prints PASS/FAIL rows, RESULT.
#   * 14 source cases (test/gen.py): honest decompositions, proved, sorry in target / definition, False frontier, changed
#     statement, project axiom (rejected / allowed with --axioms), nested open lemmas, universe-polymorphic + inductive,
#     odd names, incomplete explicit list, frontier statement over a sorry'd definition, native_decide.
#   * pinned flow: pin c01's frontier; the same project -> modulo frontier; L1 proved -> ACCEPTED (closed); L1's statement
#     weakened -> REJECTED; a new open lemma outside the pin -> REJECTED.
#   * fault injection (the untrusted parts lie): a frontier challenge minted from a FORGED challenge (target statement
#     changed) -> check 'compare' rejects -> no acceptance although check 'main' accepts; a rewrite that axiomatizes an
#     extra (proved) theorem not in the frontier list -> REJECTED (on the original export, and on the prepared redirect S'
#     itself); a frontier challenge with an extra declaration duplicating a challenge constant -> no acceptance.
#   run437.sh = the same suite on Lean 4.37.0-rc1 through bin/fastverify --pins check/sound/pins-437.env --modulo-frontier.
# WORK (default $FV_SCRATCH/$USER-frontier-test) must lie outside /tmp, /home, /var and /run (hidden in the check's sandbox).
# FV_PACKAGES = the trusted Lake workspace with materialized dependencies (default <repository root>/verify/challenge).
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FR=$(dirname "$HERE")/frontier.py
export FASTVERIFY_ROOT=${FASTVERIFY_ROOT:-$(cd "$HERE/../../.." && pwd)}
[ -x "$FASTVERIFY_ROOT/bin/fastverify" ] || FASTVERIFY_ROOT=$LIGHT_LEAN/fastverify
W=${1:-${FV_SCRATCH:?node-local work root outside /tmp, /home, /var, /run (required unless WORK is given)}/$USER-frontier-test}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-4}; J=${JOBS:-8}
WS=${FV_PACKAGES:-$(dirname "$FASTVERIFY_ROOT")/verify/challenge}   # trusted Lake workspace (default: <repository root>/verify/challenge)
[ -d "$WS" ] || { echo "FAIL no trusted package workspace at $WS: set FV_PACKAGES"; echo "RESULT FAIL"; exit 1; }
CASES=$(python3 -I "$HERE/gen.py" "$W")
python3 -I "$FASTVERIFY_ROOT/tools/claims.py" pin "$W/chroot" "$WS" "$W/given" ch > "$W/pin.log" 2>&1 || { echo "FAIL pin challenge"; echo "RESULT FAIL"; exit 1; }
CH=$W/given/ch; SHA=$(cut -d' ' -f1 "$CH/challenge.export.sha256"); CSHA=$(sha256sum "$CH/comparator.json" | cut -d' ' -f1)   # comparator pin
bad=0
runcase() {  # runcase ID
  local id=$1 args
  args=$(python3 -I -c 'import json,sys; print(" ".join(json.load(open(sys.argv[1]))["args"]))' "$W/cases/$id/expect.json")
  python3 -I "$FR" run "$W/cases/$id/proj" "$CH" "$W/out/$id" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" $args > "$W/cases/$id/run.log" 2>&1
  echo $? > "$W/cases/$id/rc"
}
mkdir -p "$W/out"
n=0
for id in $CASES; do runcase "$id" & n=$((n+1)); if [ $n -ge "$J" ]; then wait -n; n=$((n-1)); fi; done; wait
for id in $CASES; do
  r=$(python3 -I - "$W/cases/$id/expect.json" "$W/out/$id/verdict.json" "$(cat "$W/cases/$id/rc")" <<'PY'
import json, sys
e = json.load(open(sys.argv[1]))
try:
    v = json.load(open(sys.argv[2]))
except Exception as x:
    print("FAIL no verdict.json (%s)" % x); sys.exit()
rc = int(sys.argv[3])
want_rc = {"ACCEPTED": 0, "REJECTED": 1, "CONDITIONAL": 3}.get(e["verdict"], 2)
# frontier v2: a redirected open lemma L is reported as the hypothesis L._fv_frontier_axiom -> compare lemma names
fr = sorted((f.get("lemma") or f["name"]).replace("._fv_frontier_axiom", "") for f in v.get("frontier", []))
ok = v["verdict"] == e["verdict"] and rc == want_rc and (e["frontier"] is None or fr == sorted(e["frontier"]))
print("%s verdict=%s rc=%d frontier=%s (expected %s %s) %s" % ("PASS" if ok else "FAIL", v["verdict"], rc, fr, e["verdict"],
      e["frontier"], (v.get("why") or "")[:160]))
PY
)
  echo "${r%% *} frontier $id ${r#* }"; case "$r" in PASS*) ;; *) bad=1;; esac
done

# ---------- pinned flow ----------
P=$W/pinned; mkdir -p "$P"
python3 -I "$FR" pin "$W/out/c01-one-open/fv/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$P/pin" --threads "$T" > "$P/pin.log" 2>&1
[ $? = 3 ] && [ -f "$P/pin/frontier.json" ] && echo "PASS frontier pin c01 (exit 3, pinned)" || { echo "FAIL frontier pin c01: $(tail -3 "$P/pin.log")"; bad=1; }
pinrun() {  # pinrun LABEL PROJECT_SOURCE_VARIANT EXPECTED_VERDICT
  local lab=$1 src=$2 want=$3 d=$P/$1
  mkdir -p "$d"; cp -a "$W/cases/c01-one-open/proj" "$d/proj"; printf '%s' "$src" > "$d/proj/Solution.lean"
  python3 -I "$FR" run "$d/proj" "$CH" "$d/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" --pinned "$P/pin" > "$d/run.log" 2>&1
  local rc=$? v; v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], ",".join(v.get("frontier_closed") or []) or "-", (v.get("why") or "")[:120])' "$d/out/verdict.json" 2>/dev/null)
  if [ "${v%% *}" = "$want" ]; then echo "PASS frontier pinned/$lab: $v (rc $rc)"; else echo "FAIL frontier pinned/$lab: got '$v' rc $rc, expected $want"; bad=1; fi
}
BASE=$(python3 -I -c 'import sys; sys.path.insert(0,sys.argv[1]); import gen; print(gen.BASE_DEFS)' "$HERE")
L2=$(python3 -I -c 'import sys; sys.path.insert(0,sys.argv[1]); import gen; print(gen.L2)' "$HERE")
TAIL='theorem main : ∀ n, P n := fun n => (L2 n).2 (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
'
pinrun same "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := sorry
$L2
$TAIL" CONDITIONAL
pinrun closed "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := Nat.zero_add n
$L2
$TAIL" ACCEPTED
# the open lemma's statement drifts (Q redefined to something trivial, L1 still sorry): must be REJECTED against the pin
pinrun drift-def "$BASE
def Q (n : Nat) : Prop := 0 + n = n ∨ True
theorem L1 (n : Nat) : Q n := sorry
theorem L2' (n : Nat) : Q n → P n := fun _ => rfl
theorem main : ∀ n, P n := fun n => L2' n (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
" REJECTED
pinrun drift-stmt "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : P n := sorry
theorem main : ∀ n, P n := fun n => L1 n
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
" REJECTED
pinrun new-open "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := sorry
theorem L9 (p : Pt) : Good p := sorry
$L2
theorem main : ∀ n, P n := fun n => (L2 n).2 (L1 n)
theorem main2 : ∀ p : Pt, Good p := L9
" REJECTED

# ---------- fault injection: the untrusted parts lie ----------
X=$W/faults; mkdir -p "$X"
# (1) frontier challenge minted from a FORGED challenge whose target statement equals c06's changed statement
mkdir -p "$X/fchroot"; cp -a "$W/chroot/ch" "$X/fchroot/ch"
sed -i 's/^theorem main : ∀ n, P n := by sorry/def Q (n : Nat) : Prop := 0 + n = n\ntheorem main : ∀ n, Q n := by sorry/' "$X/fchroot/ch/Challenge.lean"
python3 -I "$FASTVERIFY_ROOT/tools/claims.py" pin "$X/fchroot" "$WS" "$X/fgiven" ch > "$X/fpin.log" 2>&1
python3 -I "$FR" prepare "$W/out/c06-statement-changed/fv/solution.export" "$X/fgiven/ch/challenge.export" "$CH/comparator.json" "$X/f1" > "$X/f1.prep.log" 2>&1
python3 -I - "$X/f1/frontier.json" "$CH/challenge.export" <<'PY'
import json, sys, hashlib
p = sys.argv[1]; j = json.load(open(p))
j["challenge_export"] = sys.argv[2]; j["challenge_sha256"] = hashlib.sha256(open(sys.argv[2], "rb").read()).hexdigest()
json.dump(j, open(p, "w"))
PY
python3 -I "$FR" check "$X/f1" --threads "$T" > "$X/f1.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], v["checks"]["main"]["verdict"], v["checks"]["compare"]["verdict"])' "$X/f1/verdict.json" 2>/dev/null)
case "$v" in "NO_VERDICT ACCEPTED REJECTED") echo "PASS frontier fault/forged-challenge: $v (main accepted the forged pair, compare caught it; rc $rc)";;
  *) echo "FAIL frontier fault/forged-challenge: '$v' rc $rc"; bad=1;; esac
# (2) a rewrite that axiomatizes an extra theorem (L2, proved) that is not in the permitted list
python3 -I "$FR" prepare "$W/out/c01-one-open/fv/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$X/f2" > "$X/f2.prep.log" 2>&1
python3 -I - "$X/f2/solution.frontier.export" "$W/out/c01-one-open/fv/solution.export" <<'PY'
import json, sys
sys.path.insert(0, __import__("os").environ["FRDIR"]) if False else None
dst, src = sys.argv[1], sys.argv[2]
names = {0: ""}
out = []
for raw in open(src, "rb"):
    if raw.startswith(b'{"in":'):
        o = json.loads(raw); k = "str" if "str" in o else "num"
        names[o["in"]] = (o[k]["pre"], str(o[k]["str"] if k == "str" else o[k]["i"]))
    if raw.startswith(b'{"thm":'):
        o = json.loads(raw)["thm"]
        n, i = [], o["name"]
        while i: n.append(names[i][1]); i = names[i][0]
        nm = ".".join(reversed(n))
        if nm in ("L1", "L2"):
            raw = (json.dumps({"axiom": {"isUnsafe": False, "levelParams": o["levelParams"], "name": o["name"], "type": o["type"]}}, separators=(",", ":"), sort_keys=True) + "\n").encode()
    out.append(raw)
open(dst, "wb").write(b"".join(out))
PY
python3 -I - "$X/f2/frontier.json" "$X/f2/solution.frontier.export" <<'PY'
import json, sys, hashlib
j = json.load(open(sys.argv[1])); json.dump(j, open(sys.argv[1], "w"))
PY
python3 -I "$FR" check "$X/f2" --threads "$T" > "$X/f2.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], (v.get("why") or "")[:100])' "$X/f2/verdict.json" 2>/dev/null)
case "$v" in REJECTED*) echo "PASS frontier fault/extra-axiom: $v (rc $rc)";; *) echo "FAIL frontier fault/extra-axiom: '$v' rc $rc"; bad=1;; esac
# (2b) the same lie against the REDIRECT rewrite (v2.1+, where S' keeps L1 as a theorem whose value is the fresh axiom
#      L1._fv_frontier_axiom): take the prepared S' itself and turn the proved L2 into an axiom -> REJECTED naming L2
python3 -I "$FR" prepare "$W/out/c01-one-open/fv/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$X/f2b" > "$X/f2b.prep.log" 2>&1
python3 -I - "$X/f2b/solution.frontier.export" <<'PY'
import json, sys
p = sys.argv[1]; names = {0: ""}; out = []; hit = 0
for raw in open(p, "rb"):
    if raw.startswith(b'{"in":'):
        o = json.loads(raw); k = "str" if "str" in o else "num"
        names[o["in"]] = (o[k]["pre"], str(o[k]["str"] if k == "str" else o[k]["i"]))
    if raw.startswith(b'{"thm":'):
        o = json.loads(raw)["thm"]; n, i = [], o["name"]
        while i: n.append(names[i][1]); i = names[i][0]
        if ".".join(reversed(n)) == "L2":
            raw = (json.dumps({"axiom": {"isUnsafe": False, "levelParams": o["levelParams"], "name": o["name"], "type": o["type"]}}, separators=(",", ":"), sort_keys=True) + "\n").encode(); hit += 1
    out.append(raw)
assert hit == 1, hit
open(p, "wb").write(b"".join(out))
PY
python3 -I "$FR" check "$X/f2b" --threads "$T" > "$X/f2b.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], (v.get("why") or "")[:100])' "$X/f2b/verdict.json" 2>/dev/null)
case "$v" in REJECTED*L2*) echo "PASS frontier fault/extra-axiom-redirect: $v (rc $rc)";; *) echo "FAIL frontier fault/extra-axiom-redirect: '$v' rc $rc"; bad=1;; esac
# (3) a frontier challenge with an appended duplicate of a challenge constant (P redefined as True)
python3 -I "$FR" prepare "$W/out/c01-one-open/fv/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$X/f3" > "$X/f3.prep.log" 2>&1
python3 -I - "$X/f3" <<'PY'
import json, sys, hashlib, os
d = sys.argv[1]; cp = os.path.join(d, "frontier", "challenge.export")
lines = open(cp, "rb").read().splitlines(keepends=True)
names = {}; mi = me = 0; pidx = None; true_e = None
for raw in lines:
    o = json.loads(raw)
    if "in" in o:
        mi = max(mi, o["in"])
        if "str" in o and o["str"]["pre"] == 0 and o["str"]["str"] == "P": pidx = o["in"]
        if "str" in o and o["str"]["pre"] == 0 and o["str"]["str"] == "True": tidx = o["in"]
    if "ie" in o:
        me = max(me, o["ie"])
        if "const" in o and o["const"]["name"] == tidx if 'tidx' in dir() else False: true_e = o["ie"]
# type of P: Nat -> Prop  (reuse P's own type index); value: fun _ => True
ptype = None
for raw in lines:
    o = json.loads(raw)
    if "def" in o and o["def"]["name"] == pidx: ptype = o["def"]["type"]; pdef = o["def"]
    if "const" in o and o["const"]["name"] == tidx: true_e = o["ie"]
natc = [json.loads(r) for r in lines if b'"forallE"' in r and json.loads(r)["ie"] == ptype][0]["forallE"]["type"]
add = [{"ie": me + 1, "lam": {"binderInfo": "default", "body": true_e, "name": pdef["name"], "type": natc}},
       {"def": dict(pdef, value=me + 1)}]
with open(cp, "ab") as f:
    for o in add: f.write((json.dumps(o, separators=(",", ":"), sort_keys=True) + "\n").encode())
j = json.load(open(os.path.join(d, "frontier.json")))
j["frontier_challenge_sha256"] = hashlib.sha256(open(cp, "rb").read()).hexdigest()
json.dump(j, open(os.path.join(d, "frontier.json"), "w"))
PY
python3 -I "$FR" check "$X/f3" --threads "$T" > "$X/f3.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], v["checks"]["main"]["verdict"], v["checks"]["compare"]["verdict"])' "$X/f3/verdict.json" 2>/dev/null)
case "$v" in ACCEPTED*) echo "FAIL frontier fault/duplicate-constant: '$v' rc $rc"; bad=1;; *) echo "PASS frontier fault/duplicate-constant: $v (no acceptance; rc $rc)";; esac
# comparator.json swapped DURING the build: frontier.py read it once (OUT/pinned) and passed
# that copy to bin/fastverify; the swap changes nothing - c03 (sorry in the target) stays REJECTED, the judged configuration
# is the pinned one (without that rule: frontier ACCEPTED, exit 0, judging the swapped theorem_names ["main2"])
SW=$W/swap; rm -rf "$SW"; mkdir -p "$SW"; cp -a "$CH" "$SW/ch"
SWCSHA=$(sha256sum "$SW/ch/comparator.json" | cut -d' ' -f1)
python3 -I "$FR" run "$W/cases/c03-sorry-in-target/proj" "$SW/ch" "$SW/out" --challenge-sha256 "$SHA" --comparator-sha256 "$SWCSHA" --threads "$T" > "$SW/run.log" 2>&1 &
SWPID=$!
for _ in $(seq 1 600); do [ -f "$SW/out/pinned/comparator.json" ] && break; sleep 0.2; done
python3 -I - "$SW/ch/comparator.json" <<'PY'
import json, os, sys
p = sys.argv[1]; c = json.load(open(p)); c["theorem_names"] = ["main2"]
json.dump(c, open(p + ".new", "w")); os.replace(p + ".new", p)
PY
wait $SWPID; rc=$?
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$SW/out/verdict.json" 2>/dev/null)
tn=$(python3 -I -c 'import json,sys; print(",".join(json.load(open(sys.argv[1]))["theorem_names"]))' "$SW/out/pinned/comparator.json" 2>/dev/null)
if [ "$rc" != 0 ] && [ "$v" != ACCEPTED ] && [ "$tn" != main2 ]; then echo "PASS frontier swap/comparator-during-build: $v rc $rc (pinned theorem_names $tn)"
else echo "FAIL frontier swap/comparator-during-build: $v rc $rc (pinned theorem_names $tn) $(tail -c 200 "$SW/run.log")"; bad=1; fi
# a retry in the SAME OUT never judges an earlier run's artefacts: (a) the child fails
# (bad EXTRA value: bin/fastverify exits 2 before writing anything) after an ACCEPTED run -> NO_VERDICT exit 2, the old
# OUT/fv is gone (without that rule: the old solution.export went through the frontier path -> ACCEPTED exit 0); (b) an honest
# retry in the same OUT is judged afresh (ACCEPTED, exit 0)
RT=$W/retry; rm -rf "$RT"; mkdir -p "$RT"; cp -a "$W/out/c02-proved" "$RT/out"
python3 -I "$FR" run "$W/cases/c02-proved/proj" "$CH" "$RT/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" -- --official-timeout notanumber > "$RT/a.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$RT/out/verdict.json" 2>/dev/null)
if [ "$rc" = 2 ] && [ "$v" = NO_VERDICT ] && [ ! -e "$RT/out/fv/result.json" ]; then echo "PASS frontier retry/child-failed-same-out: NO_VERDICT rc 2 (old export not judged)"
else echo "FAIL frontier retry/child-failed-same-out: $v rc $rc $(tail -c 200 "$RT/a.log")"; bad=1; fi
python3 -I "$FR" run "$W/cases/c02-proved/proj" "$CH" "$RT/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$RT/b.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$RT/out/verdict.json" 2>/dev/null)
if [ "$rc" = 0 ] && [ "$v" = ACCEPTED ]; then echo "PASS frontier retry/honest-same-out: ACCEPTED rc 0 (judged afresh)"
else echo "FAIL frontier retry/honest-same-out: $v rc $rc $(tail -c 200 "$RT/b.log")"; bad=1; fi
# verify with both pins judges the private pinned copies (OUTDIR/pinned) and gives the same verdict as run
VF=$W/verify-pinned; rm -rf "$VF"
python3 -I "$FR" verify "$W/out/c01-one-open/fv/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$VF" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$VF.log" 2>&1; rc=$?
cc=$(python3 -I -c 'import json,sys; i=json.load(open(sys.argv[1])); print(i["challenge_export"].endswith("/pinned/challenge.export") and i["comparator_config"].endswith("/pinned/comparator.json"))' "$VF/frontier.json" 2>/dev/null)
if [ "$rc" = 3 ] && [ "$cc" = True ]; then echo "PASS frontier verify/pinned-copies: CONDITIONAL rc 3, judged OUTDIR/pinned copies"
else echo "FAIL frontier verify/pinned-copies: rc $rc pinned-copies $cc $(tail -c 200 "$VF.log")"; bad=1; fi
# SIGTERM during the build: NO_VERDICT exit 2 (not 143), bin/fastverify's process group
# is killed (nothing keeps writing into OUT/fv), no verdict.json
SG=$W/signal; rm -rf "$SG"; mkdir -p "$SG"
python3 -I "$FR" run "$W/cases/c01-one-open/proj" "$CH" "$SG/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$SG/run.log" 2>&1 &
SGP=$!
for _ in $(seq 1 600); do [ -d "$SG/out/fv" ] && break; sleep 0.1; done; sleep 1
kill -TERM $SGP; wait $SGP; rc=$?; sleep 1
left=$(pgrep -f "$SG/out" | wc -l)
v=$(tail -1 "$SG/run.log" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("verdict"))' 2>/dev/null)
if [ "$rc" = 2 ] && [ "$v" = NO_VERDICT ] && [ "$left" = 0 ] && [ ! -e "$SG/out/verdict.json" ]; then echo "PASS frontier signal/sigterm-during-build: NO_VERDICT rc 2, child group gone"
else echo "FAIL frontier signal/sigterm-during-build: rc $rc $v processes left $left $(tail -c 200 "$SG/run.log")"; bad=1; fi
# OUT/pinned/comparator.json swapped to theorem_names ["main2"] right before prepare()
# parses it and restored right after: the recorded comparator sha256 is that of the bytes PARSED, so check() refuses (before
# ACCEPTED exit 0 for c03, sorry in the target)
PS=$W/prepare-swap; rm -rf "$PS"; mkdir -p "$PS"
python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c["theorem_names"]=["main2"]; json.dump(c,open(sys.argv[2],"w"),indent=1)' "$CH/comparator.json" "$PS/evil.json"
python3 -I - "$PS" > "$PS/watch.log" 2>&1 <<'PY' &
import os, shutil, sys, time
R = sys.argv[1]; D = R + "/out/pinned"; P = D + "/comparator.json"; t_end = time.time() + 900
while time.time() < t_end and not (os.path.isdir(D) and any(n.startswith("solution.export") for n in os.listdir(D))):
    pass   # busy: the window before prepare() parses the file is short
shutil.copyfile(P, R + "/orig.json"); shutil.copyfile(R + "/evil.json", R + "/e.tmp"); os.rename(R + "/e.tmp", P)
print("swapped", flush=True)
while time.time() < t_end and not os.path.exists(R + "/out/frontier"):
    time.sleep(0.001)
shutil.copyfile(R + "/orig.json", R + "/o.tmp"); os.rename(R + "/o.tmp", P)
print("restored", flush=True)
PY
PSW=$!
python3 -I "$FR" run "$W/cases/c03-sorry-in-target/proj" "$CH" "$PS/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$PS/run.log" 2>&1; rc=$?
wait $PSW
v=$(tail -1 "$PS/run.log" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("verdict"))' 2>/dev/null)
# the row must show the refusal itself: a swap that missed its window (honest REJECTED) is a FAIL of the row, not a pass
if [ "$rc" = 2 ] && [ "$v" = NO_VERDICT ] && grep -q 'not the pinned ones' "$PS/run.log" && grep -q swapped "$PS/watch.log"; then echo "PASS frontier swap/comparator-during-prepare: NO_VERDICT rc 2 (the prepared inputs are not the pinned ones)"
else echo "FAIL frontier swap/comparator-during-prepare: $v rc $rc watch: $(tr '\n' ' ' < "$PS/watch.log") $(tail -c 200 "$PS/run.log")"; bad=1; fi
# (defence in depth) both DERIVED configs (OUT/frontier/comparator.{compare,frontier}.json) swapped to
# theorem_names ["main2"] as soon as prepare() writes them: check() judges only what prepare() wrote (in-memory sha256) -> NO_VERDICT
# (without the check: ACCEPTED exit 0 for c03). The row fails if the swap missed its window.
DS=$W/derived-swap; rm -rf "$DS"; mkdir -p "$DS"
python3 -I - "$CH/comparator.json" "$DS" <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); R = sys.argv[2]; A = list(c["permitted_axioms"])
b = dict(c); b["theorem_names"] = ["main2"]; b["permitted_axioms"] = A
a = dict(c); a["theorem_names"] = ["main2"]; a["permitted_axioms"] = A + ["sorryAx"]
for k in ("external_kernels", "enable_nanoda"):
    a.pop(k, None)
json.dump(b, open(R + "/evil.frontier.json", "w"), indent=1); json.dump(a, open(R + "/evil.compare.json", "w"), indent=1)
PY
python3 -I - "$DS" > "$DS/watch.log" 2>&1 <<'PY' &
import os, shutil, sys, time
R = sys.argv[1]; D = R + "/out/frontier"; t_end = time.time() + 900
while time.time() < t_end and not os.path.exists(D + "/comparator.compare.json"):
    pass
for n in ("frontier", "compare"):
    shutil.copyfile(R + "/evil.%s.json" % n, R + "/%s.tmp" % n); os.rename(R + "/%s.tmp" % n, D + "/comparator.%s.json" % n)
print("swapped", flush=True)
PY
DSW=$!
python3 -I "$FR" run "$W/cases/c03-sorry-in-target/proj" "$CH" "$DS/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$DS/run.log" 2>&1; rc=$?
wait $DSW
v=$(tail -1 "$DS/run.log" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("verdict"))' 2>/dev/null)
if [ "$rc" = 2 ] && [ "$v" = NO_VERDICT ] && grep -q 'changed after prepare' "$DS/run.log" && grep -q swapped "$DS/watch.log"; then echo "PASS frontier swap/derived-configs-after-prepare: NO_VERDICT rc 2 (the internal configurations changed after prepare)"
else echo "FAIL frontier swap/derived-configs-after-prepare: $v rc $rc watch: $(tr '\n' ' ' < "$DS/watch.log") $(tail -c 200 "$DS/run.log")"; bad=1; fi
# SIGKILL of frontier.py's whole process group (timeout -s KILL / a job controller):
# bin/fastverify and everything below it die with it (they stay in the group); a retry in the same OUT is then judged afresh
GK=$W/group-kill; rm -rf "$GK"; mkdir -p "$GK"
setsid python3 -I "$FR" run "$W/cases/c01-one-open/proj" "$CH" "$GK/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$GK/run.log" 2>&1 &
GKP=$!
for _ in $(seq 1 600); do [ -d "$GK/out/fv" ] && break; sleep 0.1; done; sleep 1
kill -KILL -- -$GKP 2>/dev/null; wait $GKP 2>/dev/null; sleep 2
left=$(pgrep -f "$GK/out" | wc -l)
python3 -I "$FR" run "$W/cases/c01-one-open/proj" "$CH" "$GK/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$GK/retry.log" 2>&1; rc=$?
if [ "$left" = 0 ] && [ "$rc" = 3 ]; then echo "PASS frontier signal/group-sigkill: no process left; retry in the same OUT CONDITIONAL rc 3"
else echo "FAIL frontier signal/group-sigkill: processes left $left, retry rc $rc $(tail -c 200 "$GK/retry.log")"; bad=1; fi
# SIGTERM sent again and again: handled once - NO_VERDICT exit 2 (no RecursionError, not
# 143), nothing left
RP=$W/sig-repeat; rm -rf "$RP"; mkdir -p "$RP"
python3 -I "$FR" run "$W/cases/c03-sorry-in-target/proj" "$CH" "$RP/out" --challenge-sha256 "$SHA" --comparator-sha256 "$CSHA" --threads "$T" > "$RP/run.log" 2>&1 &
RPP=$!
for _ in $(seq 1 600); do [ -d "$RP/out/fv" ] && break; sleep 0.1; done; sleep 1
while kill -TERM $RPP 2>/dev/null; do sleep 0.005; done; wait $RPP; rc=$?; sleep 1
left=$(pgrep -f "$RP/out" | wc -l)
v=$(tail -1 "$RP/run.log" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read()).get("verdict"))' 2>/dev/null)
if [ "$rc" = 2 ] && [ "$v" = NO_VERDICT ] && ! grep -q 'RecursionError\|Traceback' "$RP/run.log" && [ "$left" = 0 ]; then echo "PASS frontier signal/sigterm-repeated: NO_VERDICT rc 2, handled once, nothing left"
else echo "FAIL frontier signal/sigterm-repeated: rc $rc $v left $left $(tail -c 200 "$RP/run.log")"; bad=1; fi
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

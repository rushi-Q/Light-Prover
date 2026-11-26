#!/bin/bash
# run437.sh [WORK] : the adversarial frontier suite (fastverify/tools/frontier/test) on Lean 4.37.0-rc1 through the
# PRODUCTION path of the conditional verdict:
#   source cases + pinned flow: bin/fastverify PROJECT CH OUT --preset sound --pins check/sound/pins-437.env
#     --modulo-frontier [auto|FILE] [--frontier-pin DIR]  (= check/frontier/check-frontier.sh --pins pins-437.env;
#     official 4.37.0-rc1 build + exporter; the 4.37 judge = check/sound/pins-437.env)
#   fault injection (the untrusted preparer lies): tools/frontier/frontier.py prepare, the files tampered, then the two
#     trusted checks of 'frontier.py check' run DIRECTLY: check/sound/check-sound.sh ... --pins pins-437.env (the reviewed
#     check-sound.sh v2.1 --pins path, 4.37 judge): compare = C' vs C, main = S' vs C'.
#   pin: tools/frontier/frontier.py pin (its pin-time check uses the default judge; C' does not depend on the judge).
# Case sources and expectations = fastverify/tools/frontier/test/gen.py (lean-toolchain rewritten to v4.37.0-rc1).
# Mapping of the suite's frontier.py options: '--frontier La' -> --modulo-frontier FILE (one name per line). '--axioms myAx'
# (c08: a project axiom as a hypothesis): bin/fastverify --modulo-frontier FILE (= check-frontier.sh --allowed) takes sorried
# theorems only -> c08 is expected REJECTED through bin/fastverify; the axioms rows then run check-frontier.sh --axioms FILE
# (b40fe52d) on c08's export (-> CONDITIONAL [myAx]) and on c14's (the native_decide aux axiom / Lean.ofReduceBool
# listed as 'project axioms' -> refused, never a verdict).
# Needs the 4.37 binaries of check/sound/pins-437.env installed (under /scratch/fastverify-next/sound/; else DECLINED).
# WORK (default $FV_SCRATCH/$USER-frt437) must lie outside /tmp, /home, /var and /run (hidden in the check's sandbox);
# FV_PACKAGES = the trusted Lake workspace with materialized dependencies (default <repository root>/verify/challenge).
# Usage: env JOBS=8 EVAL_THREADS=4 bash run437.sh WORK   (~4-7 min, 32 threads; prints PASS/FAIL rows, RESULT)
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
export FASTVERIFY_ROOT=${FASTVERIFY_ROOT:-$(cd "$HERE/../../.." && pwd)}
[ -x "$FASTVERIFY_ROOT/bin/fastverify" ] || FASTVERIFY_ROOT=$LIGHT_LEAN/fastverify
PKG=$FASTVERIFY_ROOT; FV=$PKG/bin/fastverify; TESTD=$HERE; [ -f "$TESTD/gen.py" ] || TESTD=$PKG/tools/frontier/test
FR=$PKG/tools/frontier/frontier.py
PINS=$PKG/check/sound/pins-437.env
TC=leanprover/lean4:v4.37.0-rc1
W=${1:-${FV_SCRATCH:?node-local work root outside /tmp, /home, /var, /run (required unless WORK is given)}/$USER-frt437}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-4}; J=${JOBS:-8}
WS=${FV_PACKAGES:-$(dirname "$FASTVERIFY_ROOT")/verify/challenge}   # trusted Lake workspace (default: <repository root>/verify/challenge)
[ -d "$WS" ] || { echo "FAIL no trusted package workspace at $WS: set FV_PACKAGES"; echo "RESULT FAIL"; exit 1; }
echo "# run437 $(date -u +%FT%TZ) host $(hostname) pkg frontier.py $(sha256sum "$PKG/tools/frontier/frontier.py" | cut -c1-8)" \
     "check-frontier.sh $(sha256sum "$PKG/check/frontier/check-frontier.sh" | cut -c1-8) pins-437 $(sha256sum "$PINS" | cut -c1-8)" \
     "fastverify.py $(sha256sum "$PKG/lib/fastverify.py" | cut -c1-8) prep-pins $(sha256sum "$PKG/check/frontier/pins.env" | cut -c1-8)"
CASES=$(python3 -I "$TESTD/gen.py" "$W")
find "$W" -name lean-toolchain -exec sh -c 'printf "%s\n" "$0" > "$1"' "$TC" {} \;
grep -rh . --include=lean-toolchain "$W" | sort | uniq -c
python3 -I "$PKG/tools/claims.py" pin "$W/chroot" "$WS" "$W/given" ch > "$W/pin.log" 2>&1 || { echo "FAIL pin challenge"; tail -5 "$W/pin.log"; echo "RESULT FAIL"; exit 1; }
CH=$W/given/ch; SHA=$(cut -d' ' -f1 "$CH/challenge.export.sha256")
echo "# challenge pinned (4.37 official build + exporter): sha256 $SHA"
bad=0
fvrun() {  # fvrun PROJ OUT [extra fastverify args...]
  local p=$1 o=$2; shift 2
  "$FV" "$p" "$CH" "$o" --preset sound --pins "$PINS" --challenge-sha256 "$SHA" --threads "$T" --export-dir none "$@" \
    > "$o.log" 2>&1
  echo $? > "$o.rc"
}
runcase() {  # runcase ID
  local id=$1 mf=auto
  local args; args=$(python3 -I -c 'import json,sys; print(" ".join(json.load(open(sys.argv[1]))["args"]))' "$W/cases/$id/expect.json")
  set -- $args
  if [ $# -ge 2 ]; then printf '%s\n' "$2" > "$W/cases/$id/allowed.txt"; mf=$W/cases/$id/allowed.txt; fi
  # production path: --modulo-frontier FILE / check-frontier.sh --allowed lists SORRIED THEOREMS only (-> frontier.py
  # --frontier @FILE); frontier.py's '--axioms' (a project axiom as a hypothesis) has no production flag -> REJECTED
  if [ "${1:-}" = "--axioms" ]; then python3 -I - "$W/cases/$id/expect.json" <<'PY2'
import json, sys
e = json.load(open(sys.argv[1])); e["verdict"] = "REJECTED"; e["note"] = "production path: no axiom hypotheses"
json.dump(e, open(sys.argv[1], "w"))
PY2
  fi
  fvrun "$W/cases/$id/proj" "$W/out/$id" --modulo-frontier "$mf"
}
mkdir -p "$W/out"
t0=$(date +%s.%N)
n=0
for id in $CASES; do runcase "$id" & n=$((n+1)); if [ $n -ge "$J" ]; then wait -n; n=$((n-1)); fi; done; wait
echo "# source cases done in $(python3 -c "import time;print(round(time.time()-$t0,1))") s"
judge() {  # judge EXPECT_JSON RESULT_JSON RC
  python3 -I - "$@" <<'PY'
import json, sys
e = json.load(open(sys.argv[1]))
try:
    r = json.load(open(sys.argv[2]))
except Exception as x:
    print("FAIL no result.json (%s)" % x); sys.exit()
rc = int(sys.argv[3])
want_rc = {"ACCEPTED": 0, "REJECTED": 1, "CONDITIONAL": 3}.get(e["verdict"], 2)
f = r.get("frontier") or {}
fr = sorted((x.get("lemma") or x.get("name")).replace("._fv_frontier_axiom", "") for x in (f.get("frontier") or [])
            if isinstance(x, dict))
ok = r.get("verdict") == e["verdict"] and rc == want_rc and (e["frontier"] is None or e["verdict"] != "CONDITIONAL"
                                                             or fr == sorted(e["frontier"]))
chk = (r.get("checks") or {}).get("sound") or {}
st = chk.get("stage") if isinstance(chk.get("stage"), dict) else {}
tcs = sorted({str(v.get("toolchain") or v.get("judge_toolchain") or "?") for v in (st.get("checks") or {}).values()
              if isinstance(v, dict)})
why = (st.get("why") or r.get("verdict_basis") or "").replace("\n", " ")[:150]
print("%s verdict=%s rc=%d frontier=%s (expected %s %s) judge=%s wall=%s | %s" % (
    "PASS" if ok else "FAIL", r.get("verdict"), rc, fr, e["verdict"], e["frontier"], ",".join(tcs),
    (r.get("seconds") or {}).get("total") or r.get("wall_s") or "?", why))
PY
}
for id in $CASES; do
  r=$(judge "$W/cases/$id/expect.json" "$W/out/$id/result.json" "$(cat "$W/out/$id.rc")")
  echo "${r%% *} frontier437 $id ${r#* }"; case "$r" in PASS*) ;; *) bad=1;; esac
done

# ---------- check-frontier.sh --axioms (b40fe52d): declared PROJECT axioms as listed hypotheses, on 4.37 ----------
axrow() {  # axrow LABEL CASE AXIOM_NAME EXPECTED(CONDITIONAL:names | REFUSED)
  local lab=$1 c=$2 ax=$3 want=$4 d=$W/axioms/$1
  mkdir -p "$d"; printf '%s\n' "$ax" > "$d/axioms.txt"
  "$PKG/check/frontier/check-frontier.sh" "$W/out/$c/solution.export" "$CH/challenge.export" "$CH/comparator.json" \
    --pins "$PINS" --axioms "$d/axioms.txt" --threads "$T" --json "$d/out.json" --log "$d/out.log" > /dev/null 2>&1
  local rc=$?
  local r; r=$(python3 -I - "$d/out.json" "$rc" "$want" <<'PY'
import json, sys
try:
    j = json.load(open(sys.argv[1]))
except Exception as x:
    j = {"verdict": "NO-JSON", "reason": str(x)}
rc, want = int(sys.argv[2]), sys.argv[3]
fr = sorted(f.get("name") for f in (j.get("frontier") or []) if isinstance(f, dict))
tcs = sorted({str(x.get("toolchain")) for x in (j.get("checks") or {}).values() if isinstance(x, dict)})
if want == "REFUSED":
    ok = rc not in (0, 3) and j.get("verdict") not in ("ACCEPTED", "CONDITIONAL")
else:
    w = want.split(":"); ok = rc == 3 and j.get("verdict") == "CONDITIONAL" and fr == sorted(w[1].split(","))
print("%s verdict=%s rc=%d frontier=%s judge=%s | %s" % ("PASS" if ok else "FAIL", j.get("verdict"), rc, fr, ",".join(tcs),
      (j.get("why") or j.get("reason") or "")[:140]))
PY
)
  echo "${r%% *} frontier437 axioms/$lab ${r#* }"; case "$r" in PASS*) ;; *) bad=1;; esac
}
axrow declared-project-axiom c08-axiom-allowed myAx CONDITIONAL:myAx
axrow native-decide-aux-refused c14-native-decide t._native.native_decide.ax_1_1 REFUSED
axrow reduceBool-refused c14-native-decide Lean.ofReduceBool REFUSED

# ---------- pinned flow (pin made by the harness copy with the 4.37 judge; runs through bin/fastverify --frontier-pin) ----
P=$W/pinned; mkdir -p "$P"
python3 -I "$FR" pin "$W/out/c01-one-open/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$P/pin" --threads "$T" > "$P/pin.log" 2>&1
prc=$?
[ $prc = 3 ] && [ -f "$P/pin/frontier.json" ] && echo "PASS frontier437 pin c01 (exit 3, pinned)" || { echo "FAIL frontier437 pin c01 rc $prc: $(tail -3 "$P/pin.log")"; bad=1; }
pinrun() {  # pinrun LABEL SOURCE EXPECTED_VERDICT
  local lab=$1 src=$2 want=$3 d=$P/$1
  mkdir -p "$d"; cp -a "$W/cases/c01-one-open/proj" "$d/proj"; printf '%s' "$src" > "$d/proj/Solution.lean"
  fvrun "$d/proj" "$d/out" --modulo-frontier auto --frontier-pin "$P/pin"
  local rc; rc=$(cat "$d/out.rc"); local v; v=$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); f=r.get("frontier") or {}; print(r["verdict"], ",".join(f.get("frontier_closed") or []) or "-", ((((r.get("checks") or {}).get("sound") or {}).get("stage") or {}).get("why") or r.get("verdict_basis") or "")[:120])' "$d/out/result.json" 2>/dev/null)
  if [ "${v%% *}" = "$want" ]; then echo "PASS frontier437 pinned/$lab: $v (rc $rc)"; else echo "FAIL frontier437 pinned/$lab: got '$v' rc $rc, expected $want"; bad=1; fi
}
BASE=$(python3 -I -c 'import sys; sys.path.insert(0,sys.argv[1]); import gen; print(gen.BASE_DEFS)' "$TESTD")
L2=$(python3 -I -c 'import sys; sys.path.insert(0,sys.argv[1]); import gen; print(gen.L2)' "$TESTD")
TAIL='theorem main : ∀ n, P n := fun n => (L2 n).2 (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
'
pinrun same "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := sorry
$L2
$TAIL" CONDITIONAL &
pinrun closed "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := Nat.zero_add n
$L2
$TAIL" ACCEPTED &
pinrun drift-def "$BASE
def Q (n : Nat) : Prop := 0 + n = n ∨ True
theorem L1 (n : Nat) : Q n := sorry
theorem L2' (n : Nat) : Q n → P n := fun _ => rfl
theorem main : ∀ n, P n := fun n => L2' n (L1 n)
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
" REJECTED &
pinrun drift-stmt "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : P n := sorry
theorem main : ∀ n, P n := fun n => L1 n
theorem main2 : ∀ p : Pt, Good p := fun p => Nat.add_comm _ _
" REJECTED &
pinrun new-open "$BASE
def Q (n : Nat) : Prop := 0 + n = n
theorem L1 (n : Nat) : Q n := sorry
theorem L9 (p : Pt) : Good p := sorry
$L2
theorem main : ∀ n, P n := fun n => (L2 n).2 (L1 n)
theorem main2 : ∀ p : Pt, Good p := L9
" REJECTED &
wait

# ---------- fault injection (same lies as tools/frontier/test/run.sh; checks = check-sound.sh --pins pins-437.env) ----------
chk2() {  # chk2 DIR : the two trusted checks of 'frontier.py check', run directly with --pins pins-437.env -> DIR/verdict.json
  local d=$1 F CS=$PKG/check/sound/check-sound.sh
  F=$(python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["frontier"]))' "$d/frontier.json")
  if [ "$F" -gt 0 ]; then
    "$CS" "$d/frontier/challenge.export" "$CH/challenge.export" "$d/comparator.compare.json" --threads "$T" --pins "$PINS" \
      --json "$d/check_compare.json" --log "$d/check_compare.log" > /dev/null 2>&1 &
  fi
  "$CS" "$d/solution.frontier.export" "$d/frontier/challenge.export" "$d/comparator.frontier.json" --threads "$T" --pins "$PINS" \
    --json "$d/check_main.json" --log "$d/check_main.log" > /dev/null 2>&1
  wait
  python3 -I - "$d" "$F" <<'PY'
import json, os, sys
d, F = sys.argv[1], int(sys.argv[2])
def ld(k):
    try:
        return json.load(open(os.path.join(d, "check_%s.json" % k)))
    except Exception:
        return {"verdict": "DECLINED", "reason": "no JSON"}
m = ld("main"); c = ld("compare") if F else None
if m.get("verdict") == "ACCEPTED" and (c is None or c.get("verdict") == "ACCEPTED"):
    v = "CONDITIONAL" if F else "ACCEPTED"; why = ""
elif m.get("verdict") == "REJECTED":
    v = "REJECTED"; why = "main check: %s" % m.get("reason")
else:
    v = "NO_VERDICT"; why = "main: %s; compare: %s" % (m.get("reason"), c and c.get("reason"))
ex = {"CONDITIONAL": 3, "ACCEPTED": 0, "REJECTED": 1}.get(v, 2)
json.dump({"verdict": v, "exit": ex, "why": why, "checks": {"main": m, "compare": c or {"verdict": "NOT_RUN"}}},
          open(os.path.join(d, "verdict.json"), "w"))
sys.exit(ex)
PY
}
X=$W/faults; mkdir -p "$X"
mkdir -p "$X/fchroot"; cp -a "$W/chroot/ch" "$X/fchroot/ch"
sed -i 's/^theorem main : ∀ n, P n := by sorry/def Q (n : Nat) : Prop := 0 + n = n\ntheorem main : ∀ n, Q n := by sorry/' "$X/fchroot/ch/Challenge.lean"
python3 -I "$PKG/tools/claims.py" pin "$X/fchroot" "$WS" "$X/fgiven" ch > "$X/fpin.log" 2>&1
python3 -I "$FR" prepare "$W/out/c06-statement-changed/solution.export" "$X/fgiven/ch/challenge.export" "$CH/comparator.json" "$X/f1" > "$X/f1.prep.log" 2>&1
python3 -I - "$X/f1/frontier.json" "$CH/challenge.export" <<'PY'
import json, sys, hashlib
p = sys.argv[1]; j = json.load(open(p))
j["challenge_export"] = sys.argv[2]; j["challenge_sha256"] = hashlib.sha256(open(sys.argv[2], "rb").read()).hexdigest()
json.dump(j, open(p, "w"))
PY
chk2 "$X/f1" > "$X/f1.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], v["checks"]["main"]["verdict"], v["checks"]["compare"]["verdict"])' "$X/f1/verdict.json" 2>/dev/null)
case "$v" in "NO_VERDICT ACCEPTED REJECTED") echo "PASS frontier437 fault/forged-challenge: $v (main accepted the forged pair, compare caught it; rc $rc)";;
  *) echo "FAIL frontier437 fault/forged-challenge: '$v' rc $rc"; bad=1;; esac
python3 -I "$FR" prepare "$W/out/c01-one-open/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$X/f2" > "$X/f2.prep.log" 2>&1
python3 -I - "$X/f2/solution.frontier.export" "$W/out/c01-one-open/solution.export" <<'PY'
import json, sys
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
chk2 "$X/f2" > "$X/f2.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], (v.get("why") or "")[:100])' "$X/f2/verdict.json" 2>/dev/null)
case "$v" in REJECTED*) echo "PASS frontier437 fault/extra-axiom: $v (rc $rc)";; *) echo "FAIL frontier437 fault/extra-axiom: '$v' rc $rc"; bad=1;; esac
# (2b) the same lie against the REDIRECT rewrite (v2.1+): take the prepared S' itself and turn the proved L2 into an axiom
python3 -I "$FR" prepare "$W/out/c01-one-open/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$X/f2b" > "$X/f2b.prep.log" 2>&1
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
chk2 "$X/f2b" > "$X/f2b.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], (v.get("why") or "")[:100])' "$X/f2b/verdict.json" 2>/dev/null)
case "$v" in REJECTED*L2*) echo "PASS frontier437 fault/extra-axiom-redirect: $v (rc $rc)";; *) echo "FAIL frontier437 fault/extra-axiom-redirect: '$v' rc $rc"; bad=1;; esac
python3 -I "$FR" prepare "$W/out/c01-one-open/solution.export" "$CH/challenge.export" "$CH/comparator.json" "$X/f3" > "$X/f3.prep.log" 2>&1
python3 -I - "$X/f3" <<'PY'
import json, sys, hashlib, os
d = sys.argv[1]; cp = os.path.join(d, "frontier", "challenge.export")
lines = open(cp, "rb").read().splitlines(keepends=True)
pidx = tidx = None; me = 0
for raw in lines:
    o = json.loads(raw)
    if "in" in o and "str" in o and o["str"]["pre"] == 0:
        if o["str"]["str"] == "P": pidx = o["in"]
        if o["str"]["str"] == "True": tidx = o["in"]
    if "ie" in o: me = max(me, o["ie"])
ptype = pdef = true_e = None
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
chk2 "$X/f3" > "$X/f3.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1])); print(v["verdict"], v["checks"]["main"]["verdict"], v["checks"]["compare"]["verdict"])' "$X/f3/verdict.json" 2>/dev/null)
case "$v" in ACCEPTED*|"") echo "FAIL frontier437 fault/duplicate-constant: '$v' rc $rc"; bad=1;; *) echo "PASS frontier437 fault/duplicate-constant: $v (no acceptance; rc $rc)";; esac
# every check of the fault rows must have run on the 4.37 judge
python3 -I - "$X" <<'PY'
import json, sys, glob
tcs = set()
for f in glob.glob(sys.argv[1] + "/f*/check_*.json"):
    j = json.load(open(f)); tcs.add(str(j.get("toolchain") or j.get("judge_toolchain") or j.get("tc_version") or "?"))
print("# fault-row judge toolchains: %s" % sorted(tcs))
PY
echo "# total $(python3 -c "import time;print(round(time.time()-$t0,1))") s"
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

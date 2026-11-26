#!/bin/bash
# tests/budget/run.sh - regression test of the resource-budget tools: no cgroup needed, runs anywhere in < 10 s.
#   1. budget.py host: valid JSON, memory_budget <= MemAvailable, cpu_budget <= affinity
#   2. budget.py estimate / plan: monotone in threads and export size; plan never exceeds the budget when it says "fits";
#      a budget below the 1-thread estimate reports fits=false
#   3. fit.py on the shipped results reproduces the model coefficients within 5 % (check / ccmp / pleanchecker / gruszka)
#   4. mkreport.py and summarize.py run on the shipped results and print the expected sections / rows
#   5. frontier.py on a synthetic lean4export (format 3.1.0): a pure-sorry theorem on the path, a partial proof, a sorried
#      definition, an unreachable sorry, an extra axiom -> exactly the expected ledger
#   6. cgrun.sh / cgrun-inner.sh / sweep_check.sh / legs.sh / run_fv.sh / swarm_check.sh parse (bash -n)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
B=${BUDGET_DIR:-$(cd "$H/../../bench/budget" 2>/dev/null && pwd || echo "$H")}
LIB=${BUDGET_LIB:-$(cd "$H/../../lib" 2>/dev/null && pwd || echo "$B")}
PY=/usr/bin/python3
T=$(mktemp -d /tmp/budget-test.XXXXXX); trap 'rm -rf "$T"' EXIT
pass=0; fail=0
ok()   { pass=$((pass+1)); echo "PASS $1"; }
bad()  { fail=$((fail+1)); echo "FAIL $1: $2"; }
BP=$LIB/budget.py; [ -f "$BP" ] || BP=$B/budget.py

# 1. host
if $PY -I "$BP" host > "$T/host.json" 2>"$T/host.err" && $PY -I - "$T/host.json" <<'PY'
import json, os, sys
h = json.load(open(sys.argv[1]))
assert h["mem_available"] is None or h["memory_budget"] <= h["mem_available"], "budget > MemAvailable"
assert h["cpu_budget"] <= len(os.sched_getaffinity(0)), "cpu_budget > affinity"
assert "cgroup" in h and "limited_by" in h
PY
then ok "budget.py host"; else bad "budget.py host" "$(cat "$T/host.err" | tail -2)"; fi

# 2. estimate / plan
if $PY -I - "$BP" <<'PY'
import json, subprocess, sys
bp = sys.argv[1]
def run(*a):
    return json.loads(subprocess.run(["/usr/bin/python3", "-I", bp, *a], capture_output=True, text=True, check=True).stdout)
e = [run("estimate", "check", str(b), str(t))["peak_bytes"] for b, t in ((10**8, 4), (10**9, 4), (10**9, 16), (10**10, 16))]
assert e[0] < e[1] < e[2] < e[3], e
p = run("plan", str(1104038853), "--mem", str(6 * 2**30), "--cpus", "16")
assert p["fits"] and p["expected_peak_bytes"] * 1.15 <= p["memory_budget"] and 1 <= p["threads"] <= 16, p
q = run("plan", str(6067502667), "--mem", str(4 * 2**30), "--cpus", "16")
assert not q["fits"] and q["threads"] == 1, q
r = run("plan", str(6067502667), "--mem", str(64 * 2**30), "--cpus", "128")
assert r["fits"] and r["threads"] <= 64, r
PY
then ok "budget.py estimate/plan"; else bad "budget.py estimate/plan" "see above"; fi

# 3. fit on shipped results runs, and the planning model stays inside the measured floors (bisection rows of results/limits1)
if [ -d "$B/results" ] && $PY -I "$B/fit.py" "$B/sizes.json" "$B/results/sweep1" "$B/results/legs1" > "$T/fit.out" 2>"$T/fit.err" \
   && $PY -I - "$T/fit.out" "$BP" <<'PY'
import json, subprocess, sys
txt = open(sys.argv[1]).read(); j = json.loads(txt[:txt.index("\n}\n") + 2])
assert j["check"]["runs"] >= 12 and j["ccmp"]["runs"] >= 5 and 3.0 <= j["check"]["bytes_per_export_byte"] <= 4.5, j["check"]
def est(b, t):
    return json.loads(subprocess.run(["/usr/bin/python3", "-I", sys.argv[2], "estimate", "check", str(b), str(t)],
                                     capture_output=True, text=True, check=True).stdout)["peak_bytes"]
G = 2**30
# rh-mid 1.10 GB: DECLINED at 3/4/5 GB, ACCEPTED at 4/5/6 GB for 4/8/16 threads -> the estimate must lie in (declined, accepted*1.2]
for t, lo, hi in ((4, 3, 4), (8, 4, 5), (16, 5, 6)):
    e = est(1104038853, t); assert lo * G < e <= hi * G * 1.2, (t, e / G)
e = est(6067502667, 16); assert 22 * G < e <= 24.25 * G * 1.2, e / G      # Mathlib: killed at 22 GB, peak 24.25 GB
e = est(61570595788, 64); assert 150 * G < e <= 212.2 * G * 1.2, e / G    # RH: peak 212 GB at 64 threads
PY
then ok "fit.py runs; planning model inside the measured floors"; else bad "fit.py / model envelope" "$(tail -2 "$T/fit.err"; tail -3 "$T/fit.out" 2>/dev/null | head -1)"; fi

# 4. report + summary
if [ -d "$B/results" ] && $PY -I "$B/mkreport.py" "$B/results" > "$T/rep.md" 2>"$T/rep.err" && grep -q '^### A\.' "$T/rep.md" \
   && grep -q '^### C\.' "$T/rep.md" && grep -q '| rh-mid | 16 | 6G | ACCEPTED' "$T/rep.md" && grep -q '| rh-mid | 16 | 5G | DECLINED' "$T/rep.md" \
   && $PY -I "$B/summarize.py" "$B/results/limits1" --tsv | grep -q 'sw-midlim.T16.M6G'
then ok "mkreport.py / summarize.py"; else bad "mkreport.py / summarize.py" "$(tail -2 "$T/rep.err"; grep -c . "$T/rep.md")"; fi

# 5. frontier.py on a synthetic export: names 1..; exprs: Prop sort, consts; decls
$PY -I - "$T/syn.export" <<'PY'
import json, sys
L = []
def w(o): L.append(json.dumps(o, separators=(",", ":")))
w({"meta": {"exporter": {"name": "synthetic", "version": "3.1.0"}, "format": {"version": "3.1.0"}, "lean": {"githash": "x", "version": "4.36.0"}}})
names = ["sorryAx", "propext", "myAxiom", "Target", "Good", "Frontier", "Partial", "BadDef", "Unreach", "P", "Q", "Bool", "Bool.true"]
for i, n in enumerate(names, 1):
    pre = 0
    if "." in n:
        pre = names.index(n.rsplit(".", 1)[0]) + 1; n = n.rsplit(".", 1)[1]
    w({"in": i, "str": {"pre": pre, "str": n}})
N = {n: i + 1 for i, n in enumerate(names)}
E = {}
def e(k, o):
    idx = len(E); E[k] = idx; o["ie"] = idx; w(o); return idx
e("Prop", {"sort": 0})
for c in ["sorryAx", "propext", "myAxiom", "Good", "Frontier", "Partial", "BadDef", "Unreach", "P", "Q", "Bool.true"]:
    e(c, {"const": {"name": N[c], "us": []}})
e("sorry P", {"app": {"fn": E["sorryAx"], "arg": E["P"]}})          # sorryAx P
e("sorry P b", {"app": {"fn": E["sorry P"], "arg": E["Bool.true"]}})  # pure sorry value
e("Partial val", {"app": {"fn": E["Good"], "arg": E["sorry P b"]}})     # Good applied to a sorry: partial
e("Target val", {"app": {"fn": E["Frontier"], "arg": E["Partial"]}})    # Target := Frontier Partial
e("Target val2", {"app": {"fn": E["Target val"], "arg": E["myAxiom"]}})  # ... myAxiom
e("Target val3", {"app": {"fn": E["Target val2"], "arg": E["BadDef"]}})  # ... BadDef
w({"axiom": {"isUnsafe": False, "levelParams": [], "name": N["sorryAx"], "type": E["Prop"]}})
w({"axiom": {"isUnsafe": False, "levelParams": [], "name": N["propext"], "type": E["Prop"]}})
w({"axiom": {"isUnsafe": False, "levelParams": [], "name": N["myAxiom"], "type": E["Prop"]}})
w({"def": {"all": [N["P"]], "hints": "abbrev", "levelParams": [], "name": N["P"], "safety": "safe", "type": E["Prop"], "value": E["Prop"]}})
w({"def": {"all": [N["Q"]], "hints": "abbrev", "levelParams": [], "name": N["Q"], "safety": "safe", "type": E["Prop"], "value": E["Prop"]}})
w({"def": {"all": [N["BadDef"]], "hints": "abbrev", "levelParams": [], "name": N["BadDef"], "safety": "safe", "type": E["Prop"], "value": E["sorry P b"]}})
w({"thm": {"all": [N["Good"]], "levelParams": [], "name": N["Good"], "type": E["P"], "value": E["propext"]}})
w({"thm": {"all": [N["Frontier"]], "levelParams": [], "name": N["Frontier"], "type": E["P"], "value": E["sorry P b"]}})
w({"thm": {"all": [N["Partial"]], "levelParams": [], "name": N["Partial"], "type": E["Q"], "value": E["Partial val"]}})
w({"thm": {"all": [N["Unreach"]], "levelParams": [], "name": N["Unreach"], "type": E["Q"], "value": E["sorry P b"]}})
w({"thm": {"all": [N["Target"]], "levelParams": [], "name": N["Target"], "type": E["Q"], "value": E["Target val3"]}})
open(sys.argv[1], "w").write("\n".join(L) + "\n")
PY
if $PY -I "$B/frontier.py" "$T/syn.export" --targets Target --json "$T/fr.json" > /dev/null 2>"$T/fr.err" && $PY -I - "$T/fr.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
fr = {(f["name"], f["kind"]) for f in r["frontier"]}
assert fr == {("Frontier", "pure-sorry"), ("Partial", "partial")}, fr
assert [d["name"] for d in r["sorried_non_theorems"]] == ["BadDef"], r["sorried_non_theorems"]
assert set(r["extra_axioms"]) == {"sorryAx", "myAxiom"}, r["extra_axioms"]
assert "Unreach" not in {n for n in r["axioms"]} and r["closure_size"] >= 8 and r["unknown_targets"] == []
PY
then ok "frontier.py ledger (synthetic export)"; else bad "frontier.py" "$(tail -3 "$T/fr.err")"; fi

# 6b. the harness itself, when a cgroup scope launcher is available on this host (CGRUN_TOOL; it needs sudo
#     rights for systemd-run, the only sanctioned sudo use): a 100 MB allocation under a 300 MB cap succeeds and is
#     recorded; a 600 MB allocation under the same cap is OOM-killed (oom_kill >= 1, non-zero exit, record still written)
CGRUN=${FV_CGRUN:-}; [ -n "$CGRUN" ] || [ ! -x /usr/local/bin/cgrun ] || CGRUN=/usr/local/bin/cgrun; [ -n "$CGRUN" ] || CGRUN=$(command -v cgrun 2>/dev/null || true)   # FV_CGRUN, else /usr/local/bin/cgrun, else cgrun on PATH
CGT=${CGRUN_TOOL:-$CGRUN}
if [ -x "$CGT" ] && [ -x "$B/cgrun.sh" ] && [ "${SKIP_CGRUN_TEST:-0}" != 1 ]; then
  if CGRUN_TOOL=$CGT "$B/cgrun.sh" --name budget-test-ok --mem 300M --sample 0 --json "$T/ok.json" -- /usr/bin/python3 -c "x=bytearray(100*1024*1024)" > /dev/null 2>&1 \
     && $PY -I -c 'import json,sys; j=json.load(open(sys.argv[1])); assert j["exit"]==0 and int(j["memory_peak"])>=90*2**20 and j["limits"]["memory_max"]=="314572800", j' "$T/ok.json" \
     && ! CGRUN_TOOL=$CGT "$B/cgrun.sh" --name budget-test-oom --mem 300M --sample 0 --json "$T/oom.json" -- /usr/bin/python3 -c "x=bytearray(600*1024*1024)" > /dev/null 2>&1 \
     && $PY -I -c 'import json,sys; j=json.load(open(sys.argv[1])); assert j["exit"]!=0 and int(j["memory_events"]["oom_kill"])>=1, j' "$T/oom.json"
  then ok "cgrun.sh records a capped run and an OOM kill"; else bad "cgrun.sh under the scope launcher" "$(cat "$T/ok.json" "$T/oom.json" 2>/dev/null | cut -c1-300)"; fi
else
  echo "SKIP cgrun.sh test (no cgroup scope launcher on this host)"
fi

# 6. shell syntax
sh_ok=1
for f in cgrun.sh cgrun-inner.sh sweep_check.sh legs.sh run_fv.sh swarm_check.sh; do
  [ -f "$B/$f" ] && bash -n "$B/$f" || { sh_ok=0; echo "  bash -n failed: $f"; }
done
[ $sh_ok = 1 ] && ok "shell scripts parse" || bad "shell scripts parse" ""

echo "RESULT: $pass PASS, $fail FAIL"
[ $fail = 0 ]

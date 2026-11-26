#!/bin/bash
# test-fvserve-437.sh [WORK] : the attempt service on a Lean 4.37.0-rc1 problem set with the 4.37 trusted check (D07).
# Needs: the 4.37.0-rc1 toolchain (config/components.json lean_toolchains, tools/addrelease.py), D23's 4.37 judge binaries
# (check/sound/pins-437.env paths) and a BUILT 4.37 Mathlib workspace: env FV437_PACKAGES (e.g. a copy of a
# ml-v4.37.0-rc1 workspace; Mathlib 31ce06ea). Without them: RESULT SKIP. ~5 min on 16 threads.
#   1. official flow (bin/fastverify --preset reference) on a 12-problem batch project switched to 4.37 -> problem set
#   2. fvserve --svc-check --pins check/sound/pins-437.env --fork-server (fvfork built with 4.37) --limits (the recommended
#      per-attempt limits, DAILY D07-isolation): 12 honest ACCEPTED, 6 cheat
#      variants REJECTED (6 concurrent clients), the 4.37 native exporter and the 4.37 pins in use, fork compiles > 0
#   3. tools/batchverify.py --pins check/sound/pins-437.env: the 12 honest attempts and the 6 cheats (two batches, files named
#      by theorem): the same verdicts
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)               # tools/guard
FASTVERIFY=${FASTVERIFY:-$(cd "$H/../.." && pwd)}
W=${1:-${SCRATCH:-/scratch}/$USER-fvserve-437-test}; rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
T=${EVAL_THREADS:-16}; WS=${FV437_PACKAGES:-}
TC=$(python3 -I -c 'import json,sys; t=json.load(open(sys.argv[1]))["lean_toolchains"].get("leanprover/lean4:v4.37.0-rc1"); print(t["prefix"] if t else "")' "$FASTVERIFY/config/components.json")
TC=${TC437:-$TC}
skip() { echo "SKIP: $*"; echo "RESULT SKIP"; exit 0; }
[ -n "$TC" ] && [ -x "$TC/bin/lean" ] || skip "no 4.37.0-rc1 toolchain (tools/addrelease.py 4.37.0-rc1)"
[ -n "$WS" ] && [ -f "$WS/lake-manifest.json" ] && grep -q "v4.37.0-rc1" "$WS/lean-toolchain" 2>/dev/null || skip "set FV437_PACKAGES to a built 4.37.0-rc1 Mathlib workspace"
while read -r _ _ _ path; do [ -x "$path" ] || [ -f "$path" ] || skip "4.37 judge component missing here: $path"; done < <(grep '^PIN ' "$FASTVERIFY/check/sound/pins-437.env")
bad=0; ok() { echo "PASS $*"; }; no() { echo "FAIL $*"; bad=1; }
NAMES=lia_chicken,rfl_nat_mul,dec_zmod,lia_two_consec,alg_diff_squares,amc_sum_1_to_100,lia_div3,lia_bound,lia_ages,lia_floor_div,lia_system,lia_mod_comb
python3 -I "$FASTVERIFY/bench/throughput/corpus/gen.py" "$W/corpus" --names "$NAMES" > /dev/null || { no "gen.py"; echo "RESULT FAIL"; exit 1; }
python3 -I - "$W/corpus" "$WS" <<'PY' || { echo "FAIL switch to 4.37"; echo "RESULT FAIL"; exit 1; }
import json, os, re, sys
root, ws = sys.argv[1], sys.argv[2]
man = json.load(open(os.path.join(ws, "lake-manifest.json")))
rev = next(p["rev"] for p in man["packages"] if p["name"] == "mathlib")
tcl = open(os.path.join(ws, "lean-toolchain")).read()
for d, _, fs in os.walk(root):
    if "lean-toolchain" in fs:
        open(os.path.join(d, "lean-toolchain"), "w").write(tcl)
        if "lake-manifest.json" in fs:
            m = json.load(open(os.path.join(d, "lake-manifest.json"))); m2 = dict(man); m2["name"] = m["name"]
            json.dump(m2, open(os.path.join(d, "lake-manifest.json"), "w"), indent=1)
        if "lakefile.toml" in fs:
            p = os.path.join(d, "lakefile.toml"); txt = open(p).read()   # read BEFORE opening for writing (truncates)
            open(p, "w").write(re.sub(r'rev = "[0-9a-f]+"', f'rev = "{rev}"', txt))
PY
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FASTVERIFY/bin/fastverify" "$W/corpus/projects/BATCH" "$W/corpus/challenges/BATCH" \
    "$W/ref" --preset reference --threads "$T" --packages "$WS" > "$W/ref.log" 2>&1
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/ref/result.json" 2>/dev/null)
[ "$v" = ACCEPTED ] && ok "official 4.37 flow on the batch project: ACCEPTED" || { no "official 4.37 flow: $v (see $W/ref.log)"; echo "RESULT FAIL"; exit 1; }
mkdir -p "$W/pset" && cp "$W/ref/challenge.export" "$W/corpus/challenges/BATCH/comparator.json" "$W/pset/"
SHA=$(sha256sum "$W/pset/challenge.export" | cut -d' ' -f1)
python3 -I - "$W/corpus" "$W/att" <<'PY'
import json, os, sys
root, out = sys.argv[1], sys.argv[2]; os.makedirs(out)
exp = {}
for case, c in json.load(open(os.path.join(root, "cases.json"))).items():
    if case == "BATCH":
        continue
    exp[case] = {"theorem": c["challenge"], "expect": c["expected_official"], "kind": c.get("kind")}
    open(os.path.join(out, case + ".lean"), "w").write(open(os.path.join(root, "projects", case, "Solution.lean")).read())
json.dump(exp, open(os.path.join(out, "expect.json"), "w"), indent=1)
PY
FK=(); if bash "$FASTVERIFY/tools/fvserve/fork/build.sh" "$TC" "$W/fvfork" > "$W/fvfork.log" 2>&1; then FK=(--fork-server "$W/fvfork/fvfork"); ok "fvfork built with 4.37.0-rc1"; else no "fvfork does not build with 4.37.0-rc1 ($W/fvfork.log)"; fi
S=$W/svc
python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" serve --state "$S" --pset "t=$W/pset:$SHA" --threads "$T" --packages "$WS" --toolchain "$TC" \
    --fv "$FASTVERIFY" --svc-check --pins check/sound/pins-437.env "${FK[@]}" --attempt-timeout 120 \
    --limits 'mem=2G,nproc=512,procs=64,threads=256,out=16M,disk=64M,fsize=64M,cpu=120' > "$S.log" 2>&1 &
for i in $(seq 1 400); do grep -q '"ready"' "$S.log" 2>/dev/null && break; kill -0 $! 2>/dev/null || break; sleep 1; done
if grep -q '"ready"' "$S.log"; then
  python3 -I - "$S.log" <<'PY' && ok "service ready with the 4.37 pins and the 4.37 native exporter" || no "service configuration: $(grep -o '"ready".*' "$S.log" | cut -c1-300)"
import json, sys
r = next(json.loads(l) for l in open(sys.argv[1]) if '"ready"' in l)
sys.exit(0 if r.get("check_pins") == "pins-437.env" and "v4.37.0-rc1" in r.get("native_exporter", "") and r.get("confirm_failures") in ("all", "errors") else 1)
PY
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S" "$W/att" > "$W/svc.verdicts.txt" 2>&1 <<'PY'
import concurrent.futures as cf, json, os, sys
sys.path.insert(0, sys.argv[1]); import fvserve
st, att = sys.argv[2], sys.argv[3]
exp = json.load(open(os.path.join(att, "expect.json")))
def one(c):
    r = fvserve.request(st, {"op": "verify", "pset": "t", "theorem": exp[c]["theorem"], "source": open(os.path.join(att, c + ".lean")).read()}, timeout=900)
    return c, r.get("verdict"), (r.get("why") or "")[:140]
bad = 0
with cf.ThreadPoolExecutor(6) as ex:
    for c, v, why in ex.map(one, sorted(exp)):
        bad += v != exp[c]["expect"]
        print(("ok   " if v == exp[c]["expect"] else "WRONG"), c, v, "expected", exp[c]["expect"], why if v != "ACCEPTED" else "")
st_ = fvserve.request(st, {"op": "stats"}, 30)
print("stats", json.dumps(st_.get("verdicts")))
sys.exit(1 if bad else 0)
PY
  r=$?; n=$(grep -c '^ok ' "$W/svc.verdicts.txt"); [ $r = 0 ] && ok "fvserve --pins 4.37: $n/18 verdicts as the official flow's ($(tail -1 "$W/svc.verdicts.txt"))" || no "fvserve --pins 4.37: $(grep WRONG "$W/svc.verdicts.txt" | head -3 | tr '\n' ' ' | cut -c1-400)"
  [ ${#FK[@]} = 0 ] || { grep -q '"fork_compiles": [1-9]' "$W/svc.verdicts.txt" && ok "the 4.37 fork server compiled attempts" || no "no fork compile on 4.37"; }
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S" > /dev/null; sleep 2
else
  no "4.37 service did not start: $(tail -3 "$S.log" | tr '\n' ' ' | cut -c1-300)"
fi
# batchverify names attempts by theorem (FILE = <theorem>.lean): the honest set and the cheat set (distinct theorems) are two batches
python3 -I - "$W/att" "$W/bvh" "$W/bvc" <<'PY'
import json, os, shutil, sys
att, h, c = sys.argv[1:4]; os.makedirs(h); os.makedirs(c)
for case, e in json.load(open(os.path.join(att, "expect.json"))).items():
    shutil.copy(os.path.join(att, case + ".lean"), os.path.join(h if case == e["theorem"] else c, e["theorem"] + ".lean"))
PY
for set in h c; do
  python3 -I "$FASTVERIFY/tools/batchverify.py" --pset "$W/pset" --attempts "$W/bv$set" --out "$W/bvout$set" --challenge-sha256 "$SHA" \
      --threads "$T" --packages "$WS" --toolchain "$TC" --fv "$FASTVERIFY" --pins check/sound/pins-437.env --attempt-timeout 120 > "$W/bv$set.log" 2>&1
done
python3 -I - "$W" <<'PY' && ok "batchverify --pins 4.37: 12 honest ACCEPTED, 6 cheats REJECTED (two batches)" || no "batchverify --pins 4.37: $(tail -1 "$W/bvh.log" | cut -c1-200) / $(tail -1 "$W/bvc.log" | cut -c1-200)"
import json, os, sys
W = sys.argv[1]
exp = json.load(open(os.path.join(W, "att", "expect.json")))
bad = []
for set, honest in (("h", True), ("c", False)):
    got = json.load(open(os.path.join(W, "bvout" + set, "batch.json")))["attempts"]
    for case, e in exp.items():
        if (case == e["theorem"]) != honest:
            continue
        g = (got.get(e["theorem"]) or {}).get("verdict")
        if g != e["expect"]:
            bad.append((case, g, e["expect"], (got.get(e["theorem"]) or {}).get("why", "")[:100]))
print("wrong:", bad) if bad else None
sys.exit(1 if bad else 0)
PY
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

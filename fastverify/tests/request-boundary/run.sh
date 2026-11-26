#!/bin/bash
# Uniform request-boundary test suite.
# Verifies across ALL 9 live fastverify entry points that:
#   - Challenge identity is (challenge.export sha256, comparator.json sha256).
#   - Requests carry SOLUTIONS (code, patches, exports), NEVER trust parameters
#     (challenge, comparator config, permitted_axioms, pins, target theorem).
#   - Every forged trust parameter fails closed (REJECTED / DECLINED / ERROR, reward=0.0, NEVER ACCEPTED).
#
# Usage: fastverify/tests/request-boundary/run.sh [WORK_DIR] [THREADS]
set -uo pipefail
export FV_EXPERIMENTAL_CI=1   # the CI check (fv-ci.sh / bin/fv ci) is EXPERIMENTAL in v0.1 and runs only when opted in
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=$(cd "$HERE/../.." && pwd)
W=${1:-/tmp/fv-b4-$$}
T=${2:-8}
mkdir -p "$W"
W=$(readlink -f "$W")

PASS=0; BAD=0
ok() { echo "PASS $*"; PASS=$((PASS+1)); }
no() { echo "FAIL $*"; BAD=$((BAD+1)); }

TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json")

cleanup() {
  python3 -I "$FV/tools/fvserve/fvserve.py" stop --state "$W/fvs" >/dev/null 2>&1 || true
  python3 -I "$FV/tools/fvwork/fvwork.py" stop --state "$W/fvw" >/dev/null 2>&1 || true
  python3 -I "$FV/check/warm/fvcheckd.py" stop --state "$W/fvc" >/dev/null 2>&1 || true
  kill ${API_PID:-} ${FVS_PID:-} ${FVW_PID:-} ${FVC_PID:-} 2>/dev/null || true
  wait ${API_PID:-} ${FVS_PID:-} ${FVW_PID:-} ${FVC_PID:-} 2>/dev/null || true
}
trap cleanup EXIT

# --------------------------------------------------------------------------- Setup fixtures (Init-only, fast)
mkdir -p "$W/chal_src" "$W/proj_good" "$W/proj_sorry" "$W/proj_bp" "$W/empty_ws/.lake/packages"
printf 'leanprover/lean4:v4.33.1\n' > "$W/chal_src/lean-toolchain"
cat > "$W/chal_src/lakefile.toml" <<'EOF'
name = "B4"
defaultTargets = ["B4"]
[[lean_lib]]
name = "B4"
EOF
printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n' > "$W/chal_src/lake-manifest.json"
cat > "$W/chal_src/B4.lean" <<'EOF'
theorem b4_thm : ∀ n : Nat, n + 0 = n := by sorry
theorem b4_other : True := by sorry
EOF
cat > "$W/chal_src/comparator.json" <<'EOF'
{"challenge_module":"B4","solution_module":"B4","theorem_names":["b4_thm","b4_other"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}
EOF

cp -a "$W/chal_src/." "$W/proj_good/"
cat > "$W/proj_good/B4.lean" <<'EOF'
theorem b4_thm : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n
theorem b4_other : True := True.intro
EOF

cp -a "$W/chal_src/." "$W/proj_sorry/"
cp -a "$W/chal_src/." "$W/proj_bp/"
cat > "$W/proj_bp/B4.lean" <<'EOF'
theorem b4_helper (n : Nat) : n + 0 = n := by sorry
theorem b4_thm : ∀ n : Nat, n + 0 = n := fun n => b4_helper n
theorem b4_other : True := True.intro
EOF

# Official pinned challenge (B0+E0)
"$FV/bin/fv" init-challenge "$W/chal_src" "$W/pinned_chal" --threads "$T" --json > "$W/init.json" || { no "setup init-challenge"; exit 1; }
PIN=$(awk '{print $1}' "$W/pinned_chal/challenge.export.sha256")
CFG_PIN=$(sha256sum "$W/pinned_chal/comparator.json" | awk '{print $1}')

# Forged challenge: identical challenge.export (matches PIN!) + forged comparator.json permitting sorryAx!
mkdir -p "$W/forged_chal"
cp "$W/pinned_chal/challenge.export" "$W/forged_chal/challenge.export"
cat > "$W/forged_chal/comparator.json" <<'EOF'
{"challenge_module":"B4","solution_module":"B4","theorem_names":["b4_thm","b4_other"],"definition_names":[],"permitted_axioms":["propext","Quot.sound","Classical.choice","sorryAx"]}
EOF

# Evil pins file (outside check/sound/, bogus sha256)
cat > "$W/evil_pins.env" <<'EOF'
TC_VERSION=leanprover/lean4:v4.36.0
PIN ccmp 0000000000000000000000000000000000000000000000000000000000000000 /bin/true
PIN pleanchecker 0000000000000000000000000000000000000000000000000000000000000000 /bin/true
PIN gruszka 0000000000000000000000000000000000000000000000000000000000000000 /bin/true
EOF

# --------------------------------------------------------------------------- 1. bin/fastverify
"$FV/bin/fastverify" "$W/proj_good" "$W/pinned_chal" "$W/fv_good" --preset sound-auto \
  --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --export-dir none --build B0 --threads "$T" > "$W/fv_good.log" 2>&1
rc_good=$?
"$FV/bin/fastverify" "$W/proj_good" "$W/pinned_chal" "$W/fv_evil_pins" --preset sound-auto \
  --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --pins "$W/evil_pins.env" --build B0 --threads "$T" > "$W/fv_evil_pins.log" 2>&1
rc_ep=$?
"$FV/bin/fastverify" "$W/proj_good" "$W/pinned_chal" "$W/fv_trav_pins" --preset sound-auto \
  --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --pins "$FV/check/sound/../../tmp/nonexistent.env" --build B0 --threads "$T" > "$W/fv_trav_pins.log" 2>&1
rc_tp=$?
"$FV/bin/fastverify" "$W/proj_good" "$W/pinned_chal" "$W/fv_badpin" --preset sound-auto \
  --challenge-sha256 "0000000000000000000000000000000000000000000000000000000000000000" --comparator-sha256 "$CFG_PIN" --build B0 --threads "$T" > "$W/fv_badpin.log" 2>&1
rc_bp=$?
python3 -I - "$W/fv_good/result.json" "$PIN" "$CFG_PIN" "$rc_good" "$rc_ep" "$rc_tp" "$rc_bp" <<'PY' \
  && ok "boundary [1/10] bin/fastverify: records (challenge_export, comparator_config) sha256 pair; refuses external/traversal --pins & bad pin" \
  || no "boundary [1/10] bin/fastverify failed"
import json, sys
r = json.load(open(sys.argv[1]))
pin, cfg_pin = sys.argv[2], sys.argv[3]
rc_g, rc_ep, rc_tp, rc_bp = [int(x) for x in sys.argv[4:8]]
assert rc_g == 0 and r["verdict"] == "ACCEPTED", r
assert r["inputs"]["challenge_export"]["sha256"] == pin, r["inputs"]
assert r["inputs"]["comparator_config"]["sha256"] == cfg_pin, r["inputs"]
assert rc_ep == 2 and rc_tp == 2 and rc_bp == 2, (rc_ep, rc_tp, rc_bp)
PY

# --------------------------------------------------------------------------- 2. bin/fv CLI
"$FV/bin/fv" verify "$W/proj_sorry" --challenge "$W/forged_chal" --challenge-sha256 "$PIN" \
  --comparator-sha256 "$CFG_PIN" --build B0 --threads "$T" --json > "$W/cli_v_forged.json"
rc_cv=$?
"$FV/bin/fv" check "$W/pinned_chal/challenge.export" --challenge "$W/forged_chal" --challenge-sha256 "$PIN" \
  --comparator-sha256 "$CFG_PIN" --threads "$T" --json > "$W/cli_c_forged.json"
rc_cc=$?
"$FV/bin/fv" verify "$W/proj_good" --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" \
  --pins "$W/evil_pins.env" --build B0 --threads "$T" --json > "$W/cli_v_evilpins.json"
rc_cp=$?
python3 -I - "$W" "$rc_cv" "$rc_cc" "$rc_cp" <<'PY' \
  && ok "boundary [2/10] bin/fv CLI: forged comparator.json refused (ERROR, reward=0.0) in verify/check; arbitrary --pins refused" \
  || no "boundary [2/10] bin/fv CLI failed"
import json, os, sys
w, r1, r2, r3 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
j1 = json.load(open(os.path.join(w, "cli_v_forged.json")))
j2 = json.load(open(os.path.join(w, "cli_c_forged.json")))
j3 = json.load(open(os.path.join(w, "cli_v_evilpins.json")))
assert r1 == 2 and j1["verdict"] == "ERROR" and j1["reward"] == 0.0 and "comparator" in j1["reason"].lower(), j1
assert r2 == 2 and j2["verdict"] == "ERROR" and j2["reward"] == 0.0 and "comparator" in j2["reason"].lower(), j2
assert r3 == 2 and j3["verdict"] == "ERROR" and j3["reward"] == 0.0 and j3["accepted"] is False, j3
PY

# --------------------------------------------------------------------------- 3. fastverify-mcp
python3 -I - "$FV" "$W" "$PIN" "$CFG_PIN" <<'PY' \
  && ok "boundary [3/10] fastverify-mcp: forged comparator refused (unpinned & mismatched), --challenge registry rejects sorryAx, arbitrary pins refused on verify & check" \
  || no "boundary [3/10] fastverify-mcp failed"
import json, os, subprocess, sys
fv, w, pin, cfg_pin = sys.argv[1:5]
mcp = os.path.join(fv, "tools", "mcp", "fastverify-mcp")
reqs = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
    # (a) forged comparator with NO comparator_sha256
    {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "pinned_chal", "challenge.export"),
        "challenge_export": os.path.join(w, "forged_chal", "challenge.export"),
        "comparator_json": os.path.join(w, "forged_chal", "comparator.json"),
        "challenge_sha256": pin,
    }}},
    # (b) forged comparator with REAL comparator_sha256
    {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "pinned_chal", "challenge.export"),
        "challenge_export": os.path.join(w, "forged_chal", "challenge.export"),
        "comparator_json": os.path.join(w, "forged_chal", "comparator.json"),
        "challenge_sha256": pin,
        "comparator_sha256": cfg_pin,
    }}},
    # (c) forged comparator in fv_verify_project
    {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
        "project_dir": os.path.join(w, "proj_sorry"),
        "challenge_dir": os.path.join(w, "forged_chal"),
        "challenge_sha256": pin,
    }}},
    # (d) server-registered challenge rejects sorryAx export
    {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "pinned_chal", "challenge.export"),
        "challenge_id": "b4reg",
    }}},
    # (e) caller arbitrary pins path in fv_check_export
    {"jsonrpc": "2.0", "id": 6, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
        "export_file": os.path.join(w, "fv_good", "solution.export"),
        "challenge_id": "b4reg",
        "pins": os.path.join(w, "evil_pins.env"),
    }}},
    # (f) caller arbitrary pins path in fv_verify_project
    {"jsonrpc": "2.0", "id": 7, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
        "project_dir": os.path.join(w, "proj_good"),
        "challenge_id": "b4reg",
        "pins": os.path.join(w, "evil_pins.env"),
    }}},
]
p = subprocess.run(
    [mcp, "--allow-root", w, "--challenge", f"b4reg={os.path.join(w, 'pinned_chal')}:{pin}:{cfg_pin}"],
    input="".join(json.dumps(r) + "\n" for r in reqs).encode(),
    capture_output=True, timeout=90,
)
assert p.returncode == 0, p.stderr.decode()
by = {r["id"]: r["result"]["structuredContent"] for r in (json.loads(l) for l in p.stdout.decode().splitlines() if l.strip()) if r.get("id") in range(2, 8)}
for k in (2, 3, 4, 6, 7):
    assert by[k]["verdict"] == "ERROR" and by[k]["accepted"] is False and by[k]["reward"] == 0.0, (k, by[k])
assert by[5]["verdict"] == "REJECTED" and by[5]["accepted"] is False and by[5]["reward"] == 0.0, by[5]
PY

# --------------------------------------------------------------------------- 4. tools/ci-action/fv-ci.sh
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_sorry" --challenge "$W/forged_chal" \
  --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --out-dir "$W/ci_forged" --build B0 --threads "$T" > "$W/ci_forged.log" 2>&1
rc_cif=$?
"$FV/tools/ci-action/fv-ci.sh" --project "$W/proj_good" --challenge "$W/pinned_chal" \
  --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --pins "$W/evil_pins.env" --out-dir "$W/ci_evil" --build B0 --threads "$T" > "$W/ci_evil.log" 2>&1
rc_cie=$?
if [ "$rc_cif" = 2 ] && [ "$rc_cie" = 2 ]; then
  ok "boundary [4/10] tools/ci-action/fv-ci.sh: forged comparator.json & arbitrary --pins both fail closed (exit 2)"
else
  no "boundary [4/10] fv-ci.sh failed (rc_cif=$rc_cif, rc_cie=$rc_cie)"
fi

# --------------------------------------------------------------------------- 5 & 6. tools/fvserve + tools/http/fvapi.py
python3 -I "$FV/tools/fvserve/fvserve.py" serve \
  --state "$W/fvs" --pset "b4=$W/pinned_chal:$PIN" \
  --packages "$W/empty_ws" --toolchain "$TC" --fv "$FV" \
  --snapshot-header "import Init" --threads "$T" --svc-check > "$W/fvs.log" 2>&1 &
FVS_PID=$!
for _ in $(seq 1 60); do grep -q '"ready"' "$W/fvs.log" 2>/dev/null && break; sleep 0.5; done
grep -q '"ready"' "$W/fvs.log" || { no "setup fvserve failed"; exit 1; }

python3 -I - "$FV" "$W" <<'PY' \
  && ok "boundary [5/10] tools/fvserve: injected comparator/permitted_axioms/challenge/pins keys ignored -> sorry REJECTED, honest ACCEPTED" \
  || no "boundary [5/10] tools/fvserve failed"
import json, os, sys
fv, w = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(fv, "tools", "fvserve"))
import fvserve
forged_cfg = json.load(open(os.path.join(w, "forged_chal", "comparator.json")))
# Attempt with sorry + injected trust parameters in JSON request
r_bad = fvserve.request(os.path.join(w, "fvs"), {
    "op": "verify", "pset": "b4", "theorem": "b4_thm",
    "source": "import Init\ntheorem b4_thm : ∀ n : Nat, n + 0 = n := by sorry\n",
    "comparator": forged_cfg,
    "comparator_json": os.path.join(w, "forged_chal", "comparator.json"),
    "challenge": os.path.join(w, "forged_chal"),
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice", "sorryAx"],
    "pins": os.path.join(w, "evil_pins.env"),
}, timeout=60)
assert r_bad.get("verdict") == "REJECTED", r_bad
r_ok = fvserve.request(os.path.join(w, "fvs"), {
    "op": "verify", "pset": "b4", "theorem": "b4_thm",
    "source": "import Init\ntheorem b4_thm : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\n",
}, timeout=60)
assert r_ok.get("verdict") == "ACCEPTED", r_ok
PY

python3 -I "$FV/tools/http/fvapi.py" --fvserve-state "$W/fvs" --default-pset b4 \
  --custom-id-is-theorem --host 127.0.0.1 --port 0 > "$W/api.log" 2>&1 &
API_PID=$!
for _ in $(seq 1 30); do grep -q '"ready"' "$W/api.log" 2>/dev/null && break; sleep 0.2; done
API_URL=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["url"])' "$W/api.log")

python3 -I - "$API_URL" "$W" <<'PY' \
  && ok "boundary [6/10] tools/http/fvapi.py: injected trust keys rejected, cross-problem credit theft blocked, unknown pset fails closed" \
  || no "boundary [6/10] fvapi.py failed"
import json, os, sys, urllib.request
url, w = sys.argv[1], sys.argv[2]
def post(path, obj):
    req = urllib.request.Request(url + path, data=json.dumps(obj).encode(),
                                 headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.status, json.loads(r.read().decode())

# (a) sorry + injected trust parameters
st, r1 = post("/v1/verify", {
    "theorem": "b4_thm",
    "source": "import Init\ntheorem b4_thm : ∀ n : Nat, n + 0 = n := by sorry\n",
    "comparator_json": os.path.join(w, "forged_chal", "comparator.json"),
    "permitted_axioms": ["sorryAx"],
    "pins": os.path.join(w, "evil_pins.env"),
})
assert st == 200 and r1["verdict"] == "REJECTED" and r1["accepted"] is False and r1["reward"] == 0.0, r1

# (b) cross-problem credit theft: prove b4_other (True) while claiming custom_id=b4_thm
st, r2 = post("/api/check", {
    "pset": "b4",
    "codes": [{"custom_id": "b4_thm", "proof": "import Init\ntheorem b4_other : True := True.intro\n"}],
})
assert st == 200 and r2["accepted_count"] == 0 and r2["results"][0]["reward"] == 0.0, r2

# (c) unknown/forged pset -> never accepted
st, r3 = post("/v1/verify", {
    "pset": "forged_nonexistent",
    "theorem": "b4_thm",
    "source": "import Init\ntheorem b4_thm : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\n",
})
assert r3["accepted"] is False and r3["reward"] == 0.0, r3
PY

# --------------------------------------------------------------------------- 7. tools/fvwork
python3 -I "$FV/tools/fvwork/fvwork.py" init --state "$W/fvw" --project "$W/proj_good" \
  --challenge "$W/pinned_chal" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --packages "$W/empty_ws" \
  --threads "$T" --fv "$FV" --tc "$TC" > "$W/fvw_init.log" 2>&1 || { no "setup fvwork init failed"; exit 1; }   # pin required
python3 -I "$FV/tools/fvwork/fvwork.py" serve --state "$W/fvw" --jobs 2 --warm 0 --threads "$T" > "$W/fvw_srv.log" 2>&1 &
FVW_PID=$!
for _ in $(seq 1 40); do [ -S "$W/fvw/sock" ] && break; sleep 0.25; done
[ -S "$W/fvw/sock" ] || { no "setup fvwork serve failed"; exit 1; }

python3 -I - "$FV" "$W" <<'PY' \
  && ok "boundary [7/10] tools/fvwork: injected comparator/permitted_axioms/challenge/pins keys ignored -> sorry patch REJECTED, honest patch ACCEPTED" \
  || no "boundary [7/10] tools/fvwork failed"
import json, os, sys
fv, w = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(fv, "tools", "fvserve"))
import fvserve
forged_cfg = json.load(open(os.path.join(w, "forged_chal", "comparator.json")))
r_bad = fvserve.request(os.path.join(w, "fvw"), {
    "op": "verify",
    "files": {"B4.lean": "theorem b4_thm : ∀ n : Nat, n + 0 = n := by sorry\ntheorem b4_other : True := True.intro\n"},
    "advance": False,
    "comparator": forged_cfg,
    "comparator_json": os.path.join(w, "forged_chal", "comparator.json"),
    "challenge": os.path.join(w, "forged_chal"),
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice", "sorryAx"],
    "pins": os.path.join(w, "evil_pins.env"),
}, timeout=90)
assert r_bad.get("verdict") == "REJECTED", r_bad
r_ok = fvserve.request(os.path.join(w, "fvw"), {
    "op": "verify",
    "files": {"B4.lean": "theorem b4_thm : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n\ntheorem b4_other : True := True.intro\n"},
    "advance": False,
}, timeout=90)
assert r_ok.get("verdict") == "ACCEPTED", r_ok
PY

# --------------------------------------------------------------------------- 8. check/warm/fvcheckd.py
python3 -I "$FV/check/warm/fvcheckd.py" serve \
  --state "$W/fvc_bad" --challenge "$W/forged_chal/challenge.export" --challenge-sha256 "$PIN" \
  --config "$W/forged_chal/comparator.json" --base "$W/fv_good/solution.export" --threads "$T" > "$W/fvc_bad.log" 2>&1
rc_fvc_bad=$?
python3 -I "$FV/check/warm/fvcheckd.py" serve \
  --state "$W/fvc" --challenge "$W/pinned_chal/challenge.export" --challenge-sha256 "$PIN" \
  --config "$W/pinned_chal/comparator.json" --config-sha256 "$CFG_PIN" \
  --base "$W/fv_good/solution.export" --threads "$T" > "$W/fvc.log" 2>&1 &
FVC_PID=$!
for _ in $(seq 1 60); do [ -S "$W/fvc/sock" ] && break; sleep 0.5; done
[ -S "$W/fvc/sock" ] || { no "setup fvcheckd serve failed: $(tail -5 "$W/fvc.log")"; exit 1; }
: > "$W/empty.delta"
python3 -I "$FV/check/warm/fvcheckd.py" check-delta --state "$W/fvc" \
  --delta "$W/empty.delta" --config "$W/forged_chal/comparator.json" > "$W/fvc_q_forged.json" 2>&1
rc_fvc_q=$?
python3 -I - "$rc_fvc_bad" "$rc_fvc_q" "$W/fvc_q_forged.json" <<'PY' \
  && ok "boundary [8/10] check/warm/fvcheckd.py: sorryAx --config refused at startup; mismatched query --config DECLINED (exit 2)" \
  || no "boundary [8/10] fvcheckd.py failed"
import json, sys
rc_bad, rc_q = int(sys.argv[1]), int(sys.argv[2])
txt = open(sys.argv[3]).read().strip()
assert rc_bad != 0, f"fvcheckd started with sorryAx config! rc={rc_bad}"
assert rc_q == 2, f"expected DECLINED exit 2, got {rc_q}: {txt}"
j = json.loads(txt.splitlines()[-1])
assert j.get("verdict") == "DECLINED", j
PY

# --------------------------------------------------------------------------- 9. tools/subcontract
python3 -I "$FV/tools/subcontract/mint.py" --experimental "$W/proj_bp" "$W/pinned_chal" "$W/sub_mint" \
  --challenge-sha256 "$PIN" --comparator-sha256 "$(sha256sum "$W/pinned_chal/comparator.json" | cut -d' ' -f1)" \
  --threads "$T" > "$W/sub_mint.log" 2>&1   # (comparator pin required with the challenge pin)
rc_sm=$?
python3 -I - "$FV" "$W" "$rc_sm" "$T" <<'PY' \
  && ok "boundary [9/10] tools/subcontract: mint pins comparator_sha256; tampering comparator.json -> NO_VERDICT / SUBCHALLENGE_TAMPERED" \
  || no "boundary [9/10] tools/subcontract failed"
import json, os, subprocess, sys
fv, w, rc_sm, t = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
assert rc_sm == 0, open(os.path.join(w, "sub_mint.log")).read()[-400:]
mp = os.path.join(w, "sub_mint", "manifest.json")
m = json.load(open(mp))
task = m["subchallenges"][0]
assert task.get("comparator_sha256") and task.get("subchallenge_sha256"), task
# Tamper with minted comparator.json by adding sorryAx
task_detail = json.load(open(task["task_json"]))
cp = task_detail["comparator_json"]
cfg = json.load(open(cp))
cfg["permitted_axioms"] = list(cfg.get("permitted_axioms") or []) + ["sorryAx"]
open(cp, "w").write(json.dumps(cfg, indent=2) + "\n")
sub_f = os.path.join(w, "sub_sorry.lean")
open(sub_f, "w").write("theorem b4_helper (n : Nat) : n + 0 = n := by sorry\n")
out_j = os.path.join(w, "sub_out.json")
p = subprocess.run(
    ["/usr/bin/python3", "-I", os.path.join(fv, "tools", "subcontract", "subverify.py"), "--experimental",
     mp, task["lemma"], sub_f, "--threads", t, "--out", out_j],
    capture_output=True, text=True, timeout=60,
)
res = json.load(open(out_j))
assert res.get("verdict") == "NO_VERDICT" and res.get("category") == "SUBCHALLENGE_TAMPERED", (p.returncode, res)
PY

# --------------------------------------------------------------------------- 10. Direct trusted wrappers (--pins integrity)
"$FV/check/sound/check-sound.sh" "$W/fv_good/solution.export" "$W/pinned_chal/challenge.export" "$W/pinned_chal/comparator.json" \
  --pins "$W/evil_pins.env" --threads "$T" --json "$W/cs_evil.json" --log "$W/cs_evil.log" >/dev/null 2>&1
rc_cs=$?
"$FV/check/frontier/check-frontier.sh" "$W/fv_good/solution.export" "$W/pinned_chal/challenge.export" "$W/pinned_chal/comparator.json" \
  --pins "$W/evil_pins.env" --threads "$T" --json "$W/cf_evil.json" --log "$W/cf_evil.log" >/dev/null 2>&1
rc_cf=$?
if [ "$rc_cs" = 2 ] && [ "$rc_cf" = 2 ]; then
  ok "boundary [10/10] check-sound.sh & check-frontier.sh: forged --pins file fails closed (DECLINED, exit 2)"
else
  no "boundary [10/10] direct wrappers failed (rc_cs=$rc_cs, rc_cf=$rc_cf)"
fi

echo "SUMMARY: PASS=$PASS FAIL=$BAD"
[ "$BAD" = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit "$BAD"

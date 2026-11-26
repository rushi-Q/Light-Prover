#!/bin/bash
# tests/service-boundary/run.sh — regression suite for service/CLI boundary fixes (MCP, export-check entry points, CI, CLI).
set -euo pipefail
export FV_EXPERIMENTAL_CI=1   # the CI gate (fv-ci.sh / bin/fv ci) is EXPERIMENTAL in v0.1 and runs only when opted in
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
W=$(mktemp -d "${TMPDIR:-/tmp}/fv-service-boundary.XXXXXX")
trap 'rm -rf "$W"' EXIT

python3 -I - "$FV" "$W" <<'PY'
import hashlib, json, os, shutil, subprocess, sys

fv, w = sys.argv[1], sys.argv[2]
mcp_bin = os.path.join(fv, "tools", "mcp", "fastverify-mcp")
fv_bin = os.path.join(fv, "bin", "fv")
fv_lm = os.path.join(fv, "tools", "lowmem", "fv_lowmem.py")
fv_ci = os.path.join(fv, "tools", "ci-action", "fv-ci.sh")
selftest = "/scratch/fastverify-next/selftest"

def sha256_file(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

def mcp_call(args, reqs, cwd=None):
    p = subprocess.run(
        [mcp_bin] + args,
        input="".join(json.dumps(r) + "\n" for r in reqs).encode("utf-8"),
        capture_output=True, timeout=120, cwd=cwd,
    )
    assert p.returncode == 0, p.stderr.decode()
    out = {}
    for ln in p.stdout.decode().splitlines():
        if ln.strip():
            obj = json.loads(ln)
            if "id" in obj:
                out[obj["id"]] = obj
    return out

# Setup pinned selftest challenge + caller-forged challenge
op_chal = os.path.join(w, "op_chal")
caller_chal = os.path.join(w, "caller_chal")
os.makedirs(op_chal)
os.makedirs(caller_chal)
shutil.copyfile(os.path.join(selftest, "challenge.export"), os.path.join(op_chal, "challenge.export"))
shutil.copyfile(os.path.join(selftest, "comparator.json"), os.path.join(op_chal, "comparator.json"))
op_pin = sha256_file(os.path.join(op_chal, "challenge.export"))
op_cfg_pin = sha256_file(os.path.join(op_chal, "comparator.json"))

shutil.copyfile(os.path.join(selftest, "challenge.export"), os.path.join(caller_chal, "challenge.export"))
bad_cfg = json.load(open(os.path.join(selftest, "comparator.json")))
bad_cfg["permitted_axioms"] = list(bad_cfg["permitted_axioms"]) + ["sorryAx"]
json.dump(bad_cfg, open(os.path.join(caller_chal, "comparator.json"), "w"))
caller_cfg_pin = sha256_file(os.path.join(caller_chal, "comparator.json"))

# Also setup a second valid S1(3) challenge (different target) to verify --challenge registry cannot be bypassed even with S1(3) axioms
alt_chal = os.path.join(w, "alt_chal")
os.makedirs(alt_chal)
shutil.copyfile(os.path.join(selftest, "good.export"), os.path.join(alt_chal, "challenge.export"))
shutil.copyfile(os.path.join(selftest, "comparator.json"), os.path.join(alt_chal, "comparator.json"))
alt_pin = sha256_file(os.path.join(alt_chal, "challenge.export"))

# 1. MCP --challenge registry blocks caller-supplied challenge substitution & unsound presets
resps = mcp_call(
    ["--allow-root", w, "--challenge", f"official={op_chal}:{op_pin}:{op_cfg_pin}"],
    [
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
        {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
            "export_file": os.path.join(selftest, "good.export") if False else os.path.join(op_chal, "challenge.export"),
            "challenge_export": os.path.join(alt_chal, "challenge.export"),
            "comparator_json": os.path.join(alt_chal, "comparator.json"),
            "challenge_sha256": alt_pin,
            "comparator_sha256": op_cfg_pin,
        }}},
        {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_verify_project", "arguments": {
            "project_dir": op_chal,
            "challenge_id": "official",
            "preset": "reference",   # a non-sound preset (fast-exact before its retirement)
        }}},
    ],
)
for k in (2, 3):
    sc = resps[k]["result"]["structuredContent"]
    assert sc["verdict"] == "ERROR" and sc["accepted"] is False and sc["reward"] == 0.0, (k, sc)
print("PASS [1/7] MCP --challenge registry blocks caller challenge substitution & unsound presets")

# 2. MCP empty --allow-root defaults to cwd containment (blocks outside paths)
sub_cwd = os.path.join(w, "sub_cwd")
outside = os.path.join(w, "outside")
os.makedirs(sub_cwd)
os.makedirs(outside)
shutil.copyfile(os.path.join(selftest, "good.export"), os.path.join(outside, "good.export"))
resps_root = mcp_call(
    ["--challenge", f"official={op_chal}:{op_pin}:{op_cfg_pin}"],
    [
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
        {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
            "export_file": os.path.join(outside, "good.export"),
            "challenge_id": "official",
        }}},
    ],
    cwd=sub_cwd,
)
sc_root = resps_root[2]["result"]["structuredContent"]
assert sc_root["verdict"] == "ERROR" and "allowed" in (sc_root.get("reason") or "").lower(), sc_root
print("PASS [2/7] MCP default --allow-root confines file access to cwd")

# 3. Standalone export-check entrypoints enforce check/xversion/xvcheck.py
# (3a) 4.37.0-rc1 challenge export with non-sorried definition_names -> REJECTED (exit 1, reward=0.0)
c437_exp = os.path.join(w, "c437_unsorried.export")
sol437_exp = os.path.join(w, "sol437_unsorried.export")
c437_cfg = os.path.join(w, "c437_cfg.json")
rels = json.load(open(os.path.join(fv, "check", "xversion", "releases.json")))
gh437 = (rels.get("releases") or rels)["4.37.0-rc1"]["githash"]
with open(c437_exp, "w") as f:
    f.write(f'{{"meta":{{"exporter":{{"name":"lean4export","version":"3.1.0"}},"format":{{"version":"3.1.0"}},"lean":{{"version":"4.37.0-rc1","githash":"{gh437}"}}}}}}\n')
    f.write('{"in":1,"str":{"pre":0,"str":"Nat"}}\n')
    f.write('{"in":2,"str":{"pre":0,"str":"target_def"}}\n')
    f.write('{"il":1,"succ":0}\n')
    f.write('{"ie":0,"const":{"name":1,"us":[]}}\n')
    f.write('{"ie":1,"natVal":"0"}\n')
    f.write('{"def":{"name":2,"levelParams":[],"type":0,"value":1,"hints":"opaque","safety":"safe","all":[2]}}\n')
with open(sol437_exp, "w") as f:
    f.write(open(c437_exp).read().replace('"natVal":"0"', '"natVal":"1"'))
json.dump({"challenge_module": "M", "solution_module": "M", "theorem_names": [], "definition_names": ["target_def"],
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, open(c437_cfg, "w"))
c437_pin = sha256_file(c437_exp)
c437_cfg_pin = sha256_file(c437_cfg)

# (3b) Unadmitted Lean 4.25.0 challenge export -> ERROR/DECLINED (exit 2, reward=0.0)
c425_exp = os.path.join(w, "c425.export")
open(c425_exp, "w").write(
    open(c437_exp).read().replace('"4.37.0-rc1"', '"4.25.0"').replace(f'"{gh437}"', '"0000000000000000000000000000000000000000"')
)
c425_cfg = os.path.join(w, "c425_cfg.json")
json.dump({"challenge_module": "M", "solution_module": "M", "theorem_names": ["target_def"], "definition_names": [],
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, open(c425_cfg, "w"))
c425_pin = sha256_file(c425_exp)
c425_cfg_pin = sha256_file(c425_cfg)

for extra_flags in ([], ["--notary"]):
    p = subprocess.run([fv_bin, "check", sol437_exp, "--challenge-export", c437_exp, "--comparator-json", c437_cfg,
                        "--challenge-sha256", c437_pin, "--comparator-sha256", c437_cfg_pin, "--json"] + extra_flags,
                       capture_output=True, text=True)
    d = json.load(io := __import__("io").StringIO(p.stdout))
    assert p.returncode == 1 and d["verdict"] == "REJECTED" and d["reward"] == 0.0 and "not sorried" in d["reason"], (extra_flags, p.returncode, d)

p425 = subprocess.run([fv_bin, "check", c425_exp, "--challenge-export", c425_exp, "--comparator-json", c425_cfg,
                       "--challenge-sha256", c425_pin, "--comparator-sha256", c425_cfg_pin, "--json"],
                      capture_output=True, text=True)
d425 = json.loads(p425.stdout)
assert p425.returncode == 2 and d425["verdict"] == "ERROR" and d425["reward"] == 0.0, (p425.returncode, d425)
p425_437 = subprocess.run([fv_bin, "check", c425_exp, "--challenge-export", c425_exp, "--comparator-json", c425_cfg,
                           "--challenge-sha256", c425_pin, "--comparator-sha256", c425_cfg_pin, "--pins", "437", "--json"],
                          capture_output=True, text=True)
d425_437 = json.loads(p425_437.stdout)
assert p425_437.returncode == 2 and d425_437["verdict"] == "ERROR" and d425_437["reward"] == 0.0, (p425_437.returncode, d425_437)

# Check MCP fv_check_export on (3a) and (3b)
resps_xv = mcp_call(
    ["--allow-root", w],
    [
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
        {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
            "export_file": sol437_exp, "challenge_export": c437_exp, "comparator_json": c437_cfg,
            "challenge_sha256": c437_pin, "comparator_sha256": c437_cfg_pin,
        }}},
        {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "fv_check_export", "arguments": {
            "export_file": c425_exp, "challenge_export": c425_exp, "comparator_json": c425_cfg,
            "challenge_sha256": c425_pin, "comparator_sha256": c425_cfg_pin,
        }}},
    ],
)
assert resps_xv[2]["result"]["structuredContent"]["verdict"] == "REJECTED" and resps_xv[2]["result"]["structuredContent"]["reward"] == 0.0
assert resps_xv[3]["result"]["structuredContent"]["verdict"] == "ERROR" and resps_xv[3]["result"]["structuredContent"]["reward"] == 0.0

# Check fv_lowmem.py on (3a) and (3b)
lm_chal = os.path.join(w, "lm_chal")
os.makedirs(lm_chal)
shutil.copyfile(c437_exp, os.path.join(lm_chal, "challenge.export"))
shutil.copyfile(c437_cfg, os.path.join(lm_chal, "comparator.json"))
plm = subprocess.run(["/usr/bin/python3", "-I", fv_lm, lm_chal, lm_chal, os.path.join(w, "lm_out1"),
                      "--from-export", sol437_exp, "--challenge-sha256", c437_pin,
                      "--comparator-sha256", c437_cfg_pin], capture_output=True, text=True)   # (both pins required)
dlm = json.loads(plm.stdout.strip().splitlines()[-1])
assert plm.returncode == 1 and dlm["verdict"] == "REJECTED" and "not sorried" in dlm["reason"], (plm.returncode, dlm)
print("PASS [3/7] fv check, fastverify-mcp, and fv_lowmem.py enforce check/xversion/xvcheck.py")

# 4. fv-ci.sh rejects mismatched untrusted PR lean-toolchain vs challenge lean-toolchain
ci_proj = os.path.join(w, "ci_proj")
ci_chal = os.path.join(w, "ci_chal")
os.makedirs(ci_proj)
os.makedirs(ci_chal)
open(os.path.join(ci_chal, "lean-toolchain"), "w").write("leanprover/lean4:v4.37.0-rc1\n")
open(os.path.join(ci_proj, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
shutil.copyfile(c437_exp, os.path.join(ci_chal, "challenge.export"))
shutil.copyfile(c437_cfg, os.path.join(ci_chal, "comparator.json"))
pci = subprocess.run([fv_ci, "--project", ci_proj, "--challenge", ci_chal, "--challenge-sha256", c437_pin,
                      "--comparator-sha256", c437_cfg_pin,   # required with the challenge pin
                      "--out-dir", os.path.join(w, "ci_out")], capture_output=True, text=True)
assert pci.returncode == 2 and "lean-toolchain" in pci.stderr, (pci.returncode, pci.stderr)
print("PASS [4/7] fv-ci.sh pins toolchain from challenge/lean-toolchain and rejects PR mismatch")

# 5. CLI parity: bin/fv scrubs dangerous caller env vars (env -i) and supports documented `fv audit --solution-mode`
env_dirty = dict(os.environ, BASH_ENV="/nonexistent/evil.sh", LEAN_PATH="/nonexistent/evil_lean", PYTHONPATH="/nonexistent/evil_py")
pfv = subprocess.run([fv_bin, "doctor", "--json"], env=env_dirty, capture_output=True, text=True)
assert pfv.returncode in (0, 2) and json.loads(pfv.stdout).get("checks") is not None and "evil.sh" not in pfv.stderr, (pfv.returncode, pfv.stderr)
paud = subprocess.run([fv_bin, "audit", op_chal, "--solution-mode", "--json"], env=env_dirty, capture_output=True, text=True)
daud = json.loads(paud.stdout)
assert paud.returncode in (0, 1) and isinstance(daud.get("deep_audit"), dict), (paud.returncode, daud)
print("PASS [5/7] CLI parity: bin/fv scrubs caller env via env -i and supports fv audit --solution-mode")

# 6. exit-code vs JSON-verdict cross-check across fv_schema / fv check / fastverify-mcp
sys.path.insert(0, os.path.join(fv, "schemas"))
import fv_schema
fake_acc = fv_schema.make_envelope("export_in", "ACCEPTED", "sound", "fake", 0.1)
chk_mis = fv_schema.enforce_process_exit(fake_acc, 2, "export_in", 0.1)
assert chk_mis["verdict"] == "ERROR" and chk_mis["accepted"] is False and chk_mis["reward"] == 0.0 and chk_mis["exit_code"] == 2, chk_mis
fake_cond = fv_schema.make_envelope("frontier", "CONDITIONAL", "sound-conditional", "fake", 0.1)
chk_cmis = fv_schema.enforce_process_exit(fake_cond, 0, "frontier", 0.1)
assert chk_cmis["verdict"] == "ERROR" and chk_cmis["accepted"] is False and chk_cmis["exit_code"] == 2, chk_cmis
chk_ok = fv_schema.enforce_process_exit(fake_acc, 0, "export_in", 0.1)
assert chk_ok["verdict"] == "ACCEPTED" and chk_ok["accepted"] is True and chk_ok["exit_code"] == 0, chk_ok

# Also test E2E via a tiny real-copy mirror where check-notary.sh writes verdict="ACCEPTED" then exits 2!
m_fv = os.path.join(w, "mini_fv")
for sub in ("bin", "schemas", "tools/cli", "tools/mcp", "tools/fvserve", "tools/triage", "tools/guard", "check/xversion", "check/sound", "config"):
    s = os.path.join(fv, sub)
    if os.path.exists(s):
        dst = os.path.join(m_fv, sub)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if os.path.isdir(s):
            shutil.copytree(s, dst, symlinks=False)
        else:
            shutil.copy2(s, dst)
os.makedirs(os.path.join(m_fv, "check", "notary"), exist_ok=True)
mock_notary = os.path.join(m_fv, "check", "notary", "check-notary.sh")
with open(mock_notary, "w", encoding="utf-8") as mf:
    mf.write('#!/bin/bash\nwhile [ $# -gt 0 ]; do case "$1" in --json) J="$2"; shift 2;; *) shift;; esac; done\n'
             'echo \'{"checker":"checkNotary","verdict":"ACCEPTED","trust":"notary","reason":"forged"}\' > "$J"\n'
             'exit 2\n')
os.chmod(mock_notary, 0o755)
good_exp = os.path.join(selftest, "good.export")
pmock = subprocess.run([os.path.join(m_fv, "bin", "fv"), "check", good_exp, "-c", op_chal,
                        "--challenge-sha256", op_pin, "--notary", "--json"], capture_output=True, text=True)
dmock = json.loads(pmock.stdout)
assert pmock.returncode == 2 and dmock["verdict"] == "ERROR" and dmock["accepted"] is False and dmock["reward"] == 0.0, (pmock.returncode, dmock)
print("PASS [6/7] fv check & fv_schema fail closed to ERROR (exit 2) when checker exits != 0 with JSON ACCEPTED")

# 7. fvserve startup fails closed on non-S1(3) permitted_axioms AND on missing check/xversion/xvcheck.py
fvs_py = os.path.join(m_fv, "tools", "fvserve", "fvserve.py")
os.makedirs(os.path.join(m_fv, "tools"), exist_ok=True)
shutil.copy2(os.path.join(fv, "tools", "batchverify.py"), os.path.join(m_fv, "tools", "batchverify.py"))
tc_pfx = json.load(open(os.path.join(fv, "config", "components.json"), encoding="utf-8"))["comparator"]["prefix"]
p_bad_ax = subprocess.run(["/usr/bin/python3", "-I", fvs_py, "serve", "--state", os.path.join(w, "fvs_st1"),
                           "--packages", w, "--toolchain", tc_pfx,
                           "--pset", f"bad={caller_chal}:{op_pin}", "--fv", m_fv], capture_output=True, text=True)
assert p_bad_ax.returncode != 0 and "S1(3)" in (p_bad_ax.stderr + p_bad_ax.stdout), (p_bad_ax.returncode, p_bad_ax.stderr)
os.unlink(os.path.join(m_fv, "check", "xversion", "xvcheck.py"))
p_no_xv = subprocess.run(["/usr/bin/python3", "-I", fvs_py, "serve", "--state", os.path.join(w, "fvs_st2"),
                          "--packages", w, "--toolchain", tc_pfx,
                          "--pset", f"ok={op_chal}:{op_pin}", "--fv", m_fv], capture_output=True, text=True)
assert p_no_xv.returncode != 0 and "xvcheck.py" in (p_no_xv.stderr + p_no_xv.stdout), (p_no_xv.returncode, p_no_xv.stderr)
print("PASS [7/7] fvserve startup refuses non-S1(3) permitted_axioms and missing check/xversion/xvcheck.py")
PY
echo "RESULT PASS"

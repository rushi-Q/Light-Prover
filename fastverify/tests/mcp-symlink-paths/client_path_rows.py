#!/usr/bin/env python3
"""tests/mcp-symlink-paths/client_path_rows.py FV W -- client-path policy rows (client-path/*, triage-*/*, c/*):
the uniform client-path policy on every MCP tool and bin/fv / audit.py path:
  client-path/doctor-*, client-path/cli-doctor-*, client-path/verify-project-srcdir, client-path/cli-verify-srcdir: a client lakefile.toml srcDir
    that leaves the private copy (absolute, '..') never reaches lib/autotune.py on the host (no outside module names /
    counts, no hang on an outside FIFO); fv_verify_project / fv verify refuse it before bin/fastverify runs
  client-path/audit-dot-import-*, client-path/vacuity-*, client-path/audit-toolchain-*: `import .abs.path` in a client Challenge.lean
    never names a host path (same answer whether the outside file exists, is a symlink or is missing; no -o outside the
    work dir); a client lean-toolchain '..' (or a symlink) never resolves to ~/.elan
  client-path/mcp-*, client-path/cli-*: no client path is resolved before it is checked: a planted out_dir symlink inside the
    root, an intermediate directory symlink, a symlinked file inside the root, a bounce symlink through a path outside
    --allow-root (same answer at any depth), CLI init-challenge / audit / triage / check / verify outputs: refused or
    replaced, never followed; no outside sha256 is printed
  client-path/triage-*, client-path/mcp-triage-*: triage reads a client source with tools/triage/leanlex.py (the
    Lean-tokenizer mirror from tools/http/fvapi.py): a string "/-" ... "-/" no longer hides the real target, an
    unreadable (syntax-defining) source fails closed (UNCLEAR, no dispatch)
  triage-probes/triage-*: lexer cases (`~r` + a plain string) UNCLEAR and (`section theorem ...`) hard_thm seen;
    triage probes claim REFUTED only on positive evidence (no lean / crash / forged output -> not REFUTED; MCP too)
  triage-evidence/*-triage-*: tagged S1-only evidence (forged axioms line + @[simp] sorry theorem ->
    not REFUTED; a client axiom -> UNCLEAR; a closed true statement -> OK), CLI and MCP
  triage-header/*-triage-*: line-leading `||` / `|>` -> UNCLEAR; the probe header is
    the target's environment; an explicit theorem is found (qualified) or UNCLEAR; namespaced probes; CLI and MCP
  triage-scopes/*-triage-*: included / optParam section variables, `... in` scopes, dotted
    names, `namespace A.B` / `mutual` scopes, `let` in the statement: no false claim; CLI and MCP
  triage-lexer/triage-*: the lexer's `]'` token and `/--` then `--` re-synced verbatim from fvapi.py: triage is not desynced
  c/*: controls (plain paths, lexical '..' on the CLI, an in-tree srcDir, a plain triage source, leanlex == fvapi lexer)
Prints PASS/FAIL rows; writes "P F" to W/count4."""
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
fv, w, here_pkg = sys.argv[1], sys.argv[2], sys.argv[3]
_TX = ["--experimental"] if "--experimental" in subprocess.run([os.path.join(fv, "bin", "fv"), "triage", "--help"], capture_output=True, text=True).stdout else []   # the `fv triage --experimental` opt-in, only when the installed fv has it
ALLOWED, OUTSIDE = os.path.join(w, "allowed4"), os.path.join(w, "outside4")
os.makedirs(ALLOWED)
os.makedirs(OUTSIDE)
P = F = 0


def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    if ok:
        P += 1
    else:
        F += 1


def sha(b):
    return hashlib.sha256(b).hexdigest()


def mcp(tool, args, timeout=300, extra=(), pfx=()):
    reqs = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": tool, "arguments": args}}]
    cmd = [*pfx, "python3", "-I", "-B", os.path.join(fv, "tools", "mcp", "mcp_server.py"), "--allow-root", ALLOWED,
           "--threads", "4", *extra]
    p = subprocess.run(cmd, input="".join(json.dumps(r) + "\n" for r in reqs), capture_output=True, text=True, timeout=timeout)
    for ln in p.stdout.splitlines():
        try:
            o = json.loads(ln)
        except ValueError:
            continue
        if o.get("id") == 2:
            res = o.get("result") or {}
            return res.get("structuredContent") or {}, res.get("isError")
    return {"raw": (p.stdout + p.stderr)[-400:]}, True


def fvcli(args, timeout=300, cwd=None):
    return subprocess.run([os.path.join(fv, "bin", "fv")] + args, capture_output=True, text=True, timeout=timeout, cwd=cwd)


S1 = ["propext", "Quot.sound", "Classical.choice"]

# ======================= (1) lakefile.toml srcDir -> lib/autotune.py on the host =======================
sec = os.path.join(OUTSIDE, "autotune_secret_dir")
os.makedirs(sec)
open(os.path.join(sec, "SecretAlpha.lean"), "w").write("@[to_additive]\ntheorem secret_alpha : True := trivial\n")
open(os.path.join(sec, "SecretBeta.lean"), "w").write("@[to_dual]\ntheorem secret_beta : True := trivial\n")
fifo_d = os.path.join(OUTSIDE, "autotune_fifo_dir")
os.makedirs(fifo_d)
os.mkfifo(os.path.join(fifo_d, "HangOutside.lean"))


def lake_proj(name, srcdir, globs):
    d = os.path.join(ALLOWED, name)
    os.makedirs(d)
    open(os.path.join(d, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
    open(os.path.join(d, "lakefile.toml"), "w").write(
        'name = "p"\ndefaultTargets = ["L"]\n\n[[lean_lib]]\nname = "L"\nsrcDir = "%s"\nglobs = ["%s"]\n' % (srcdir, globs))
    return d


rel_up = "../" * 12 + OUTSIDE.lstrip("/")
for kind, val in (("abs", OUTSIDE), ("rel", rel_up)):
    d = lake_proj("doc_%s" % kind, val, "autotune_secret_dir.*")
    sc, err = mcp("fv_doctor", {"project_dir": d})
    txt = json.dumps(sc)
    row("Secret" not in txt and "autotune_secret_dir" not in txt.replace(val, ""),
        "client-path/doctor-%s-srcdir" % kind, "isError %s, outside module named: %s" % (err, "Secret" in txt))
    p = fvcli(["doctor", "--project", d, "--json"])
    row("Secret" not in p.stdout and "2 module" not in p.stdout, "client-path/cli-doctor-%s-srcdir" % kind,
        "exit %d, outside module named: %s" % (p.returncode, "Secret" in p.stdout))
d = lake_proj("doc_fifo", OUTSIDE, "autotune_fifo_dir.*")
t0 = time.time()
try:
    mcp("fv_doctor", {"project_dir": d}, timeout=8)
    row(time.time() - t0 < 8, "client-path/doctor-fifo-srcdir", "returned in %.1f s (no hang on an outside FIFO)" % (time.time() - t0))
except subprocess.TimeoutExpired:
    row(False, "client-path/doctor-fifo-srcdir", "fv_doctor hung > 8 s on an outside FIFO named by srcDir")
d = lake_proj("doc_plain", "src", "Pl.*")
os.makedirs(os.path.join(d, "src", "Pl"))
open(os.path.join(d, "src", "Pl", "A.lean"), "w").write("theorem a : True := trivial\n")
sc, err = mcp("fv_doctor", {"project_dir": d})
row(not err and isinstance(sc.get("autotune"), dict), "c/doctor-in-tree-srcdir",
    "isError %s, autotune ran: %s" % (err, isinstance(sc.get("autotune"), dict)))

# a pinned challenge (S1 axioms) for fv_verify_project / fv verify
pc = os.path.join(ALLOWED, "pinned_chal")
os.makedirs(pc)
shutil.copyfile(os.path.join(here_pkg, "tests", "frontier-axiom-scope", "data", "sorry", "challenge.export"),
                os.path.join(pc, "challenge.export"))
json.dump({"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["prove_false"],
           "definition_names": [], "permitted_axioms": S1}, open(os.path.join(pc, "comparator.json"), "w"))
csha = sha(open(os.path.join(pc, "challenge.export"), "rb").read())
cfgsha = sha(open(os.path.join(pc, "comparator.json"), "rb").read())
vp_proj = lake_proj("vp_abs", OUTSIDE, "autotune_secret_dir.*")
sc, err = mcp("fv_verify_project", {"project_dir": vp_proj, "challenge_dir": pc, "challenge_sha256": csha,
                                    "comparator_sha256": cfgsha, "timeout": 60}, timeout=400)
txt = json.dumps(sc)
row(bool(err) and "lakefile.toml" in txt and "Secret" not in txt, "client-path/verify-project-srcdir",
    "isError %s, refused before bin/fastverify: %s" % (err, "lakefile.toml" in txt))
p = fvcli(["verify", vp_proj, "--challenge", pc, "--challenge-sha256", csha, "--comparator-sha256", cfgsha, "--json"], timeout=600)
row(p.returncode == 2 and "lakefile.toml" in p.stdout and "Secret" not in p.stdout, "client-path/cli-verify-srcdir",
    "exit %d, refused: %s" % (p.returncode, "lakefile.toml" in p.stdout))

# ======================= (2) import .abs.path / lean-toolchain '..' =======================
dotfree = os.path.join(w, "bwrap_dotfree")
os.makedirs(dotfree)
open(os.path.join(dotfree, "SecretMod.lean"), "w").write("def secret_val : Nat := 42\n")
open(os.path.join(OUTSIDE, "OutsideSecret.lean"), "w").write("theorem outside_secret : True := trivial\n")
os.symlink(os.path.join(OUTSIDE, "OutsideSecret.lean"), os.path.join(dotfree, "SymToOutside.lean"))
bw = ["bwrap", "--unshare-net", "--die-with-parent", "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
      "--tmpfs", "/tmp", "--tmpfs", "/var/tmp", "--bind", dotfree, "/var/tmp/fvaudit_outside", "--bind", w, w]
answers = {}
for lbl, imp in (("existing", "SecretMod"), ("symlink", "SymToOutside"), ("missing", "DoesNotExist")):
    cd = os.path.join(ALLOWED, "dot_imp_" + lbl)
    os.makedirs(cd)
    open(os.path.join(cd, "lean-toolchain"), "w").write("leanprover/lean4:v4.36.0\n")
    open(os.path.join(cd, "Challenge.lean"), "w").write("import .var.tmp.fvaudit_outside.%s\ntheorem goal : True := sorry\n" % imp)
    json.dump({"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["goal"],
               "permitted_axioms": S1}, open(os.path.join(cd, "comparator.json"), "w"))
    sc, err = mcp("fv_audit_challenge", {"challenge_dir": cd, "probe": False, "threads": 2}, pfx=bw)
    e = json.dumps((sc.get("deep_audit") or {}).get("error"))
    answers[lbl] = ("same file" in e or "SameFileError" in e, e.replace(imp, "X")[:200])
same = len({a[1] for a in answers.values()}) == 1
row(not any(a[0] for a in answers.values()) and same, "client-path/audit-dot-import-no-oracle",
    "same answer for existing / symlink / missing outside file: %s (%s)" % (same, answers["existing"][1][:120]))
vpc = os.path.join(w, "vp_dot_chal")
os.makedirs(vpc)
open(os.path.join(vpc, "Challenge.lean"), "w").write("import .var.tmp.fvaudit_outside.SecretMod\ntheorem goal : True := sorry\n")
tc36 = json.load(open(os.path.join(fv, "config", "components.json")))["comparator"]["prefix"]
code = ("import importlib.util, json, sys; "
        "spec = importlib.util.spec_from_file_location('vp', %r); vp = importlib.util.module_from_spec(spec); "
        "spec.loader.exec_module(vp); calls = []; vp.bwrap_cmd = lambda *a, **k: ['echo']; orig = vp.subprocess.run; "
        "vp.subprocess.run = lambda argv, **k: (calls.append(argv), orig(['/bin/true'], capture_output=True, text=True))[1]; "
        "r = vp.run_probes(%r, ['goal'], %r); "
        "print('ARGV', json.dumps([c for c in calls if '-o' in c]))") % (
    os.path.join(fv, "tools", "audit", "vacuity_probe.py"), os.path.join(vpc, "Challenge.lean"), tc36)
p = subprocess.run(bw + ["python3", "-I", "-B", "-c", code], capture_output=True, text=True, timeout=60)
row("/var/tmp/fvaudit_outside/SecretMod.olean" not in p.stdout, "client-path/vacuity-dot-import-no-outside-o",
    "outside -o path in a lean argv: %s" % ("/var/tmp/fvaudit_outside" in p.stdout))
code2 = ("import importlib.util, json, os, sys; "
         "spec = importlib.util.spec_from_file_location('vp', %r); vp = importlib.util.module_from_spec(spec); "
         "spec.loader.exec_module(vp); calls = []; orig = vp.subprocess.run; "
         "vp.subprocess.run = lambda argv, **k: (calls.append(argv), orig(['/bin/true'], capture_output=True, text=True))[1]; "
         "r = vp.run_probes(%r, ['goal'], os.path.expanduser('~/.elan/toolchains/..')); "
         "print('BINDS', json.dumps([c for c in calls]))") % (
    os.path.join(fv, "tools", "audit", "vacuity_probe.py"), os.path.join(vpc, "Challenge.lean"))
p = subprocess.run(bw + ["python3", "-I", "-B", "-c", code2], capture_output=True, text=True, timeout=60)
elan = os.path.realpath(os.path.expanduser("~/.elan"))
row('"%s", "%s"' % (elan, elan) not in p.stdout, "client-path/vacuity-toolchain-elan-not-bound",
    "~/.elan ro-bound into the sandbox: %s" % ('"%s", "%s"' % (elan, elan) in p.stdout))
spec = importlib.util.spec_from_file_location("a4", os.path.join(fv, "tools", "audit", "audit.py"))
sys.path.insert(0, os.path.join(fv, "tools", "audit"))
am = importlib.util.module_from_spec(spec)
spec.loader.exec_module(am)
tdd = os.path.join(w, "tc_dotdot")
os.makedirs(tdd)
open(os.path.join(tdd, "lean-toolchain"), "w").write("..\n")
r = am.resolve_toolchain({}, hint_dir=tdd)
row(r is None or (not r.endswith("..") and os.path.realpath(r) != os.path.realpath(os.path.expanduser("~/.elan"))),
    "client-path/audit-toolchain-dotdot", "resolve_toolchain('..') = %r" % r)
tsl = os.path.join(w, "tc_sym")
os.makedirs(tsl)
open(os.path.join(OUTSIDE, "tc_spec"), "w").write("leanprover/lean4:v4.36.0\n")
os.symlink(os.path.join(OUTSIDE, "tc_spec"), os.path.join(tsl, "lean-toolchain"))
r = am.resolve_toolchain({}, hint_dir=tsl)
row(r is None, "client-path/audit-toolchain-symlink", "resolve_toolchain(symlinked lean-toolchain) = %r" % r)

# ======================= (3) nothing resolved before it is checked =======================
real_sub = os.path.join(ALLOWED, "real_sub")
os.makedirs(real_sub)
open(os.path.join(real_sub, "Plain.lean"), "w").write("theorem plain_ok : True := trivial\n")
os.symlink(real_sub, os.path.join(ALLOWED, "sym_sub"))
os.symlink(os.path.join(real_sub, "Plain.lean"), os.path.join(ALLOWED, "sym_plain.lean"))
sc, err = mcp("fv_triage_sublemma", {"source_file": os.path.join(ALLOWED, "sym_sub", "Plain.lean"), "static_only": True})
row(bool(err), "client-path/mcp-intermediate-dir-symlink", "isError %s" % err)
sc, err = mcp("fv_triage_sublemma", {"source_file": os.path.join(ALLOWED, "sym_plain.lean"), "static_only": True})
row(bool(err), "client-path/mcp-intra-root-file-symlink", "isError %s" % err)
sc, err = mcp("fv_triage_sublemma", {"source_file": os.path.join(real_sub, "Plain.lean"), "static_only": True})
row(not err, "c/mcp-plain-file", "isError %s" % err)
sc, err = mcp("fv_triage_sublemma", {"source_file": os.path.join(ALLOWED, "real_sub", "..", "real_sub", "Plain.lean"),
                                     "static_only": True})
row(bool(err), "client-path/mcp-dotdot-refused", "isError %s (%s)" % (err, str(sc.get("error"))[:80]))
os.makedirs(os.path.join(OUTSIDE, "d_one"))
os.makedirs(os.path.join(OUTSIDE, "d_two", "nested"))
os.symlink("d_one", os.path.join(OUTSIDE, "probe_sym_1"))
os.symlink("d_two/nested", os.path.join(OUTSIDE, "probe_sym_2"))
b = {}
for k in ("1", "2"):
    lk = os.path.join(ALLOWED, "bounce_" + k)
    os.symlink(os.path.join(OUTSIDE, "probe_sym_" + k, "..", "..", os.path.basename(ALLOWED), "real_sub", "Plain.lean"), lk)
    sc, err = mcp("fv_triage_sublemma", {"source_file": lk, "static_only": True})
    b[k] = (bool(err), str(sc.get("error")).replace("bounce_" + k, "bounce_N"))
row(b["1"][0] and b["2"][0] and b["1"][1] == b["2"][1], "client-path/mcp-bounce-symlink-no-depth-oracle",
    "depth1 %s / depth2 %s, same message %s" % (b["1"][0], b["2"][0], b["1"][1] == b["2"][1]))
# init source (tiny 4.33.1 project) used by the init rows
init_src = os.path.join(ALLOWED, "init_src")
os.makedirs(init_src)
open(os.path.join(init_src, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
open(os.path.join(init_src, "lakefile.toml"), "w").write('name = "InitD1"\ndefaultTargets = ["InitD1"]\n[[lean_lib]]\nname = "InitD1"\n')
open(os.path.join(init_src, "lake-manifest.json"), "w").write('{"version":"1.1.0","packagesDir":".lake/packages","packages":[],"lakeDir":".lake"}\n')
open(os.path.join(init_src, "InitD1.lean"), "w").write("theorem t_d1 : True := by sorry\n")
json.dump({"challenge_module": "InitD1", "solution_module": "InitD1", "theorem_names": ["t_d1"], "definition_names": [],
           "permitted_axioms": S1}, open(os.path.join(init_src, "comparator.json"), "w"))
victim_in = os.path.join(ALLOWED, "victim_init_dir")
os.makedirs(victim_in)
open(os.path.join(victim_in, "comparator.json"), "w").write("UNTOUCHED\n")
os.symlink(victim_in, os.path.join(ALLOWED, "sym_init_out"))
sc, err = mcp("fv_init_challenge", {"challenge_dir": init_src, "out_dir": os.path.join(ALLOWED, "sym_init_out"), "threads": 4},
              timeout=900)
row(bool(err) and open(os.path.join(victim_in, "comparator.json")).read() == "UNTOUCHED\n", "client-path/mcp-init-out-dir-symlink",
    "isError %s, victim intact %s" % (err, open(os.path.join(victim_in, "comparator.json")).read() == "UNTOUCHED\n"))
victim_m = os.path.join(ALLOWED, "victim_mint_dir")
os.makedirs(victim_m)
open(os.path.join(victim_m, "mint-manifest.json"), "w").write("UNTOUCHED\n")
os.symlink(victim_m, os.path.join(ALLOWED, "sym_mint_out"))
sc, err = mcp("fv_mint_subchallenges", {"project_dir": init_src, "out_dir": os.path.join(ALLOWED, "sym_mint_out"),
                                        "theorems": ["t_d1"], "threads": 4}, timeout=900)
row(bool(err) and open(os.path.join(victim_m, "mint-manifest.json")).read() == "UNTOUCHED\n" and len(os.listdir(victim_m)) == 1,
    "client-path/mcp-mint-out-dir-symlink", "isError %s, victim intact %s" % (err, len(os.listdir(victim_m)) == 1))
# CLI init-challenge
cv = os.path.join(OUTSIDE, "cli_init_victim")
os.makedirs(cv)
open(os.path.join(cv, "comparator.json"), "w").write("UNTOUCHED\n")
os.symlink(cv, os.path.join(ALLOWED, "cli_sym_out"))
p = fvcli(["init-challenge", init_src, os.path.join(ALLOWED, "cli_sym_out"), "--threads", "4", "--json"], timeout=900)
row(p.returncode != 0 and open(os.path.join(cv, "comparator.json")).read() == "UNTOUCHED\n", "client-path/cli-init-out-symlink",
    "exit %d, outside victim intact %s" % (p.returncode, open(os.path.join(cv, "comparator.json")).read() == "UNTOUCHED\n"))
oc = os.path.join(OUTSIDE, "cli_outside_chal")
shutil.copytree(init_src, oc)
open(os.path.join(oc, "InitD1.lean"), "w").write('def cli_secret : String := "OUTSIDE_CHAL_SECRET_7788"\ntheorem t_d1 : cli_secret = "" := by sorry\n')
os.symlink(oc, os.path.join(ALLOWED, "cli_sym_chal"))
out2 = os.path.join(ALLOWED, "cli_init_out2")
p = fvcli(["init-challenge", os.path.join(ALLOWED, "cli_sym_chal"), out2, "--threads", "4", "--json"], timeout=900)
ex = os.path.join(out2, "challenge.export")
row(p.returncode != 0 and not os.path.exists(ex), "client-path/cli-init-challenge-symlink",
    "exit %d, outside challenge built: %s" % (p.returncode, os.path.exists(ex)))
# CLI audit
clean = os.path.join(ALLOWED, "clean_chal")
shutil.copytree(pc, clean)
osec = os.path.join(OUTSIDE, "audit_secret.bin")
open(osec, "wb").write(b"SECRET_FOR_AUDIT_SHA256_ORACLE_551199\n")
osha = sha(open(osec, "rb").read())
ad = os.path.join(ALLOWED, "aud_sha_leak")
os.makedirs(ad)
shutil.copyfile(os.path.join(pc, "comparator.json"), os.path.join(ad, "comparator.json"))
os.symlink(osec, os.path.join(ad, "challenge.export"))
p = fvcli(["audit", ad, "--json"])
row(osha not in p.stdout + p.stderr and p.returncode != 0, "client-path/cli-audit-export-symlink-no-sha",
    "exit %d, outside sha256 printed: %s" % (p.returncode, osha in p.stdout + p.stderr))
oac = os.path.join(OUTSIDE, "outside_aud_chal")
shutil.copytree(pc, oac)
os.symlink(oac, os.path.join(ALLOWED, "sym_aud_chal"))
p = fvcli(["audit", os.path.join(ALLOWED, "sym_aud_chal"), "--json"])
j = json.loads(p.stdout or "{}") if p.stdout.strip().startswith("{") else {}
row(p.returncode != 0 and not j.get("deep_audit") and csha not in p.stdout, "client-path/cli-audit-challenge-symlink",
    "exit %d, outside challenge audited: %s" % (p.returncode, bool(j.get("deep_audit"))))
iv = os.path.join(OUTSIDE, "aud_interm_victim")
os.makedirs(iv)
json.dump({"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["INTERM_OUTSIDE_CFG_THM"],
           "definition_names": [], "permitted_axioms": S1}, open(os.path.join(iv, "cfg.json"), "w"))
open(os.path.join(iv, "victim_rs.lean"), "w").write("UNTOUCHED_RS\n")
open(os.path.join(iv, "victim_out.json"), "w").write("UNTOUCHED_JSON\n")
os.symlink(iv, os.path.join(ALLOWED, "sym_interm"))
p = fvcli(["audit", clean, "--config", os.path.join(ALLOWED, "sym_interm", "cfg.json"),
           "--reading-set", os.path.join(ALLOWED, "sym_interm", "victim_rs.lean"), "--json"])
intact = open(os.path.join(iv, "victim_rs.lean")).read() == "UNTOUCHED_RS\n"
row("INTERM_OUTSIDE_CFG_THM" not in p.stdout + p.stderr and intact, "client-path/cli-audit-intermediate-dir-symlink",
    "exit %d, outside config read %s, outside reading set intact %s" % (p.returncode, "INTERM_OUTSIDE_CFG_THM" in p.stdout + p.stderr, intact))
p = subprocess.run(["python3", "-I", "-B", os.path.join(fv, "tools", "audit", "audit.py"), clean, "--no-probe",
                    "--json", os.path.join(ALLOWED, "sym_interm", "victim_out.json")], capture_output=True, text=True, timeout=300)
intact = open(os.path.join(iv, "victim_out.json")).read() == "UNTOUCHED_JSON\n"
row(intact, "client-path/audit-py-json-intermediate-dir-symlink", "exit %d, outside json intact %s" % (p.returncode, intact))
p = fvcli(["audit", clean, "--json"])
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
row((j.get("challenge_export") or {}).get("sha256") == csha, "c/cli-audit-plain", "exit %d, sha256 of the real export reported" % p.returncode)
sub = os.path.join(ALLOWED, "cwd_sub")
os.makedirs(sub)
p = fvcli(["audit", "../clean_chal", "--json"], cwd=sub)
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
row((j.get("challenge_export") or {}).get("sha256") == csha, "c/cli-relative-dotdot", "exit %d (lexical '..' from the cwd)" % p.returncode)
# CLI triage / check / verify outputs
os.symlink(os.path.join(OUTSIDE, "OutsideSecret.lean"), os.path.join(ALLOWED, "sym_triage.lean"))
p = fvcli(["triage", *_TX, os.path.join(ALLOWED, "sym_triage.lean"), "--static-only", "--json"], timeout=60)
row("outside_secret" not in p.stdout, "client-path/cli-triage-symlink", "exit %d, outside source read: %s" % (p.returncode, "outside_secret" in p.stdout))
os.symlink(osec, os.path.join(ALLOWED, "sym_chx.export"))
p = fvcli(["check", os.path.join(pc, "challenge.export"), "--challenge-export", os.path.join(ALLOWED, "sym_chx.export"),
           "--comparator-json", os.path.join(pc, "comparator.json"), "--challenge-sha256", csha, "--comparator-sha256", cfgsha, "--json"], timeout=120)
row(osha not in p.stdout + p.stderr, "client-path/cli-check-export-symlink-no-sha",
    "exit %d, outside sha256 printed: %s" % (p.returncode, osha in p.stdout + p.stderr))
vj = os.path.join(OUTSIDE, "victim_jout.json")
open(vj, "w").write("UNTOUCHED_JOUT\n")
os.symlink(vj, os.path.join(ALLOWED, "sym_jout.json"))
empty = os.path.join(ALLOWED, "empty_proj")
os.makedirs(empty)
p = fvcli(["verify", empty, "--challenge", pc, "--challenge-sha256", csha, "--comparator-sha256", cfgsha, "--extra-arg=--unsafe=all",
           "--json-out", os.path.join(ALLOWED, "sym_jout.json")], timeout=60)
row(open(vj).read() == "UNTOUCHED_JOUT\n", "client-path/cli-verify-json-out-symlink",
    "exit %d, outside file intact %s" % (p.returncode, open(vj).read() == "UNTOUCHED_JOUT\n"))
p = fvcli(["verify", empty, "--challenge", pc, "--challenge-sha256", csha, "--comparator-sha256", cfgsha, "--extra-arg=--unsafe=all",
           "--json-out", os.path.join(ALLOWED, "plain_jout.json")], timeout=60)
row(os.path.isfile(os.path.join(ALLOWED, "plain_jout.json")) and not os.path.islink(os.path.join(ALLOWED, "plain_jout.json")),
    "c/cli-verify-json-out-plain", "exit %d, --json-out written" % p.returncode)

# ======================= triage reads sources with the Lean-tokenizer mirror (the fvapi.py lexer) =======
trick = ('theorem decoy : True := trivial\ndef s1 := "/-"\n'
         'theorem real_target (n : Nat) : n - 5 + 5 = n := by sorry\ndef s2 := "-/"\n')
tf = os.path.join(ALLOWED, "trick.lean")
open(tf, "w").write(trick)
p = fvcli(["triage", *_TX, tf, "--static-only", "--json"], timeout=60)
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
nm = (j.get("statement") or {}).get("name")
row(nm == "real_target", "client-path/triage-string-literal-comment",
    "target %r (a string \"/-\" ... \"-/\" must not hide the real last theorem; an earlier lexer picked 'decoy')" % nm)
sc, err = mcp("fv_triage_sublemma", {"source": trick, "static_only": True})
nm = (sc.get("statement") or {}).get("name")
row(nm == "real_target", "client-path/mcp-triage-string-literal-comment", "isError %s, target %r" % (err, nm))
mf = os.path.join(ALLOWED, "macro.lean")
open(mf, "w").write('macro "foo" : term => `(1)\ntheorem t (n : Nat) : n + 0 = n := by sorry\n')
p = fvcli(["triage", *_TX, mf, "--static-only", "--json"], timeout=60)
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
row(j.get("status") == "UNCLEAR" and j.get("dispatch_recommended") is False, "client-path/triage-unclear-source-fails-closed",
    "status %r dispatch %r (syntax-defining source: not read as plain theorems)" % (j.get("status"), j.get("dispatch_recommended")))
# the `]'` token (xs[i]'h) and `/--` followed by `--`
# (doc text in 4.36 / 4.37, a comment in 4.33): neither may hide the real last theorem from triage
r5_inputs = {
    "getelem-proof-token": ('def String.pf (_ : String) : 0 < #[(1:Nat)].size := by decide\n'
                            'theorem easy_thm : True := trivial\n'
                            'def a : Nat := #[(1:Nat)][0]\'"\'".pf\n'
                            'theorem hard_thm (n : Nat) : n - 5 + 5 = n := by sorry\n-- "\n'),
    "doc-comment-line-comment": ('theorem easy_thm : True := trivial\n/-- -- -/\n'
                                 'theorem hard_thm (n : Nat) : n - 5 + 5 = n := (fun _ => sorry) "-/"\n-- "\n'),
}
for lbl, src in r5_inputs.items():
    rf = os.path.join(ALLOWED, "r5_%s.lean" % lbl)
    open(rf, "w").write(src)
    p = fvcli(["triage", *_TX, rf, "--static-only", "--json"], timeout=60)
    j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    nm = (j.get("statement") or {}).get("name")
    row(j.get("status") == "UNCLEAR" and j.get("dispatch_recommended") is False or nm == "hard_thm",
        "triage-lexer/triage-%s" % lbl, "status %r target %r (earlier lexer: 'easy_thm', dispatch)" % (j.get("status"), nm))
# case: Mathlib's `~r` token directly before a plain string (a raw-string opener after
# a symbol) -> UNCLEAR; s1: `section theorem hard_thm ...` (an anonymous section, then a theorem Lean declares) -> hard_thm
# is not hidden from triage
r1 = ('import Mathlib.Data.List.Rotate\nexample : (fun _ : Prop => True) (([] : List Char) ~r"\\" x".toList) := trivial\n'
      'theorem hard_thm : True := trivial\n-- "\ntheorem easy_thm : True := trivial\n')
rf = os.path.join(ALLOWED, "probe_raw_string.lean")
open(rf, "w").write(r1)
p = fvcli(["triage", *_TX, rf, "--static-only", "--json"], timeout=60)
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
row(j.get("status") == "UNCLEAR" and j.get("dispatch_recommended") is False, "triage-probes/triage-raw-string-after-symbol",
    "status %r target %r (earlier lexer: 'easy_thm', dispatch)" % (j.get("status"), (j.get("statement") or {}).get("name")))
s1 = "section theorem hard_thm (n : Nat) : n - 5 + 5 = n := by sorry\ntheorem easy_thm : True := trivial\n"
sf = os.path.join(ALLOWED, "probe_section_thm.lean")
open(sf, "w").write(s1)
p = fvcli(["triage", *_TX, sf, "--static-only", "--theorem", "hard_thm", "--json"], timeout=60)
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
row((j.get("statement") or {}).get("name") == "hard_thm" or j.get("status") == "UNCLEAR", "triage-probes/triage-s1-section-theorem",
    "status %r target %r (Lean declares hard_thm: it must not be hidden)" % (j.get("status"), (j.get("statement") or {}).get("name")))
# a triage probe claims REFUTED / VACUOUS only on positive evidence (completion marker, the theorem's axioms
# line without sorryAx, a confirming run with exit 0, the verified official toolchain); a probe that could not run
# (no lean, a crash, forged output from an unofficial "toolchain") gives UNCLEAR (earlier versions said REFUTED)
fk = os.path.join(w, "fake_tc")
for k, body in (("none", None), ("crash", "#!/bin/sh\nkill -SEGV $$\n"),
                ("forged", "#!/bin/sh\necho \"'_fv_refuted' does not depend on any axioms\"\necho FV_TRIAGE_PROBE_DONE_7f3a\nexit 0\n")):
    os.makedirs(os.path.join(fk, k, "bin"))
    os.makedirs(os.path.join(fk, k, "lib", "lean"))
    if body:
        open(os.path.join(fk, k, "bin", "lean"), "w").write(body)
        os.chmod(os.path.join(fk, k, "bin", "lean"), 0o755)
ews = os.path.join(w, "tri_ws")
os.makedirs(os.path.join(ews, ".lake", "packages"))
good_src = "theorem good_add (n : Nat) : n + 0 = n := by sorry\n"
sys.path.insert(0, os.path.join(fv, "tools", "triage"))
import triage as _tri  # noqa: E402
for k in ("none", "crash", "forged"):
    r = _tri.triage_sublemma(good_src, tc=os.path.join(fk, k), ws=ews, run_lean_probes=True, timeout=60)
    row(r["status"] != "REFUTED" and r["dispatch_recommended"] is False, "triage-probes/triage-probe-%s-not-refuted" % k,
        "status %r (earlier: REFUTED)" % r["status"])
sc, err = mcp("fv_triage_sublemma", {"source": good_src}, extra=("--toolchain", os.path.join(fk, "none"), "--packages", ews))
row(sc.get("status") != "REFUTED" and sc.get("dispatch_recommended") is False, "triage-probes/mcp-triage-unrunnable-toolchain-not-refuted",
    "isError %s, status %r" % (err, sc.get("status")))
tc33 = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
r = _tri.triage_sublemma("theorem bad_natsub (n : Nat) : n - 5 + 5 = n := by sorry\n", tc=tc33, ws=ews, run_lean_probes=True, timeout=60)
row(r["status"] == "REFUTED", "c/triage-probe-real-refuted", "status %r with the official 4.33.1 toolchain" % r["status"])
r = _tri.triage_sublemma(good_src, tc=tc33, ws=ews, run_lean_probes=True, timeout=60)
row(r["status"] == "OK", "c/triage-probe-real-ok", "status %r" % r["status"])
# evidence is tagged and S1-only: a client header that prints a forged axioms line and
# carries an `@[simp] theorem bad ... := sorry`, or a client axiom, never yields REFUTED - on the CLI
# and on MCP fv_triage_sublemma; a closed true statement is OK
rF = ('#print "\'_FVTriage._fv_refuted\' does not depend on any axioms"\n'
      '@[simp] theorem bad : (2:Nat) + 2 = 5 := sorry\n\ntheorem t : (2:Nat) + 2 = 4 := by sorry\n')
rB = "@[simp] axiom fv_ax : (2:Nat) + 2 = 5\n\ntheorem t : (2:Nat) + 2 = 4 := by sorry\n"
rC = "theorem t : (2:Nat) + 2 = 4 := by sorry\n"
for lbl, src, want in (("forged-axioms-line", rF, "not-refuted"), ("client-axiom", rB, "UNCLEAR"), ("closed-true", rC, "OK")):
    fp = os.path.join(ALLOWED, "evidence_%s.lean" % lbl)
    open(fp, "w").write(src)
    p = fvcli(["triage", *_TX, fp, "--toolchain", tc33, "--packages", ews, "--json"], timeout=300)
    j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    st = j.get("status")
    okc = (st not in ("REFUTED", None)) if want == "not-refuted" else st == want
    row(okc, "triage-evidence/cli-triage-%s" % lbl, "status %r (want %s; earlier probe rule: %s)" % (st, want, "OK/UNCLEAR" if want == "OK" else "REFUTED"))
    sc, err = mcp("fv_triage_sublemma", {"source": src}, extra=("--toolchain", tc33, "--packages", ews), timeout=300)
    st = sc.get("status")
    okm = (st not in ("REFUTED", None)) if want == "not-refuted" else st == want
    row(okm, "triage-evidence/mcp-triage-%s" % lbl, "isError %s, status %r (want %s)" % (err, st, want))
# true, axiom-free client sources never come out REFUTED / VACUOUS: a
# statement continued by a line-leading `||` / `|>` is UNCLEAR (not cut); the probe header is the TARGET's environment (a
# closed section's local instance, an inner namespace's shadowing definition, an `omit` all apply); an explicit theorem
# name is found (namespace-qualified) or UNCLEAR, never the last theorem instead; a theorem inside an open namespace is
# probed under its own name (_root_ probe declarations) - CLI and MCP
HEADER_CASES = [
    ("bool-or-continuation", "theorem true_bool_or :\n    (1 + 1 == 3)\n    || (1 + 1 == 2) := by sorry\n", None, ("UNCLEAR",)),
    ("pipe-continuation", "theorem true_nonvacuous_pipe :\n    (0 = 1 → 0 = 1)\n    |> (fun P => ∀ k : Nat, k > 0 → k ≥ 1 ∧ P) := by sorry\n",
     None, ("UNCLEAR",)),
    ("closed-section-local-instance", "section LocalOverride\nlocal instance (priority := high) : OfNat Nat 2 := ⟨3⟩\n"
     "theorem helper_local : (2 : Nat) = 3 := rfl\nend LocalOverride\n\ntheorem target_true : (2 : Nat) + 2 = 4 := by sorry\n",
     "target_true", ("OK", "WARN")),
    ("inner-namespace-shadow-refuted", "@[simp] def GoalProp : Prop := False\ntheorem helper_outer : ¬ GoalProp := id\n\n"
     "namespace Inner\ndef GoalProp : Prop := True\ntheorem target_inner : GoalProp := by sorry\nend Inner\n",
     "target_inner", ("OK", "WARN")),
    ("inner-namespace-shadow-vacuous", "@[simp] def ValidInput (n : Nat) : Prop := False\n"
     "theorem helper_valid (n : Nat) : ¬ ValidInput n := by simp\n\nnamespace Inner\ndef ValidInput (n : Nat) : Prop := n > 0\n"
     "theorem target_nonvacuous (n : Nat) (h : ValidInput n) : n + 1 > 0 := by sorry\nend Inner\n",
     "target_nonvacuous", ("OK", "WARN")),
    ("include-omit", "section S\nvariable (n : Nat) (h1 : n > 5) (h2 : n < 3)\ninclude h1 h2\ntheorem helper_vac : n = 99 := by omega\n"
     "omit h1 h2\ntheorem target_clean (k : Nat) (hk : k > 0) : k ≥ 1 := by sorry\nend S\n", "target_clean", ("OK", "WARN")),
    ("explicit-qualified-name", "theorem helper_top : True := trivial\nnamespace Foo\ntheorem good_thm (n : Nat) : n + 0 = n := by sorry\n"
     "end Foo\ntheorem scratch_false : (2 : Nat) + 2 = 5 := by sorry\n", "Foo.good_thm", ("OK", "WARN")),
    ("explicit-name-not-found", "theorem scratch_false : (2 : Nat) + 2 = 5 := by sorry\n", "Foo.missing", ("UNCLEAR",)),
    ("namespaced-false-refuted", "namespace Foo\ntheorem obviously_false : (2 : Nat) + 2 = 5 := by sorry\nend Foo\n", None,
     ("REFUTED",)),
    ("last-of-several-true", "theorem t1 : (1 : Nat) + 1 = 2 := rfl\ntheorem t2 (n : Nat) : n + 0 = n := by sorry\n", None,
     ("OK", "WARN")),
]
for lbl, src, thm, want in HEADER_CASES:
    fp = os.path.join(ALLOWED, "header_%s.lean" % lbl)
    open(fp, "w").write(src)
    p = fvcli(["triage", *_TX, fp, "--toolchain", tc33, "--packages", ews, "--json"] + (["--theorem", thm] if thm else []), timeout=300)
    j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    row(j.get("status") in want, "triage-header/cli-triage-%s" % lbl, "status %r (want %s)" % (j.get("status"), "/".join(want)))
    sc, err = mcp("fv_triage_sublemma", dict({"source": src}, **({"theorem": thm} if thm else {})),
                  extra=("--toolchain", tc33, "--packages", ews), timeout=300)
    row(sc.get("status") in want, "triage-header/mcp-triage-%s" % lbl, "isError %s, status %r (want %s)" % (err, sc.get("status"), "/".join(want)))
# still no false REFUTED / VACUOUS / ELAB_ERROR:
# an included section hypothesis or an optParam section variable (closedness checks in the probe), a command-scoped
# `... in` before the target (UNCLEAR), a dotted target name (its namespace reopened), `namespace A.B` / `end B` and
# `mutual ... end` scopes, `let ... :=` in the statement (UNCLEAR) - CLI and MCP
SCOPED = ("class Setting where\n  value : Nat\ninstance : Setting := ⟨0⟩\nnamespace Alternative\n"
          "scoped instance (priority := high) : Setting := ⟨1⟩\nend Alternative\n\n")
NOTCLAIM = ("OK", "WARN", "UNCLEAR")
SCOPE_CASES = [
    ("included-section-hyp", "section\nvariable (n : Nat) (h : n < 0)\ninclude h\ntheorem selected : 2 + 2 = 4 := rfl\nend\n", None,
     ("UNCLEAR",)),   # the shown statement is not the declaration Lean elaborates
    ("included-after-theorem", "theorem addZero (n : Nat) : n + 0 = n := rfl\nsection\nvariable (n : Nat) (h : n < 0)\ninclude h\n"
     "theorem selected : 2 + 2 = 4 := rfl\nend\n", "selected", ("UNCLEAR",)),
    ("optparam-section-var", "section S\nvariable (n : Nat := 0)\ntheorem target_opt (h : n > 0) : n ≥ 1 := by sorry\nend S\n", None,
     ("UNCLEAR",)),
    ("scoped-in-refuted", SCOPED + "open scoped Alternative in\ntheorem selected : Setting.value = 1 := rfl\n", None, ("UNCLEAR",)),
    ("scoped-in-vacuous", SCOPED + "open scoped Alternative in\ntheorem selected (h : Setting.value = 1) : Setting.value + 1 = 2 := by rw [h]\n",
     None, ("UNCLEAR",)),
    ("dotted-name-refuted", "@[simp] def GoalProp : Prop := False\nnamespace Foo\ndef GoalProp : Prop := True\nend Foo\n"
     "theorem Foo.target : GoalProp := by sorry\n", None, ("OK", "WARN")),
    ("dotted-name-vacuous", "@[simp] def Valid (n : Nat) : Prop := False\nnamespace Foo\ndef Valid (n : Nat) : Prop := n > 0\nend Foo\n"
     "theorem Foo.target_vac (n : Nat) (_h : Valid n) : n + 1 > 0 := by sorry\n", None, ("OK", "WARN")),
    ("namespace-end-component", "namespace A.B\ntheorem helper : True := trivial\nend B\ntheorem good_thm (n : Nat) : n + 0 = n := by sorry\n"
     "end A\nnamespace C.A\ntheorem good_thm : (2 : Nat) + 2 = 5 := by sorry\nend C.A\n", "A.good_thm", ("OK", "WARN")),
    ("mutual-end", "namespace A\nmutual\ndef f : Nat → Nat\n  | 0 => 0\n  | n+1 => g n\ndef g : Nat → Nat\n  | 0 => 0\n  | n+1 => f n\nend\n"
     "theorem good_thm (n : Nat) : n + 0 = n := by sorry\nend A\nnamespace C.A\ntheorem good_thm : (2 : Nat) + 2 = 5 := by sorry\nend C.A\n",
     "A.good_thm", ("OK", "WARN")),
    ("mutual-qualified-found", "namespace Example\nmutual\n  def sizeA : Nat := 0\n  def sizeB : Nat := 1\nend\n"
     "theorem selected : sizeA + sizeB = 1 := rfl\nend Example\n", "Example.selected", ("OK", "WARN")),
    ("let-in-statement", "theorem selected : let n := 2; n + n = 4 := rfl\n", None, ("UNCLEAR",)),
    ("control-still-vacuous", "theorem vac (n : Nat) (h1 : n > 5) (h2 : n < 3) : n = 99 := by sorry\n", None, ("VACUOUS",)),
    # universe parameters are not carried into the probe: UNCLEAR (earlier: a false ELAB_ERROR)
    ("universe-params", "universe u\ntheorem universeId.{v} (α : Sort v) (a : α) : id a = a := rfl\n", None, ("UNCLEAR",)),
    ("definition-only", "def f : Nat := 1\n", None, ("UNCLEAR",)),
    # a satisfiable hypothesis mentioning False is no "vacuity" finding
    ("false-or-true-hypothesis", "theorem t (h : False ∨ True) (n : Nat) : n + 0 = n := by sorry\n", None, ("OK", "WARN")),
]
for lbl, src, thm, want in SCOPE_CASES:
    fp = os.path.join(ALLOWED, "scopes_%s.lean" % lbl)
    open(fp, "w").write(src)
    p = fvcli(["triage", *_TX, fp, "--toolchain", tc33, "--packages", ews, "--json"] + (["--theorem", thm] if thm else []), timeout=300)
    j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
    row(j.get("status") in want, "triage-scopes/cli-triage-%s" % lbl, "status %r (want %s)" % (j.get("status"), "/".join(want)))
    sc, err = mcp("fv_triage_sublemma", dict({"source": src}, **({"theorem": thm} if thm else {})),
                  extra=("--toolchain", tc33, "--packages", ews), timeout=300)
    row(sc.get("status") in want, "triage-scopes/mcp-triage-%s" % lbl, "isError %s, status %r (want %s)" % (err, sc.get("status"), "/".join(want)))
# the standalone tools/triage/triage.py maps UNCLEAR to exit 2, as bin/fv triage does
fu = os.path.join(ALLOWED, "final2_unclear.lean")
open(fu, "w").write("theorem t (n : Nat) : n + 0 = n := by sorry\n")
p = subprocess.run(["/usr/bin/python3", "-I", os.path.join(fv, "tools", "triage", "triage.py"), fu, "--theorem", "missingName",
                    "--static-only"], capture_output=True, text=True, timeout=120, cwd=ALLOWED)
try:
    jst = json.loads(p.stdout).get("status")
except ValueError:
    jst = None
row(p.returncode == 2 and jst == "UNCLEAR", "packagesdir/standalone-triage-unclear-exit-2", "exit %d status %r" % (p.returncode, jst))
p = subprocess.run(["/usr/bin/python3", "-I", os.path.join(fv, "tools", "triage", "triage.py"), os.path.join(ALLOWED, "no-such.lean"),
                    "--static-only"], capture_output=True, text=True, timeout=120, cwd=ALLOWED)
row(p.returncode == 2 and "Traceback" not in p.stderr, "deep-tree/standalone-triage-unreadable-exit-2", "exit %d" % p.returncode)
gf = os.path.join(ALLOWED, "good.lean")
open(gf, "w").write("theorem good_add (n : Nat) : n + 0 = n := by sorry\n")
p = fvcli(["triage", *_TX, gf, "--static-only", "--json"], timeout=60)
j = json.loads(p.stdout) if p.stdout.strip().startswith("{") else {}
row(j.get("status") == "OK" and (j.get("statement") or {}).get("name") == "good_add", "c/triage-plain-source",
    "status %r" % j.get("status"))
# the lexer copy must stay identical to fvapi.py's (when fvapi.py carries it)
fa = os.path.join(fv, "tools", "http", "fvapi.py")
ll = os.path.join(fv, "tools", "triage", "leanlex.py")
ftxt = open(fa, encoding="utf-8").read() if os.path.isfile(fa) else ""
if "class _LeanLexer" in ftxt and os.path.isfile(ll):
    # leanlex.py loads the INSTALLED fvapi.py's lexer section at import (LEXER_ORIGIN), so triage
    # reads sources exactly as the installed fvapi does whatever lexer version is installed; the bundled copy is the fallback
    a0 = ftxt.index("# Lean source lexer:"); a1 = ftxt.index("def strict_json_loads")
    ltxt = open(ll, encoding="utf-8").read()
    b0 = ltxt.index("# Lean source lexer:")
    b1 = ltxt.index("# ---- end of the lexer copy") if "# ---- end of the lexer copy" in ltxt else len(ltxt)
    same = ftxt[a0:a1].rstrip() == ltxt[b0:b1].rstrip()
    spec = importlib.util.spec_from_file_location("leanlex_under_test", ll)
    llm = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(llm)
    active = getattr(llm, "LEXER_ORIGIN", "") == os.path.join(fv, "tools", "http", "fvapi.py") or \
        os.path.realpath(getattr(llm, "LEXER_ORIGIN", "") or "/nonexistent") == os.path.realpath(fa)
    row(same or active, "c/leanlex-identical-to-fvapi",
        "bundled copy identical: %s; the installed fvapi.py lexer is the active one: %s" % (same, active))
else:
    row(True, "c/leanlex-identical-to-fvapi", "SKIP (fvapi.py has no Lean lexer yet)")
open(os.path.join(w, "count4"), "w").write("%d %d\n" % (P, F))

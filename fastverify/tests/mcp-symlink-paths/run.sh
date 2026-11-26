#!/bin/bash
# tests/mcp-symlink-paths/run.sh [WORKDIR] -- regression test: the MCP server and bin/fv never follow a client symlink (HIGH,
# tools/mcp/mcp_server.py): _resolve_pinned_challenge copied a source-only challenge_dir with shutil.copytree(symlinks=False),
# dereferencing symlinks out of --allow-root (and into paths bwrap hides) on the host: a challenge whose Challenge.lean
# does `include_str "secret_link.txt"` gave an ACCEPTED / ERROR oracle on an outside file. Reproduction
# inputs: data/ (SHA256SUMS).
# Rows:
#   unit/*: the no-follow helpers (open_nofollow_under, scan_client_tree, copy_client_tree, copy_client_file): absolute /
#     relative / directory symlinks, a symlinked path component, FIFO, hard link, outside-root paths -> refused; a plain
#     tree is copied (regular files only, .lake/.git skipped)
#   e2e/verify-project-*: fv_verify_project with the evidence challenge (absolute and relative symlink to a file outside
#     --allow-root): refused before any copy/build, the SAME answer whatever the outside file says (no oracle)
#   e2e/audit-*, e2e/init-*: fv_audit_challenge / fv_init_challenge on a challenge_dir with a symlinked comparator.json /
#     source -> refused (nothing read through the link)
#   e2e/control-regular-file: the same challenge with secret_link.txt a REGULAR file inside the root -> ACCEPTED (the
#     no-follow copy builds the challenge as before)
#   e2e/mint-*, e2e/init-out-dir-*, e2e/frontier-pinned-*, e2e/triage-*, e2e/source-only-hard-link, e2e/audit-tool-*:
#     no client path is followed on mint / init out_dir / pinned frontier / triage / audit;
#     e2e/pinned-layout-internal-symlink-not-refused: a pinned challenge is read as exactly three files
#   mcp/*: .lake symlinks, client packages_dir, fv_doctor links/FIFO, client dupfind index
#     symlink, single-file hard links, comparator challenge_module = absolute path outside the root (audit MCP + CLI)
#   client-path/*, c/* (client_path_rows.py): lakefile srcDir escape into lib/autotune.py, `import .abs.path`
#     and lean-toolchain '..' in the audit, nothing resolved before it is checked (MCP check_path, CLI init-challenge /
#     audit / triage / check / verify outputs, audit.py --json); controls
#   hardlink/* (hardlink_race_rows.py): the hard-link race after open() (name re-checked against the parent fd), MCP mint module
#   cli-path/* (cli_path_rows.py): fv verify --modulo-frontier / --extra-arg paths / --build-cache, bcache, --pins, fv watch
#     --fvwork-state, explicit --toolchain, FV_CLI_ROOTS
#   git-file/* (git_file_rows.py + data_git_files/): a `.git` FILE (worktree / submodule) skipped, never followed; fv verify uses
#     the challenge's own .lake/packages; `bin/fv ci` under the local path policy
#   cache-tree/* (cache_tree_rows.py): no link anywhere in --cache-dir / --incr-base, packages entries / .git / .lake/build
#     not links, --frontier-pinned DIR, CI reports delivered as a unit before the result is printed, triage exit 2
#   packagesdir/* (packages_dir_rows.py): the manifest's packagesDir checked, no .git indirection, deep trees exit 2, triage
#     of a source without a theorem UNCLEAR
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy (the test data stays here).
set -u
export FV_EXPERIMENTAL=1   # the MCP tool fv_triage_sublemma is EXPERIMENTAL in v0.1: the explicit opt-in for its rows
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/mcp-symlink-paths.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
(cd "$HERE/data" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
mkdir -p "$W/allowed" "$W/outside"
cp -a "$HERE/data/chal" "$W/allowed/chal"; cp -a "$HERE/data/proj" "$W/allowed/proj"; chmod -R u+w "$W/allowed"
python3 -I -B - "$FV" "$W" <<'PY'
import hashlib, json, os, shutil, subprocess, sys
sys.dont_write_bytecode = True
fv, w = sys.argv[1], sys.argv[2]
allowed, outside = os.path.join(w, "allowed"), os.path.join(w, "outside")
chal, proj = os.path.join(allowed, "chal"), os.path.join(allowed, "proj")
secret = os.path.join(outside, "secret.txt")
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    if ok:
        P += 1
    else:
        F += 1

# ---------------- unit: the no-follow helpers ----------------
sys.path.insert(0, os.path.join(fv, "tools", "mcp"))
try:
    import mcp_server as m
    have = all(hasattr(m, n) for n in ("open_nofollow_under", "scan_client_tree", "copy_client_tree", "copy_client_file"))
except Exception as e:  # noqa: BLE001
    m, have = None, False
if not have:
    row(False, "unit/helpers", "mcp_server has no no-follow copy helpers (open_nofollow_under / scan_client_tree / copy_client_tree)")
else:
    u = os.path.join(w, "unit"); r = os.path.join(u, "root"); os.makedirs(os.path.join(r, "t", "sub"))
    os.makedirs(os.path.join(r, "t", ".lake")); open(os.path.join(r, "t", "a.lean"), "w").write("a")
    open(os.path.join(r, "t", "sub", "b.lean"), "w").write("b")
    os.symlink(secret, os.path.join(r, "t", ".lake", "skipped"))   # inside an ignored dir: not copied, not refused
    open(secret, "w").write("SECRET_MARKER\n")
    def refused(label, setup, fn):
        try:
            setup()
            fn()
            row(False, "unit/" + label, "not refused")
        except m.ClientPathError as e:
            row(True, "unit/" + label, "refused: %s" % str(e)[:90])
    def tree_op(op):
        def go():
            fd = m.open_nofollow_under(os.path.join(r, "t"), [r], True)
            try:
                op(fd)
            finally:
                os.close(fd)
        return go
    try:
        tree_op(lambda fd: m.copy_client_tree(fd, os.path.join(u, "c0")))()
        got = sorted(os.path.relpath(os.path.join(d, f), os.path.join(u, "c0")) for d, _, fs in os.walk(os.path.join(u, "c0")) for f in fs)
        row(got == ["a.lean", "sub/b.lean"], "unit/plain-tree-copied", "copied %s" % got)
    except Exception as e:  # noqa: BLE001
        row(False, "unit/plain-tree-copied", repr(e))
    L = os.path.join(r, "t", "link.txt")
    refused("absolute-symlink", lambda: os.symlink(secret, L), tree_op(m.scan_client_tree)); os.unlink(L)
    refused("relative-symlink", lambda: os.symlink("../../../outside/secret.txt", L), tree_op(lambda fd: m.copy_client_tree(fd, os.path.join(u, "c1")))); os.unlink(L)
    refused("dir-symlink", lambda: os.symlink("sub", L), tree_op(m.scan_client_tree)); os.unlink(L)
    refused("fifo", lambda: os.mkfifo(L), tree_op(lambda fd: m.copy_client_tree(fd, os.path.join(u, "c2")))); os.unlink(L)
    refused("hard-link", lambda: os.link(secret, L), tree_op(lambda fd: m.copy_client_tree(fd, os.path.join(u, "c3")))); os.unlink(L)
    refused("symlinked-component", lambda: os.symlink(os.path.join(r, "t"), os.path.join(r, "t2")),
            lambda: m.open_nofollow_under(os.path.join(r, "t2", "a.lean"), [r], False))
    refused("final-symlink-file", lambda: os.symlink(secret, L), lambda: m.copy_client_file(L, os.path.join(u, "x"), [r])); os.unlink(L)
    refused("outside-root", lambda: None, lambda: m.open_nofollow_under(secret, [r], False))

# ---------------- e2e through the MCP server ----------------
def mcp(reqs, timeout=900):
    p = subprocess.run(["python3", "-I", "-B", os.path.join(fv, "tools", "mcp", "mcp_server.py"), "--allow-root", allowed,
                        "--threads", "4"], input="".join(json.dumps(x) + "\n" for x in reqs), capture_output=True,
                       text=True, timeout=timeout)
    out = {}
    for ln in p.stdout.splitlines():
        try:
            o = json.loads(ln)
        except ValueError:
            continue
        if "id" in o:
            out[o["id"]] = o
    return out
INIT = {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}}
def call(name, args, timeout=900):
    r = mcp([INIT, {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": name, "arguments": args}}], timeout)
    res = (r.get(2) or {}).get("result") or {}
    return res.get("structuredContent") or {}, res.get("isError")
cfg_sha = hashlib.sha256(open(os.path.join(chal, "comparator.json"), "rb").read()).hexdigest()
link = os.path.join(chal, "secret_link.txt")
VP = lambda: {"project_dir": proj, "challenge_dir": chal, "comparator_sha256": cfg_sha, "preset": "sound", "build_option": "B0",
              "timeout": 300}
for kind, target in (("absolute", secret), ("relative", "../../outside/secret.txt")):
    if os.path.lexists(link):
        os.unlink(link)
    os.symlink(target, link)
    seen = []
    for val in ("SECRET_MARKER_Z03_7711", "WRONG_SECRET_0000"):
        open(secret, "w").write(val + "\n")
        sc, _ = call("fv_verify_project", VP())
        seen.append((sc.get("verdict"), sc.get("accepted"), str(sc.get("reason") or sc.get("error") or "")))
    same = len(set((v, a) for v, a, _ in seen)) == 1
    refusal = all(v != "ACCEPTED" and a is not True and "symlink" in why for v, a, why in seen)
    row(same and refusal, "e2e/verify-project-%s-symlink" % kind,
        "answers %s" % [(v, a, why[:80]) for v, a, why in seen])
# audit / init with a symlinked comparator.json (a regular-file challenge otherwise)
os.unlink(link)
open(link, "w").write("SECRET_MARKER_Z03_7711\n")
bad = os.path.join(allowed, "chal_badcfg"); shutil.copytree(chal, bad)
os.unlink(os.path.join(bad, "comparator.json"))
open(os.path.join(outside, "c.json"), "w").write(json.dumps({"theorem_names": ["LEAKED_THEOREM_NAME"], "definition_names": [],
                                                             "permitted_axioms": ["propext"]}))
os.symlink(os.path.join(outside, "c.json"), os.path.join(bad, "comparator.json"))
sc, err = call("fv_audit_challenge", {"challenge_dir": bad})
txt = json.dumps(sc)
row(err is True and "LEAKED_THEOREM_NAME" not in txt and "symlink" in txt, "e2e/audit-symlinked-comparator",
    "isError %s, leaked %s: %s" % (err, "LEAKED_THEOREM_NAME" in txt, str(sc.get("error"))[:100]))
sc, err = call("fv_init_challenge", {"challenge_dir": bad, "out_dir": os.path.join(allowed, "init_out")}, timeout=600)
leaked = os.path.isfile(os.path.join(allowed, "init_out", "comparator.json")) and \
    "LEAKED_THEOREM_NAME" in open(os.path.join(allowed, "init_out", "comparator.json")).read()
row(err is True and not leaked and "symlink" in json.dumps(sc), "e2e/init-symlinked-comparator",
    "isError %s, leaked %s: %s" % (err, leaked, str(sc.get("error"))[:100]))
# positive control: the same source-only challenge with a REGULAR secret_link.txt inside the root is still built + accepted
sc, _ = call("fv_verify_project", VP())
row(sc.get("verdict") == "ACCEPTED" and sc.get("accepted") is True, "e2e/control-regular-file",
    "verdict %s accepted %s %s" % (sc.get("verdict"), sc.get("accepted"), str(sc.get("reason"))[:100]))
# ---------------- every other client-path copy / read / write ----------------
open(secret, "w").write("TOP_SECRET_FIXB_R2_4242\n")
def leaked_under(d):
    for r_, _, fs in os.walk(d):
        for f_ in fs:
            try:
                if b"TOP_SECRET_FIXB_R2_4242" in open(os.path.join(r_, f_), "rb").read():
                    return True
            except OSError:
                pass
    return False
# (1) fv_mint_subchallenges: project with a symlink (include_str exfiltration) -> refused, nothing leaked into out_dir
mp = os.path.join(allowed, "mint_proj"); shutil.copytree(proj, mp)
open(os.path.join(mp, "Solution.lean"), "w").write('def leaked : String := include_str "secret_link.txt"\n'
                                                    'theorem leak_thm : leaked = "" := by sorry\n')
os.symlink(secret, os.path.join(mp, "secret_link.txt"))
mo = os.path.join(allowed, "mint_out")
sc, err = call("fv_mint_subchallenges", {"project_dir": mp, "out_dir": mo, "theorems": ["leak_thm"], "timeout": 300}, timeout=600)
row(err is True and "symlink" in json.dumps(sc) and not (os.path.isdir(mo) and leaked_under(mo)), "e2e/mint-project-symlink",
    "isError %s, leaked %s: %s" % (err, os.path.isdir(mo) and leaked_under(mo), str(sc.get("error"))[:100]))
# (2) bin/fv mint (local CLI) on the same project -> refused
p2 = subprocess.run([os.path.join(fv, "bin", "fv"), "mint", mp, "--out", os.path.join(w, "cli_mint_out"), "--json",
                     "--theorem", "leak_thm"], capture_output=True, text=True, timeout=600)
row(p2.returncode != 0 and "symlink" in (p2.stdout + p2.stderr) and not leaked_under(os.path.join(w, "cli_mint_out"))
    if os.path.isdir(os.path.join(w, "cli_mint_out")) else (p2.returncode != 0 and "symlink" in (p2.stdout + p2.stderr)),
    "e2e/cli-mint-project-symlink", "exit %d: %s" % (p2.returncode, (p2.stdout + p2.stderr).strip()[-120:]))
# (3) fv_init_challenge: a symlink planted in out_dir must be replaced, never written through (victim outside untouched)
victim = os.path.join(outside, "victim.txt"); open(victim, "w").write("VICTIM_ORIGINAL\n")
okchal = os.path.join(allowed, "chal_regular"); shutil.copytree(chal, okchal)
if os.path.lexists(os.path.join(okchal, "secret_link.txt")):
    os.unlink(os.path.join(okchal, "secret_link.txt"))
open(os.path.join(okchal, "secret_link.txt"), "w").write("SECRET_MARKER_Z03_7711\n")
io = os.path.join(allowed, "init_out2"); os.makedirs(io)
os.symlink(victim, os.path.join(io, "challenge.export.sha256"))
sc, err = call("fv_init_challenge", {"challenge_dir": okchal, "out_dir": io}, timeout=600)
row(open(victim).read() == "VICTIM_ORIGINAL\n" and not os.path.islink(os.path.join(io, "challenge.export.sha256")) and err is False,
    "e2e/init-out-dir-planted-symlink", "victim intact %s, entry replaced %s, ok %s %s" % (
        open(victim).read() == "VICTIM_ORIGINAL\n", not os.path.islink(os.path.join(io, "challenge.export.sha256")), sc.get("ok"),
        str(sc.get("error") or "")[:80]))
# (4) fv_check_export frontier_pinned_dir with a symlinked frontier.json -> refused before any judge reads it
pd = os.path.join(allowed, "fpin"); os.makedirs(pd); os.symlink(secret, os.path.join(pd, "frontier.json"))
ex4 = os.path.join(allowed, "x4"); os.makedirs(ex4)
open(os.path.join(ex4, "sol.export"), "w").write('{"meta":{}}\n')
shutil.copyfile(os.path.join(chal, "comparator.json"), os.path.join(ex4, "comparator.json"))
open(os.path.join(ex4, "challenge.export"), "w").write('{"meta":{}}\n')
sha = lambda q: hashlib.sha256(open(q, "rb").read()).hexdigest()
sc, err = call("fv_check_export", {"export_file": os.path.join(ex4, "sol.export"), "challenge_export": os.path.join(ex4, "challenge.export"),
                                   "comparator_json": os.path.join(ex4, "comparator.json"), "challenge_sha256": sha(os.path.join(ex4, "challenge.export")),
                                   "comparator_sha256": sha(os.path.join(ex4, "comparator.json")), "frontier": True,
                                   "frontier_pinned_dir": pd}, timeout=300)
txt = json.dumps(sc)
row("symlink" in txt and "JSONDecodeError" not in txt and sc.get("accepted") is not True, "e2e/frontier-pinned-dir-symlink",
    "verdict %s: %s" % (sc.get("verdict"), str(sc.get("reason") or sc.get("error"))[:110]))
# (5) fv_triage_sublemma repo_dir with a symlinked .lean -> refused
rd = os.path.join(allowed, "repo"); os.makedirs(rd)
open(os.path.join(outside, "Hidden.lean"), "w").write("theorem hidden_secret_thm : 1 + 1 = 2 := rfl\n")
os.symlink(os.path.join(outside, "Hidden.lean"), os.path.join(rd, "Hidden.lean"))
sc, err = call("fv_triage_sublemma", {"source": "theorem q : 1 + 1 = 2 := by sorry\n", "repo_dir": rd, "static_only": True}, timeout=120)
row(err is True and "hidden_secret_thm" not in json.dumps(sc), "e2e/triage-repo-symlink", "isError %s: %s" % (err, str(sc.get("error"))[:100]))
# (6) a source-only challenge with a HARD link to an outside file -> refused (its content would be copied and built)
hc = os.path.join(allowed, "chal_hard"); shutil.copytree(okchal, hc); os.unlink(os.path.join(hc, "secret_link.txt"))
try:
    os.link(secret, os.path.join(hc, "secret_link.txt")); hard = True
except OSError:
    hard = False
if hard:
    sc, _ = call("fv_verify_project", {"project_dir": proj, "challenge_dir": hc, "comparator_sha256": cfg_sha, "preset": "sound",
                                       "build_option": "B0", "timeout": 300})
    row(sc.get("accepted") is not True and "hard-linked" in str(sc.get("reason") or sc.get("error")), "e2e/source-only-hard-link",
        "verdict %s: %s" % (sc.get("verdict"), str(sc.get("reason"))[:100]))
else:
    print("SKIP e2e/source-only-hard-link: cannot hard-link across filesystems here")
# (7) a PINNED challenge (challenge.export present) is read as three files: an unrelated internal symlink is not refused
pc = os.path.join(allowed, "chal_pinned"); os.makedirs(pc)
shutil.copyfile(os.path.join(ex4, "challenge.export"), os.path.join(pc, "challenge.export"))
shutil.copyfile(os.path.join(chal, "comparator.json"), os.path.join(pc, "comparator.json"))
os.symlink("comparator.json", os.path.join(pc, "notes-link.txt"))
sc, _ = call("fv_verify_project", {"project_dir": proj, "challenge_dir": pc, "comparator_sha256": "0" * 64,
                                   "challenge_sha256": sha(os.path.join(pc, "challenge.export")), "preset": "sound", "timeout": 60})
why = str(sc.get("reason") or sc.get("error"))
row("comparator_json sha256 mismatch" in why and "symlink" not in why, "e2e/pinned-layout-internal-symlink-not-refused",
    why[:110])
# (8) the audit tool itself (bin/fv audit / tools/audit/audit.py) refuses a target dir with a symlink
p8 = subprocess.run(["python3", "-I", "-B", os.path.join(fv, "tools", "audit", "audit.py"), mp, "--no-probe"],
                    capture_output=True, text=True, timeout=120)
row(p8.returncode == 2 and "symlink" in p8.stderr and "SECRET" not in p8.stdout, "e2e/audit-tool-target-symlink",
    "exit %d: %s" % (p8.returncode, p8.stderr.strip()[-110:]))
# ---------------- mcp/*: ONE policy for every client path ----------------
open(secret, "w").write("TOP_SECRET_FIXB_R3_7788\nSECOND_LINE\n")
def leaked3(x):
    return "TOP_SECRET_FIXB_R3_7788" in json.dumps(x)
# (1) a symlink named .lake (or .lake/packages pointing outside) in a copied client tree: refused, not skipped
lk = os.path.join(allowed, "mint_lake"); shutil.copytree(proj, lk)
os.symlink(outside, os.path.join(lk, ".lake"))
sc, err = call("fv_mint_subchallenges", {"project_dir": lk, "out_dir": os.path.join(allowed, "mint_lake_out"), "timeout": 300}, timeout=600)
row(err is True and ".lake" in json.dumps(sc), "mcp/mint-dot-lake-symlink", "isError %s: %s" % (err, str(sc.get("error"))[:100]))
lk2 = os.path.join(allowed, "mint_lake2"); shutil.copytree(proj, lk2); os.makedirs(os.path.join(lk2, ".lake"))
os.symlink(outside, os.path.join(lk2, ".lake", "packages"))
sc, err = call("fv_mint_subchallenges", {"project_dir": lk2, "out_dir": os.path.join(allowed, "mint_lake2_out"), "timeout": 300}, timeout=600)
row(not (err is False and sc.get("ok")) or not leaked_under(os.path.join(allowed, "mint_lake2_out")), "mcp/mint-dot-lake-packages-not-used",
    "isError %s ok %s leaked %s" % (err, sc.get("ok"), leaked_under(os.path.join(allowed, "mint_lake2_out")) if os.path.isdir(os.path.join(allowed, "mint_lake2_out")) else False))
# (2) a client packages_dir (not the configured workspace) is refused on every tool
pk = os.path.join(allowed, "evil_ws"); os.makedirs(pk)
for tool, args in (("fv_mint_subchallenges", {"project_dir": mp, "out_dir": os.path.join(allowed, "o_pk1")}),
                   ("fv_init_challenge", {"challenge_dir": okchal, "out_dir": os.path.join(allowed, "o_pk2")}),
                   ("fv_audit_challenge", {"challenge_dir": okchal}),
                   ("fv_verify_project", {"project_dir": proj, "challenge_dir": okchal, "comparator_sha256": cfg_sha, "preset": "sound"})):
    a2 = dict(args); a2["packages_dir"] = pk
    sc, err = call(tool, a2, timeout=300)
    row("(fastverify-mcp --packages)" in json.dumps(sc), "mcp/%s-client-packages-refused" % tool, str(sc.get("error") or sc.get("reason"))[:100])
# (3) fv_doctor: symlinked lean-toolchain / source and a FIFO: refused, no leak, no hang
dp = os.path.join(allowed, "doc_proj"); shutil.copytree(proj, dp); os.unlink(os.path.join(dp, "lean-toolchain"))
os.symlink(secret, os.path.join(dp, "lean-toolchain"))
sc, err = call("fv_doctor", {"project_dir": dp}, timeout=120)
row(not leaked3(sc) and err is True, "mcp/doctor-symlinked-toolchain", "isError %s leaked %s: %s" % (err, leaked3(sc), str(sc.get("error"))[:90]))
df = os.path.join(allowed, "doc_fifo"); shutil.copytree(proj, df); os.mkfifo(os.path.join(df, "Hang.lean"))
import time as _t
t0 = _t.time()
try:
    sc, err = call("fv_doctor", {"project_dir": df}, timeout=60)
    row(err is True and _t.time() - t0 < 50, "mcp/doctor-fifo-no-hang", "isError %s in %.1fs: %s" % (err, _t.time() - t0, str(sc.get("error"))[:80]))
except subprocess.TimeoutExpired:
    row(False, "mcp/doctor-fifo-no-hang", "MCP server hung")
# (4) fv_lookup_duplicate with a client index whose index.sqlite is a symlink: refused (no oracle)
ix = os.path.join(allowed, "idx"); os.makedirs(ix); os.symlink(secret, os.path.join(ix, "index.sqlite"))
sc, err = call("fv_lookup_duplicate", {"indexes": [ix], "name": "x"}, timeout=120)
row(err is True and "DatabaseError" not in json.dumps(sc) and "refused" in json.dumps(sc), "mcp/lookup-client-index-symlink",
    str(sc.get("error"))[:100])
# (5) single-file hard links (source_file, targets_file) refused
hs = os.path.join(allowed, "hl_src.lean")
open(os.path.join(outside, "hl_target.lean"), "w").write("theorem outside_hl_thm_4455 : 1 = 1 := rfl\n")
try:
    os.link(os.path.join(outside, "hl_target.lean"), hs); hl = True
except OSError:
    hl = False
if hl:
    sc, err = call("fv_triage_sublemma", {"source_file": hs, "static_only": True}, timeout=120)
    row(err is True and "outside_hl_thm_4455" not in json.dumps(sc), "mcp/triage-hard-linked-source", str(sc.get("error"))[:90])
# (6) comparator.json challenge_module naming an ABSOLUTE path outside the root (zero symlinks)
od = os.path.join(os.path.dirname(w), "absmodout" + str(os.getpid())); os.makedirs(od, exist_ok=True)   # dot-free path
open(os.path.join(od, "MarkerMod.lean"), "w").write("theorem marker_thm_outside : True := trivial\n-- OUTSIDE_SOURCE_MARKER\n")
ce = os.path.join(allowed, "chal_absmod"); os.makedirs(ce)
open(os.path.join(ce, "challenge.export"), "w").write(   # the evidence's minimal valid export (minimal repro)
    '{"meta":{"format":{"version":"3.1.0"},"exporter":{"name":"lean4export","version":"3.1.0"},"lean":{"version":"4.33.1",'
    '"githash":"0000000000000000000000000000000000000000"}}}\n{"in":1,"str":{"pre":0,"str":"True"}}\n'
    '{"in":2,"str":{"pre":0,"str":"marker_thm_outside"}}\n{"ie":0,"sort":0}\n{"ie":1,"const":{"name":1,"us":[]}}\n'
    '{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}\n{"axiom":{"name":2,"levelParams":[],"type":1,"isUnsafe":false}}\n')
json.dump({"challenge_module": os.path.join(od, "MarkerMod"), "solution_module": "Solution", "theorem_names": ["marker_thm_outside"],
           "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, open(os.path.join(ce, "comparator.json"), "w"))
for probe in (False, True):
    sc, err = call("fv_audit_challenge", {"challenge_dir": ce, "probe": probe}, timeout=300)
    txt = json.dumps(sc)
    row("OUTSIDE_SOURCE_MARKER" not in txt and "MarkerMod.lean" not in txt and "marker_thm_outside" not in str((sc.get("deep_audit") or {}).get("dynamic_probes")),
        "mcp/audit-absolute-module-probe-%s" % probe, "isError %s, outside file named/read: %s" % (err, "MarkerMod.lean" in txt))
p9 = subprocess.run(["python3", "-I", "-B", os.path.join(fv, "tools", "audit", "audit.py"), ce, "--no-probe"], capture_output=True, text=True, timeout=300)
row("OUTSIDE_SOURCE_MARKER" not in p9.stdout and "MarkerMod.lean" not in p9.stdout, "mcp/audit-cli-absolute-module",
    "exit %d, outside file in report: %s" % (p9.returncode, "MarkerMod.lean" in p9.stdout))
shutil.rmtree(od, ignore_errors=True)
# (7) bin/fv audit: symlinked --config / --reading-set are refused (no outside config read, no write through the link)
ocfg = os.path.join(outside, "ocfg.json")
json.dump({"challenge_module": "Challenge", "solution_module": "Challenge", "theorem_names": ["SECRET_CFG_THM_MCP"],
           "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}, open(ocfg, "w"))
vict = os.path.join(outside, "victim_rs.txt"); open(vict, "w").write("UNTOUCHED_RS\n")
os.symlink(ocfg, os.path.join(allowed, "sym_cfg.json")); os.symlink(vict, os.path.join(allowed, "sym_rs.lean"))
p10 = subprocess.run([os.path.join(fv, "bin", "fv"), "audit", ce, "--config", os.path.join(allowed, "sym_cfg.json"),
                      "--reading-set", os.path.join(allowed, "sym_rs.lean"), "--json"], capture_output=True, text=True, timeout=300)
row("SECRET_CFG_THM_MCP" not in p10.stdout + p10.stderr and open(vict).read() == "UNTOUCHED_RS\n", "mcp/cli-audit-symlinked-config-and-reading-set",
    "exit %d, cfg leaked %s, victim intact %s" % (p10.returncode, "SECRET_CFG_THM_MCP" in p10.stdout + p10.stderr, open(vict).read() == "UNTOUCHED_RS\n"))
open(os.path.join(w, "count"), "w").write("%d %d\n" % (P, F))
PY
read p f < "$W/count" 2>/dev/null || { p=0; f=1; }
# client-path/* and c/* rows: client lakefile srcDir, `import .abs.path`, lean-toolchain '..', unresolved client paths (client_path_rows.py)
python3 -I -B "$HERE/client_path_rows.py" "$FV" "$W" "$(cd "$HERE/../.." && pwd)"
read p4 f4 < "$W/count4" 2>/dev/null || { p4=0; f4=1; }
p=$((p + p4)); f=$((f + f4))
# hardlink/* rows: hard-link race after the open, MCP mint module name (hardlink_race_rows.py)
python3 -I -B "$HERE/hardlink_race_rows.py" "$FV" "$W"
read p6 f6 < "$W/count6a" 2>/dev/null || { p6=0; f6=1; }
p=$((p + p6)); f=$((f + f6))
# cli-path/* rows: bin/fv path policy (modulo-frontier, --extra-arg paths, bcache, pins, watch, flags), FV_CLI_ROOTS
python3 -I -B "$HERE/cli_path_rows.py" "$FV" "$W" "$(cd "$HERE/../.." && pwd)"
read p7 f7 < "$W/count6c" 2>/dev/null || { p7=0; f7=1; }
p=$((p + p7)); f=$((f + f7))
# git-file/* rows: challenge .lake/packages, `.git` file, `fv ci` under the local path policy
python3 -I -B "$HERE/git_file_rows.py" "$FV" "$W" "$HERE"
read p8 f8 < "$W/count6d" 2>/dev/null || { p8=0; f8=1; }
p=$((p + p8)); f=$((f + f8))
# cache-tree/* rows: --cache-dir / --incr-base trees, packages entries, frontier pin
# directories, CI report delivery, triage exit codes
python3 -I -B "$HERE/cache_tree_rows.py" "$FV" "$W"
read p9 f9 < "$W/count6e" 2>/dev/null || { p9=0; f9=1; }
p=$((p + p9)); f=$((f + f9))
# packagesdir/* rows: packagesDir from the workspace manifest, .git indirection, deep trees, triage
python3 -I -B "$HERE/packages_dir_rows.py" "$FV" "$W"
read p10 f10 < "$W/count6f" 2>/dev/null || { p10=0; f10=1; }
p=$((p + p10)); f=$((f + f10))
echo "RESULT pass=$p fail=$f"
[ "$f" = 0 ]

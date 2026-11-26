#!/usr/bin/env python3
"""tests/mcp-symlink-paths/hardlink_race_rows.py FV W -- hardlink/* rows (hard-link race, MCP mint module names):
  hardlink/hardlink-race-read, hardlink/hardlink-race-copy: a client file name flipped between a hard link to a secret outside the
    root and nothing (os.link / os.unlink in a loop): read_client_file / copy_client_file never return the secret (earlier versions
    checked st_nlink on the fd only: the link could be removed between open() and fstat; one earlier version read it ~3000 times in 30k)
  c/plain-file-read: a plain single-link file is still read (the post-open name re-check does not refuse normal files)
  hardlink/mcp-mint-invalid-module: fv_mint_subchallenges with module '../x' / '.abs.Mod' / 'A..B' -> refused before any build
Prints PASS/FAIL rows; writes "P F" to W/count6a."""
import json
import os
import subprocess
import sys
import threading

sys.dont_write_bytecode = True
fv, w = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(fv, "tools", "mcp"))
import mcp_server as M  # noqa: E402

P = F = 0


def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    if ok:
        P += 1
    else:
        F += 1


R = os.path.join(w, "hl_root")
os.makedirs(R)
sec = os.path.join(w, "hl_secret")
open(sec, "w").write("HL_SECRET\n")
tgt = os.path.join(R, "f")


def race(fn, n=30000):
    stop = threading.Event()

    def flip():
        while not stop.is_set():
            try:
                os.link(sec, tgt)
                os.unlink(tgt)
            except OSError:
                pass
    th = threading.Thread(target=flip, daemon=True)
    th.start()
    leaks = 0
    for i in range(n):
        try:
            if b"HL_SECRET" in fn(i):
                leaks += 1
        except (M.ClientPathError, OSError):
            pass
    stop.set()
    th.join(5)
    try:
        os.unlink(tgt)
    except OSError:
        pass
    return leaks


leaks = race(lambda i: M.read_client_file(tgt, [R]))
row(leaks == 0, "hardlink/hardlink-race-read", "secret returned %d times in 30000 reads" % leaks)
cdir = os.path.join(w, "hl_copies")
os.makedirs(cdir)


def copy_once(i):
    dst = os.path.join(cdir, "c%d" % i)
    M.copy_client_file(tgt, dst, [R])
    b = open(dst, "rb").read()
    os.unlink(dst)
    return b


leaks = race(copy_once, 15000)
row(leaks == 0, "hardlink/hardlink-race-copy", "secret copied %d times in 15000 copies" % leaks)
pf = os.path.join(R, "plain.lean")
open(pf, "w").write("theorem plain : True := trivial\n")
try:
    ok = M.read_client_file(pf, [R]) == b"theorem plain : True := trivial\n"
except (M.ClientPathError, OSError) as e:
    ok = False
row(ok, "c/plain-file-read", "plain single-link file read")

# MCP fv_mint_subchallenges: the module name is validated before anything runs
A = os.path.join(w, "hl_allowed")
proj = os.path.join(A, "proj")
os.makedirs(proj)
open(os.path.join(proj, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
open(os.path.join(proj, "lakefile.toml"), "w").write('name = "P"\ndefaultTargets = ["P"]\n[[lean_lib]]\nname = "P"\n')
open(os.path.join(proj, "P.lean"), "w").write("theorem t : True := by sorry\n")
for bad in ("../x", ".abs.Mod", "A..B"):
    reqs = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-11-25"}},
            {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "fv_mint_subchallenges", "arguments": {
                "project_dir": proj, "out_dir": os.path.join(A, "out_" + bad.replace("/", "_").replace(".", "d")),
                "theorems": ["t"], "module": bad, "threads": 2, "timeout": 300}}}]
    p = subprocess.run(["python3", "-I", "-B", os.path.join(fv, "tools", "mcp", "mcp_server.py"), "--allow-root", A],
                       input="".join(json.dumps(r) + "\n" for r in reqs), capture_output=True, text=True, timeout=900)
    res = {}
    for ln in p.stdout.splitlines():
        try:
            o = json.loads(ln)
        except ValueError:
            continue
        if o.get("id") == 2:
            res = o.get("result") or {}
    sc = res.get("structuredContent") or {}
    row(res.get("isError") is True and "invalid module name" in str(sc.get("error")), "hardlink/mcp-mint-invalid-module %s" % bad,
        "isError %s: %s" % (res.get("isError"), str(sc.get("error"))[:100]))
open(os.path.join(w, "count6a"), "w").write("%d %d\n" % (P, F))

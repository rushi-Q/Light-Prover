#!/bin/bash
# tests/sandbox-ipc/run.sh [WORKBASE] -- regression test: untrusted compiles cannot reach host IPC or other tenants (MEDIUM, S4 sandbox of
# every untrusted compile): same-uid bwrap with --ro-bind / let an attempt's elaboration code write a FIFO and connect to a
# pathname Unix socket on the read-only bind and read other files outside the hidden dirs (/scratch): stop fvserve / fvwork /
# fvcheckd, feed snapshots to the incr leg, read other attempts' sources. The probe of the
# reproduction is used here (FIFO write, socket connect + {"op":"stop"}, read of another tenant's file).
# Fix: every untrusted sandbox hides EVERY top-level directory except the system ones (and the given service
# state dirs) behind an empty, then read-only, tmpfs and binds back only the run's own dirs.
# Rows (each probe runs as a real attempt / module through the package's own entry point):
#   batchverify/*   tools/batchverify.py attempt          fvserve/*      tools/fvserve/fvserve.py attempt (cold compile) incl.
#   official-build/* build/official-build.sh module                        the service's OWN socket: {"op":"stop"} -> still alive
#   fast-build/*     build/build.sh (B1) module
#   */probe-ran: control - the attempt's code did run (the probe's marker is in the output), so a blocked row is the sandbox
# WORKBASE must be outside /tmp /home /var /run /root (the old sandbox already hid those); default /scratch/$USER-fvtest.
# Exit 0 iff every row PASS. FV_ROOT=<package> runs the rows against another package copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
DATA=$HERE/../build-guard-data
# WORKBASE must stay visible inside the sandboxes under test (they hide /tmp, /home, /root, /var, /run): the argument
# if given, else a visible default (tests/lib/visible_workdir.sh); SKIP only if there is none
. "$HERE/../lib/visible_workdir.sh"
fv_visible_workdir sandbox-ipc "${1:-}" || { echo "SKIP all rows: $FV_WORKDIR_WHY"; echo "RESULT pass=0 fail=0 (SKIP)"; exit 0; }
base=$FV_WORKDIR
mkdir -p "$base" && W=$(mktemp -d "$base/sandbox-ipc.XXXXXX") || exit 2
trap 'rm -rf "$W"' EXIT
(cd "$DATA" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
python3 -I -B - "$FV" "$W" "$DATA" <<'PY'
import json, os, shutil, socket, subprocess, sys, threading, time
sys.dont_write_bytecode = True
fv, w, data = sys.argv[1:4]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
comp = json.load(open(os.path.join(fv, "config", "components.json")))["lean_toolchains"]["leanprover/lean4:v4.33.1"]
tc = comp["prefix"]
# ---- the "service" endpoints and another tenant's file, outside every directory the old sandbox hid
svc, other = os.path.join(w, "svc"), os.path.join(w, "other")
os.makedirs(svc); os.makedirs(other)
fifo, sockp = os.path.join(svc, "cmd"), os.path.join(svc, "sock")
os.mkfifo(fifo, 0o600)
open(os.path.join(other, "secret_proof.lean"), "w").write("-- OTHER_TENANT_SECRET_Z02_1\n")
got = {"fifo": b"", "sock": b""}
stop = threading.Event()
def fifo_reader():
    fd = os.open(fifo, os.O_RDONLY | os.O_NONBLOCK)
    while not stop.is_set():
        try:
            b = os.read(fd, 4096)
            if b:
                got["fifo"] += b
        except BlockingIOError:
            pass
        time.sleep(0.05)
def sock_server():
    s = socket.socket(socket.AF_UNIX); s.bind(sockp); os.chmod(sockp, 0o600); s.listen(8); s.settimeout(0.2)
    while not stop.is_set():
        try:
            c, _ = s.accept()
        except socket.timeout:
            continue
        c.settimeout(2)
        try:
            got["sock"] += c.recv(1000)
        except OSError:
            pass
        c.close()
threading.Thread(target=fifo_reader, daemon=True).start()
threading.Thread(target=sock_server, daemon=True).start()

def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'
def probe_src(extra_sock=None, thm="thmA", mode="throw"):
    import shlex
    socks = [sockp] + ([extra_sock] if extra_sock else [])
    # short output (the attempt's error message is cut at 300 characters in batch.json): the secret first, then tokens only
    py = ("import socket,sys\nfor p in sys.argv[1:]:\n try:\n  s=socket.socket(socket.AF_UNIX);s.connect(p)\n"
          "  s.sendall(b'{\"op\": \"stop\"}\\n');print('SOCK_SENT')\n except Exception: print('SOCK_ERR')\n")
    script = (f"head -c 40 {other}/secret_proof.lean 2>/dev/null; (printf 'snap /injected.export\\n' > {fifo}) 2>/dev/null && "
              f"echo FIFO_WRITTEN; /usr/bin/python3 -I -c {shlex.quote(py)} {' '.join(socks)} 2>/dev/null; echo PROBE_DONE")
    body = (f"def probe : IO String := do\n  let o ← IO.Process.output {{cmd := \"/bin/sh\", args := #[\"-c\", {lean_str(script)}]}}\n"
            "  return o.stdout ++ o.stderr\n")
    if mode == "throw":   # the attempt's error message carries the probe output into batch.json / the answer
        body += ("def runProbe : IO Unit := do\n  let s ← probe\n"
                 "  throw <| IO.userError (\"PROBE[\" ++ s.replace \"\\n\" \" | \" ++ \"]\")\n#eval runProbe\n")
    else:                 # a build: the module writes the probe output into its (writable) project dir = cwd
        body += ("def runProbe : IO Unit := do\n  let s ← probe\n  IO.FS.writeFile \"probe.out\" s\n"
                 "  IO.println (\"PROBE[\" ++ s.replace \"\\n\" \" | \" ++ \"]\")\n#eval runProbe\n")
    return "import Init\n" + body + f"theorem {thm} : True := trivial\n"

def judge(prefix, text, before):
    ran = "PROBE_DONE" in text
    row(ran, prefix + "/probe-ran", "the attempt's probe ran" if ran else "probe output not found: " + text[-300:])
    f_new, s_new = got["fifo"][before[0]:], got["sock"][before[1]:]
    row(b"snap" not in f_new and "FIFO_WRITTEN" not in text, prefix + "/fifo-write-blocked",
        "no snapshot command reached the FIFO" if b"snap" not in f_new else f"FIFO received {f_new[:80]!r}")
    row(not s_new and "SOCK_SENT" not in text, prefix + "/socket-connect-blocked",
        "no connection reached the socket" if not s_new else f"socket received {s_new[:80]!r}")
    row("OTHER_TENANT_SECRET_Z02_1" not in text, prefix + "/other-file-hidden",
        "another tenant's file is not visible" if "OTHER_TENANT_SECRET_Z02_1" not in text else "read another tenant's file")

pset = os.path.join(w, "pset"); shutil.copytree(os.path.join(data, "pset"), pset)
chsha = __import__("hashlib").sha256(open(os.path.join(pset, "challenge.export"), "rb").read()).hexdigest()
ws = os.path.join(w, "ws"); os.makedirs(os.path.join(ws, ".lake", "packages", "dummy", ".lake", "build", "lib", "lean"))

# ---- batchverify
att = os.path.join(w, "att"); os.makedirs(att)
open(os.path.join(att, "thmA.lean"), "w").write(probe_src())
before = (len(got["fifo"]), len(got["sock"]))
p = subprocess.run(["python3", "-I", os.path.join(fv, "tools", "batchverify.py"), "--pset", pset, "--attempts", att,
                    "--out", os.path.join(w, "bv"), "--challenge-sha256", chsha, "--toolchain", tc, "--packages", ws,
                    "--threads", "2", "--jobs", "1", "--snapshot-header", ""], capture_output=True, text=True, timeout=900)
try:
    why = json.load(open(os.path.join(w, "bv", "batch.json")))["attempts"]["thmA"].get("why", "")
except (OSError, ValueError, KeyError):
    why = p.stdout[-500:] + p.stderr[-500:]
time.sleep(0.5)
judge("batchverify", why, before)

# ---- official-build.sh and build.sh (B1): a module whose elaboration runs the probe
for name, script, extra in (("official-build", "official-build.sh", []), ("fast-build", "build.sh", ["--preset", "B1"])):
    pj = os.path.join(w, name + "-proj"); os.makedirs(pj)
    open(os.path.join(pj, "lean-toolchain"), "w").write("leanprover/lean4:v4.33.1\n")
    open(os.path.join(pj, "lakefile.toml"), "w").write('name = "probe"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n')
    open(os.path.join(pj, "Main.lean"), "w").write(probe_src(mode="print"))
    log = os.path.join(w, name + "-log")
    before = (len(got["fifo"]), len(got["sock"]))
    p = subprocess.run([os.path.join(fv, "build", script), pj, "/nonexistent", tc, "--log", log, "--threads", "2"] + extra,
                       capture_output=True, text=True, timeout=1200)
    text = p.stdout + p.stderr
    try:
        text += open(os.path.join(pj, "probe.out"), errors="replace").read()
    except OSError:
        pass
    for r, _, fs in os.walk(log):
        for fn in fs:
            if fn.endswith((".log", ".out", ".err")):
                try:
                    text += open(os.path.join(r, fn), errors="replace").read()[-200000:]
                except OSError:
                    pass
    time.sleep(0.5)
    judge(name, text, before)

# ---- fvserve (cold compile): the attempt also tries the service's OWN socket
state = os.path.join(w, "fvs")
srv = subprocess.Popen(["python3", "-I", os.path.join(fv, "tools", "fvserve", "fvserve.py"), "serve", "--state", state,
                        "--pset", f"demo={pset}:{chsha}", "--toolchain", tc, "--packages", ws, "--threads", "2",
                        "--snapshot-header", "import Init", "--linger", "0.05"],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
ssock = os.path.join(state, "sock")
for _ in range(600):
    if os.path.exists(ssock) or srv.poll() is not None:
        break
    time.sleep(0.5)
def req(obj, timeout=600):
    s = socket.socket(socket.AF_UNIX); s.settimeout(timeout); s.connect(ssock)
    s.sendall((json.dumps(obj) + "\n").encode()); s.shutdown(socket.SHUT_WR)
    b = b""
    while True:
        c = s.recv(65536)
        if not c:
            break
        b += c
    return json.loads(b.decode())
if not os.path.exists(ssock):
    row(False, "fvserve/start", "fvserve did not start: " + (srv.stdout.read() if srv.poll() is not None else "timeout")[-400:])
else:
    before = (len(got["fifo"]), len(got["sock"]))
    try:
        r = req({"pset": "demo", "theorem": "thmB", "source": probe_src(extra_sock=ssock, thm="thmB")})
        text = r.get("why") or json.dumps(r)
    except (OSError, ValueError) as e:
        text = f"no answer ({e})"
    time.sleep(1.0)
    judge("fvserve", text, before)
    try:
        alive = "served" in json.dumps(req({"op": "stats"}, 30)) or True
    except (OSError, ValueError):
        alive = False
    row(alive and srv.poll() is None, "fvserve/service-socket-hidden",
        "the service survived an attempt sending {\"op\":\"stop\"} to its socket" if alive and srv.poll() is None
        else "the attempt stopped the service through its own socket")
    try:
        req({"op": "stop"}, 30)
    except (OSError, ValueError):
        pass
try:
    srv.wait(30)
except subprocess.TimeoutExpired:
    srv.kill()
stop.set()
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY

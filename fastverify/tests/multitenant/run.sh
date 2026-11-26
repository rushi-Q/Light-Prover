#!/bin/bash
# tests/multitenant/run.sh [WORKBASE] -- regression test: tenant isolation of batchverify and the fork server (HIGH, tools/batchverify.py
# + tools/fvserve/fvserve.py --fork-server, fork/FvFork.lean + fork/shim.c): (1) plain batchverify bound the whole batch
# project dir into every attempt's sandbox (attempt B read attempt A's source); (2) fork-server children could read every
# batch dir of the service (Landlock restricted writes only); (3) a child could leave a background process behind; (4) a
# child could kill the shared fvfork parent (kill -9 -1); (5) same-uid ptrace / /proc access to the unconfined parent.
# The probes here are those of the reproduction.
# Rows:
#   batch/*: thmB's elaboration tries to read thmA's source and .olean in the same batch -> nothing readable
#   fork/honest-via-fork: an honest attempt is ACCEPTED and compiled BY the fork server (fork_compiles >= 1, no fallback)
#   fork/chmod-attack-harmless: an attempt chmods STATE/batches and earlier batch dirs to 000 with
#     IO.setAccessRights -> modes unchanged, the next honest attempt ACCEPTED (base: the service is broken for everyone)
#   fork/deep-tree-attempt, fork/restart-after-deep-tree: a 1500-level tree built by an attempt (and
#     one planted in STATE/fork, with a mode-000 subdir) neither kills the batch nor stops a restart on the same state dir
#   fork/devshm-state: --state in /dev/shm with --fork-server -> fork server refused there, a
#     tenant cannot read another batch
#   c/*: harness.c, linked with this package's fork/shim.c, runs NATIVE probes in forked children inside
#     the fork-server sandbox: no signal / setpgid / setsid / prlimit64 / sched_* / setpriority / ioprio_set / tkill /
#     tgkill / fork / exec on the parent or a sibling, sibling pids neither listable nor inspectable in /proc, the parent not
#     signalled and the sibling not stopped; sanity: own signals, threads, own rlimits / priority, own /proc work
#   fork/cross-batch-read, fork/no-persistent-process, fork/parent-survives-kill, fork/parent-not-inspectable
#     (/proc/<parent>/environ), fork/legacy-binary-refused (an fvfork whose READY line lacks 'sandbox=2' is not used)
# Builds fvfork with the package's fork/build.sh and the official 4.33.1 toolchain (~1 min). Exit 0 iff every row PASS.
# FV_ROOT=<package> runs the rows against another package copy.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
DATA=$HERE/../build-guard-data
base=${1:-${TMPDIR:-/tmp}/$USER-fvtest}
mkdir -p "$base" && W=$(mktemp -d "$base/multitenant.XXXXXX") || exit 2
trap 'chmod -R u+rwx "$W" 2>/dev/null; rm -rf --one-file-system "$W"' EXIT   # (a base copy may be left with mode-000 dirs)
(cd "$DATA" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json")
"$FV/tools/fvserve/fork/build.sh" "$TC" "$W/fk" > "$W/fk.log" 2>&1 || { echo "FAIL setup: fork/build.sh failed"; tail -5 "$W/fk.log"; echo "RESULT pass=0 fail=1"; exit 1; }
mkdir -p "$W/fksrc" && cp "$FV/tools/fvserve/fork/"* "$W/fksrc/" && sed -i 's/ sandbox=2//' "$W/fksrc/FvFork.lean" \
  && "$W/fksrc/build.sh" "$TC" "$W/fklegacy" > "$W/fklegacy.log" 2>&1 || { echo "FAIL setup: legacy build failed"; echo "RESULT pass=0 fail=1"; exit 1; }
# C-level policy probe: harness.c linked with the package's own fork/shim.c (built like fork/build.sh)
HXB=1
( set -e; mkdir -p "$W/hx"; cp "$FV/tools/fvserve/fork/shim.c" "$HERE/harness.c" "$W/hx/"; cd "$W/hx"
  I="-idirafter /usr/include/x86_64-linux-gnu -idirafter /usr/include"
  "$TC/bin/leanc" -c -O2 $I -o shim.o shim.c && "$TC/bin/leanc" -c -O2 $I -o harness.o harness.c
  PARTS=$(cd "$TC/lib/lean" && ls libleanshared_[0-9]*.so 2>/dev/null | sed 's/^lib\(leanshared_[0-9]*\)\.so$/\1/' | sort -t_ -k2,2nr | sed 's/^/-l/' | tr '\n' ' ')
  "$TC/bin/clang" --sysroot "$TC" -fuse-ld=lld -o harness harness.o shim.o -L "$TC/lib" -L "$TC/lib/glibc" -L "$TC/lib/lean" \
    -lc -lc_nonshared -Wl,--as-needed -l:ld.so -Wl,--no-as-needed -lpthread_nonshared -lInit_shared $PARTS -lleanshared \
    -Wl,-rpath,"$TC/bin/../lib/lean" -lpthread -ldl -lm -rdynamic ) > "$W/hx.log" 2>&1 || HXB=0
export HXB
python3 -I -B - "$FV" "$W" "$DATA" "$TC" <<'PY'
import hashlib, json, os, shutil, socket, subprocess, sys, tempfile, time
sys.dont_write_bytecode = True
fv, w, data, tc = sys.argv[1:5]
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg, flush=True)
    P, F = (P + 1, F) if ok else (P, F + 1)
pset = os.path.join(w, "pset"); shutil.copytree(os.path.join(data, "pset"), pset)
chsha = hashlib.sha256(open(os.path.join(pset, "challenge.export"), "rb").read()).hexdigest()
ws = os.path.join(w, "ws"); os.makedirs(os.path.join(ws, ".lake", "packages", "dummy", ".lake", "build", "lib", "lean"))
SLEEP = str(37000 + os.getpid() % 10000)   # unique per run: concurrent runs never see each other's sleeper

# ---- [1] plain batchverify: same-batch read of another attempt's source / .olean
att = os.path.join(w, "att"); os.makedirs(att)
open(os.path.join(att, "thmA.lean"), "w").write("-- TENANT_A_SAME_BATCH_SECRET_Z03_13\ntheorem thmA : True := trivial\n")
open(os.path.join(att, "thmB.lean"), "w").write(r'''
def tryRead (p : System.FilePath) : IO String := do
  try
    let b ← IO.FS.readBinFile p
    return s!"[{p}: READ {b.size} bytes {String.fromUTF8! (b.extract 0 (min b.size 60)) |>.replace "\n" " "}]"
  catch e => return s!"[{p}: {e}]"
def steal : IO Unit := do
  let mut s := ""
  for p in ["Attempt/thmA.lean", "build/lib/lean/Attempt/thmA.olean", "../batch.json", "../log"] do
    s := s ++ (← tryRead p)
  throw <| IO.userError ("STEAL " ++ s)
#eval steal
theorem thmB : True := trivial
''')
p = subprocess.run(["python3", "-I", os.path.join(fv, "tools", "batchverify.py"), "--pset", pset, "--attempts", att,
                    "--out", os.path.join(w, "bv"), "--challenge-sha256", chsha, "--toolchain", tc, "--packages", ws,
                    "--threads", "2", "--jobs", "1", "--snapshot-header", ""], capture_output=True, text=True, timeout=900)
try:
    bj = json.load(open(os.path.join(w, "bv", "batch.json")))
    whyB, vA = bj["attempts"]["thmB"].get("why", ""), bj["attempts"]["thmA"].get("verdict")
except (OSError, ValueError, KeyError):
    whyB, vA = p.stderr[-300:], None
row("STEAL" in whyB and "TENANT_A_SAME_BATCH_SECRET" not in whyB and "READ" not in whyB, "batch/same-batch-read",
    "thmB could read nothing of the batch: " + whyB[whyB.find("STEAL"):][:200] if "STEAL" in whyB else "probe did not run: " + whyB[-200:])
row(vA == "ACCEPTED", "batch/control-honest-accepted", f"thmA verdict {vA}")

# ---- [2] fvserve --fork-server
def find_procs(prefix):
    out = []
    for pid in os.listdir("/proc"):
        if pid.isdigit():
            try:
                cmd = open(f"/proc/{pid}/cmdline", "rb").read().replace(b"\x00", b" ").decode(errors="replace").strip()
            except OSError:
                continue
            if cmd.startswith(prefix):
                out.append(int(pid))
    return out
def serve(state, binary):
    srv = subprocess.Popen(["python3", "-I", os.path.join(fv, "tools", "fvserve", "fvserve.py"), "serve", "--state", state,
                            "--pset", f"demo={pset}:{chsha}", "--toolchain", tc, "--packages", ws, "--threads", "4",
                            "--keep", "10", "--linger", "0.05", "--snapshot-header", "import Init\n", "--fork-server", binary],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    for _ in range(600):
        if os.path.exists(os.path.join(state, "sock")) or srv.poll() is not None:
            break
        time.sleep(0.5)
    return srv
def req(state, obj, timeout=600):
    s = socket.socket(socket.AF_UNIX); s.settimeout(timeout); s.connect(os.path.join(state, "sock"))
    s.sendall((json.dumps(obj) + "\n").encode()); s.shutdown(socket.SHUT_WR)
    b = b""
    while True:
        c = s.recv(65536)
        if not c:
            break
        b += c
    return json.loads(b.decode())
def stop(state, srv):
    subprocess.run(["python3", "-I", os.path.join(fv, "tools", "fvserve", "fvserve.py"), "stop", "--state", state], capture_output=True)
    try:
        srv.wait(30)
    except subprocess.TimeoutExpired:
        srv.kill()
def events(state):
    try:
        return [json.loads(l) for l in open(os.path.join(state, "service.jsonl"))]
    except (OSError, ValueError):
        return []

state = os.path.join(w, "fvs"); fvfork = os.path.join(w, "fk", "fvfork")
srv = serve(state, fvfork)
if not os.path.exists(os.path.join(state, "sock")):
    row(False, "fork/start", "fvserve did not start: " + (srv.stdout.read() if srv.poll() is not None else "timeout")[-400:])
else:
    r1 = req(state, {"pset": "demo", "theorem": "thmA",
                     "source": "import Init\n-- TENANT_A_HISTORICAL_BATCH_SECRET_Z03_13\ntheorem thmA : True := trivial\n"})
    st = req(state, {"op": "stats"}, 60)
    stats = st.get("verdicts") or {}   # the service's counters (fvserve 'stats' op)
    fc, ff = stats.get("fork_compiles", 0), stats.get("fork_fallback", 0)
    row(r1.get("verdict") == "ACCEPTED" and fc >= 1 and not ff, "fork/honest-via-fork",
        f"verdict {r1.get('verdict')}, fork_compiles {fc}, fork_fallback {ff}")
    spy = f'''import Init
def spy : IO Unit := do
  let mut s := ""
  try
    for e in (← System.FilePath.readDir "{state}/batches") do
      let p := e.path / "out" / "proj" / "Attempt" / "thmA.lean"
      if (← p.pathExists) then
        s := s ++ "[" ++ e.fileName ++ "]=" ++ ((← IO.FS.readFile p).replace "\\n" " | ")
  catch _ => s := s ++ " RD_DENIED"
  try
    let o ← IO.Process.output {{ cmd := "/bin/sh", args := #["-c", "nohup /bin/sleep {SLEEP} >/dev/null 2>&1 </dev/null & echo PERSIST_PID=$!"] }}
    s := s ++ " " ++ o.stdout.trim
  catch _ => s := s ++ " SPAWN_DENIED"
  let stat ← IO.FS.readFile "/proc/self/stat"
  let ppid := ((stat.splitOn ") ").getD 1 "").splitOn " " |>.getD 1 "0"
  try
    let pst ← IO.FS.readFile s!"/proc/{{ppid}}/stat"
    s := s ++ " PARENT=" ++ ((pst.splitOn "(").getD 1 "").takeWhile (· != ')')
  catch _ => s := s ++ " PARENT=?"
  try
    let env ← IO.FS.readFile s!"/proc/{{ppid}}/environ"
    s := s ++ s!" ENVIRON_READ_OK({{env.length}})"
  catch _ => s := s ++ " ENV_DENIED"
  throw <| IO.userError ("SPY" ++ s)
#eval spy
theorem thmB : True := trivial
'''
    r2 = req(state, {"pset": "demo", "theorem": "thmB", "source": spy})
    why = r2.get("why") or ""
    time.sleep(1.0)
    row("SPY" in why and "TENANT_A_HISTORICAL_BATCH_SECRET" not in why, "fork/cross-batch-read",
        "no other batch readable: " + why[why.find("SPY"):][:160] if "SPY" in why else "probe did not run: " + why[-200:])
    sl = find_procs("/bin/sleep " + SLEEP)
    row("SPY" in why and not sl, "fork/no-persistent-process", "no process outlives the attempt" if not sl else f"alive: {sl}")
    infork = "PARENT=fvfork" in why or "PARENT=?" in why   # older sandbox: the parent visible, its environ not; current: /proc/<ppid> unreadable
    row(infork and "ENVIRON_READ_OK" not in why, "fork/parent-not-inspectable",
        ("the fvfork parent's /proc/PID entries are not readable (" + ("PARENT=?" if "PARENT=?" in why else "environ") + ")"
         if "ENVIRON_READ_OK" not in why else "read the fvfork parent's environ") if infork
        else "the probe did not run in a fork child: " + why[-160:])
    # plain-Lean IO.setAccessRights on STATE/batches and earlier batch dirs (path from /proc/self/cmdline)
    chm = '''import Init
def atk : IO Unit := do
  let cl ← IO.FS.readFile "/proc/self/cmdline"
  let snap := (cl.splitOn (String.singleton (Char.ofNat 0))).getD 1 ""
  let st := ((System.FilePath.mk snap).parent.bind (·.parent)).bind (·.parent) |>.getD "?"
  for n in ["b000001", "b000002", "b000003"] do
    try IO.setAccessRights (st / "batches" / n) {} catch _ => pure ()
  try IO.setAccessRights (st / "batches") {} catch _ => pure ()
#eval atk
theorem thmB : True := trivial
'''
    req(state, {"pset": "demo", "theorem": "thmB", "source": chm})
    try:
        bmode = os.stat(os.path.join(state, "batches")).st_mode & 0o777
        old_ok = all(os.access(os.path.join(state, "batches", e), os.R_OK | os.X_OK)
                     for e in os.listdir(os.path.join(state, "batches")))
    except OSError as e:
        bmode, old_ok = -1, False
    if bmode != 0o700:   # repair (base copy), so that the remaining rows still run
        subprocess.run(["chmod", "-R", "u+rwx", os.path.join(state, "batches")], capture_output=True)
    try:
        r5 = req(state, {"pset": "demo", "theorem": "thmA", "source": "import Init\ntheorem thmA : True := trivial\n"}, 300)
    except (OSError, ValueError) as e:
        r5 = {"verdict": f"request failed ({e})"}
    row(bmode == 0o700 and old_ok and r5.get("verdict") == "ACCEPTED", "fork/chmod-attack-harmless",
        f"batches mode {oct(bmode) if bmode >= 0 else 'unreadable'}, earlier batch dirs accessible {old_ok}, next honest attempt {r5.get('verdict')}")
    before = find_procs(fvfork)
    killer = '''import Init
def killAll : IO Unit := do
  try
    let _ ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "kill -9 -1"] }
  catch _ => pure ()
#eval killAll
theorem thmB : True := trivial
'''
    req(state, {"pset": "demo", "theorem": "thmB", "source": killer})
    time.sleep(1.0)
    after = find_procs(fvfork)
    row(bool(before) and bool(after), "fork/parent-survives-kill", f"fvfork before {before}, after {after}")
    # an attempt builds a 1500-level directory tree in its private dir; the service must answer it,
    # stay up, and a RESTART on the same state dir must come up (also with such a tree left in STATE/fork) and serve
    deep = '''import Init
def deep : IO Unit := do
  let lg ← IO.FS.realPath "/proc/self/fd/1"
  let priv := lg.parent.getD "?"
  IO.Process.setCurrentDir priv
  for _ in [0:1500] do
    IO.FS.createDir "d"
    IO.Process.setCurrentDir "d"
#eval deep
theorem thmB : True := trivial
'''
    try:
        rd = req(state, {"pset": "demo", "theorem": "thmB", "source": deep}, 300)
    except (OSError, ValueError) as e:
        rd = {"verdict": f"request failed ({e})"}
    alive = srv.poll() is None
    row(alive and "service error" not in str(rd.get("why", "")) and rd.get("verdict") in ("ACCEPTED", "REJECTED", "NO-VERDICT"),
        "fork/deep-tree-attempt", f"answered {rd.get('verdict')} ({str(rd.get('why', ''))[:80]}), service alive {alive}")
    stop(state, srv)
    planted = os.path.join(state, "fork", "fk.planted")   # a leftover as after a crash: 1500 levels, a mode-000 subdir
    subprocess.run(["mkdir", "-p", os.path.join(planted, *(["d"] * 1500)), os.path.join(planted, "locked", "x")],
                   capture_output=True)   # (coreutils mkdir -p: iterative; os.makedirs recurses per level)
    subprocess.run(["chmod", "0", os.path.join(planted, "locked")], capture_output=True)
    try:
        os.unlink(os.path.join(state, "sock"))   # (the stopped service's socket file: wait for the NEW one)
    except OSError:
        pass
    srv = serve(state, fvfork)
    up = os.path.exists(os.path.join(state, "sock")) and srv.poll() is None
    try:
        r6 = req(state, {"pset": "demo", "theorem": "thmA", "source": "import Init\ntheorem thmA : True := trivial\n"}, 300) if up else {}
    except (OSError, ValueError) as e:
        r6 = {"verdict": f"request failed ({e})"}
    row(up and r6.get("verdict") == "ACCEPTED", "fork/restart-after-deep-tree",
        f"restart on the same state: up {up} (exit {srv.poll()}), honest attempt {r6.get('verdict')} {str(r6.get('why', ''))[:80]}")
    if up:
        stop(state, srv)
    else:
        print((srv.stdout.read() if srv.poll() is not None else "")[-600:])
for pid in find_procs("/bin/sleep " + SLEEP):
    try:
        os.kill(pid, 9)
    except OSError:
        pass
# ---- an fvfork without the child sandbox announcement is never used
state2 = os.path.join(w, "fvs-legacy")
srv = serve(state2, os.path.join(w, "fklegacy", "fvfork"))
ev = events(state2)
started = [e for e in ev if e.get("event") == "startup"]
used = started[0].get("fork_server") if started else None
row(started and used is False and any(e.get("event") == "fork-server-refused" for e in ev), "fork/legacy-binary-refused",
    f"fork_server {used}, events {[e.get('event') for e in ev if 'fork' in str(e.get('event'))]}")
if os.path.exists(os.path.join(state2, "sock")):
    stop(state2, srv)
else:
    srv.kill()
# ---- --state in /dev/shm with --fork-server: the fork server is not used there (a state dir
# below /dev, or below any tree the children may read, is refused for it), and a tenant cannot read another batch
if os.path.isdir("/dev/shm"):
    state3 = tempfile.mkdtemp(prefix="z0313-fvs.", dir="/dev/shm")
    try:
        srv = serve(state3, fvfork)
        if not os.path.exists(os.path.join(state3, "sock")):
            row(False, "fork/devshm-state", "fvserve did not start: " + (srv.stdout.read() if srv.poll() is not None else "timeout")[-300:])
        else:
            req(state3, {"pset": "demo", "theorem": "thmA",
                         "source": "import Init\n-- TENANT_A_DEVSHM_SECRET_Z03_13\ntheorem thmA : True := trivial\n"})
            spy3 = f'''import Init
def spy : IO Unit := do
  let mut s := ""
  try
    for e in (← System.FilePath.readDir "{state3}/batches") do
      let p := e.path / "out" / "proj" / "Attempt" / "thmA.lean"
      if (← p.pathExists) then
        s := s ++ "[" ++ e.fileName ++ "]=" ++ ((← IO.FS.readFile p).replace "\\n" " | ")
  catch _ => s := s ++ " RD_DENIED"
  throw <| IO.userError ("SPY" ++ s)
#eval spy
theorem thmB : True := trivial
'''
            r3 = req(state3, {"pset": "demo", "theorem": "thmB", "source": spy3})
            why3 = r3.get("why") or ""
            ev3 = events(state3)
            refused = any(e.get("event") == "fork-server-refused" for e in ev3)
            row("SPY" in why3 and "TENANT_A_DEVSHM_SECRET" not in why3 and refused, "fork/devshm-state",
                f"fork server refused for a /dev/shm state: {refused}; spy: " + why3[why3.find("SPY"):][:120])
            stop(state3, srv)
    finally:
        subprocess.run(["chmod", "-R", "u+rwx", state3], capture_output=True)
        shutil.rmtree(state3, ignore_errors=True)
# ---- the child sandbox against NATIVE code: harness.c (linked with the package's shim.c) forks a victim
# sibling and attackers in the fork-server sandbox (batchverify.sandbox, mask = STATE, FVFORK_READ as ForkServer sets it)
CROWS = ["setup", "kill-parent", "kill-all", "kill-sibling", "kill-parent-group", "kill-own-group-sane", "threads-sane",
         "own-session", "parent-environ", "sibling-proc-stat", "proc-not-listable", "own-proc-readable", "sibling-log",
         "setpgid-parent-group", "setpgid-sibling-group", "setsid", "parent-not-signalled", "sibling-not-stopped",
         "prlimit-sibling", "prlimit-parent", "getrlimit-own-sane", "affinity-sibling", "setpriority-sibling",
         "setpriority-user", "setpriority-own-sane", "setscheduler-sibling", "setparam-sibling", "ioprio-sibling", "tkill",
         "tgkill-sibling", "fork", "exec", "sibling-limits-unchanged",
         # no metadata changes / watches
         "chmod-sibling-file", "chmod-sibling-dir", "chmod-batch-dir", "fchmodat-sibling-dir", "fchmod-own-fd",
         "chown-sibling-dir", "utimensat-sibling-dir", "setxattr-sibling-dir", "inotify", "fanotify", "modes-unchanged",
         # every denied syscall by number (x86_64)
         "sc-chmod", "sc-chown", "sc-lchown", "sc-utime", "sc-utimes", "sc-futimesat", "sc-inotify_init", "sc-fchmod",
         "sc-fchmodat", "sc-fchmodat2", "sc-fchown", "sc-fchownat", "sc-utimensat", "sc-utimensat-fd", "sc-setxattr",
         "sc-lsetxattr", "sc-fsetxattr", "sc-removexattr", "sc-lremovexattr", "sc-fremovexattr", "sc-inotify_init1",
         "sc-inotify_add_watch", "sc-fanotify_init", "sc-fanotify_mark", "sc-setxattrat", "sc-removexattrat", "sc-file_setattr"]
if os.environ.get("HXB") != "1":
    row(False, "c/harness-build", "harness.c does not link with this package's fork/shim.c (no fv_child_setup2 child sandbox): "
        + open(os.path.join(w, "hx.log"), errors="replace").read()[-200:].replace("\n", " "))
else:
    hw = os.path.join(w, "hxw"); hst = os.path.join(hw, "st"); hb = os.path.join(hst, "batches"); hsnap = os.path.join(hst, "snap", "k")
    hws = os.path.join(hw, "ws", ".lake", "packages"); hbin = os.path.join(hw, "bin")
    for d in (os.path.join(hb, "b1"), hsnap, hws, hbin):
        os.makedirs(d, exist_ok=True)
    shutil.copy(os.path.join(w, "hx", "harness"), os.path.join(hbin, "harness"))
    open(os.path.join(hb, "b1", "src.lean"), "w").write("theorem t : True := trivial\n")
    sys.path.insert(0, os.path.join(fv, "tools"))
    import batchverify as bvm
    hro = [hsnap, hbin]
    henv = {"FVFORK_READ": ":".join([tc, hws] + hro)}
    try:
        hargv = bvm.sandbox(tc, hws, rw=[hb], ro=hro, chdir="/", mask=[hst], env=henv)
    except TypeError:
        hargv = bvm.sandbox(tc, hws, rw=[hb], ro=hro, chdir="/", env=henv)
    hargv += [os.path.join(hbin, "harness"), os.path.join(hb, "b1"), os.path.join(hb, "b1", "src.lean")]
    try:
        hp = subprocess.run(hargv, env={}, capture_output=True, text=True, timeout=120)
        hout = hp.stdout + hp.stderr
    except subprocess.TimeoutExpired as e:
        hout = "harness timed out (a child stopped or wedged the parent?) " + str(e.stdout or "")[-300:]
    for d in ("a1", "a2", "a3", "a4", "a5", "a6"):
        try:
            hout += open(os.path.join(hb, "b1", d, "log"), errors="replace").read()
        except OSError:
            pass
    got = {}
    for ln in hout.splitlines():
        f = ln.split(" ", 3)
        if len(f) >= 3 and f[0] == "ROW":
            got[f[1]] = (f[2] == "ok", f[3] if len(f) > 3 else "")
    for name in CROWS:
        ok, det = got.get(name, (False, "no result (" + hout.strip().splitlines()[-1][:120] + ")" if hout.strip() else "no output"))
        row(ok, "c/" + name, det or "ok")
print(f"RESULT pass={P} fail={F}")
sys.exit(0 if F == 0 else 1)
PY

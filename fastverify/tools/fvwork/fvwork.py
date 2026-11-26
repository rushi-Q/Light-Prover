#!/usr/bin/python3 -I
"""tools/fvwork/fvwork.py - a persistent per-repository SOUND verification daemon for the edit loop.

A mathematician or a coding / proving agent edits a Lean project many times a day and wants, after each edit, the sound
verdict of the whole project against its pinned challenge ("are my claims still proved, from the permitted axioms, with
every declaration kernel-checked?") plus the compiler feedback of the edit. `fvwork` keeps everything that does not
depend on the edit warm between requests:

  * one owned build tree + Lake plan of the last verified state (the "base"; untrusted; every request is built
    EXACTLY - every reverse dependency of every changed module is rebuilt, as a fresh build would - and incr-build.py
    verifies that the outputs are the submitted tree's, else no verdict);
  * the pinned challenge export (private copy, sha256 re-checked before every check);
  * PRE-WARMED Lean-kernel legs: `pleanchecker_incr` servers (pinned) fed with the base export as an
    UNTRUSTED snapshot while the user thinks, so the request's Lean leg replays only what changed;
  * the trusted check's integrity cache (`check/sound/check-sound-svc.sh --integrity-cache`);
  * the planner / plugin / toolchain choices of the cold run.

Per request (a working tree, a git revision or a set of changed files): materialize the sources, rebuild the dirty modules
(tools/incr/incr-build.py; default --mode full = exact; --mode optimistic / interface are EXPERIMENTAL: they keep importers
of an edited module, which can hold what they obtained at elaboration time from its OLD version - macros, tactics,
instances -, so their ACCEPTED is only provisional: it is confirmed by an exact build, or reported as NO-VERDICT),
export (export/export.sh, the native exporter), and run the UNCHANGED trusted check on that export against the pinned
official challenge export. The verdict is the trusted check's; nothing in this file is trusted (README 1b: build, export,
orchestration, caching of build outputs and snapshot feeding are untrusted in sound mode - each can only cost a verdict).

  fvwork.py init   --state S --project P --challenge C --challenge-sha256 H [--packages WS] [--threads N]
                   [--fv PKG] [--tc TC433] [--items LIST] [--adopt OUT] [--closure-only]
  fvwork.py serve  --state S [--jobs K] [--warm W] [--threads N] [--mode full|optimistic|interface] [--foreground]
  fvwork.py verify --state S (--tree DIR | --git REPO --rev REV | --files JSON) [--no-advance] [--stream] [--label L]
  fvwork.py status|stop --state S

Exit of `verify`: 0 ACCEPTED, 1 REJECTED, 2 no verdict (for rewards / CI gates: no verdict counts as REJECTED).
"""
import argparse, glob, hashlib, json, os, re, shutil, signal, socket, socketserver, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.realpath(__file__))
PY = "/usr/bin/python3"
# portable trees first (glibc 2.17+; the plain s01zy/pgo trees need glibc 2.38 and are skipped on glibc-2.35 hosts,
# where the build otherwise falls back to the nopgo tree WITHOUT zygote - far slower cold builds)
DEFAULT_ITEMS = ("toolchain-T1=lean4-s01zy-3cf5641cbd-pgo-portable lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo-portable "
                 "lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo,skip-kernel-tc,"
                 "linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,"
                 "sound-fast-path=importarts-empty,cost-hints,native-pkg,check-tail")
VERDICT = {0: "ACCEPTED", 1: "REJECTED", 3: "CONDITIONAL"}


def now():
    return time.time()


def sha256_file(p, bs=1 << 22):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        while True:
            b = f.read(bs)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


class StatSha:
    """sha256 of a file, recomputed only when (dev, ino, size, mtime_ns, ctime_ns) changes"""

    def __init__(self):
        self.c, self.lock = {}, threading.Lock()

    def __call__(self, p):
        try:
            link = os.readlink(p) if os.path.islink(p) else None
            st = os.stat(p)   # a symlink counts by its link text AND its target's content
        except OSError:
            return "missing" if not os.path.lexists(p) else "symlink:%s:dangling" % (os.readlink(p),)
        pre = "" if link is None else "symlink:" + link + ":"
        if not os.path.isfile(p):
            return pre + "special"
        k = (link, st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
        with self.lock:
            hit = self.c.get(p)
        if hit and hit[0] == k:
            return hit[1]
        try:
            h = pre + sha256_file(p)
        except OSError:
            return pre + "unreadable"
        with self.lock:
            self.c[p] = (k, h)
        return h


def verdict_files(fv):
    """every file of the package that can change a verdict of the trusted check (its scripts, pins,
    gates - check/xversion/xvcheck.py, releases.json -, toolchain manifests and verifier, config): ALL regular files under
    check/, config/, lib/ and toolchains/ (re-listed on every call, so an added file counts too; __pycache__ skipped)"""
    out = []
    for d in ("check", "config", "lib", "toolchains"):
        top = os.path.join(fv, d)
        seen = set()
        for root, dirs, files in os.walk(top, followlinks=True):   # symlinked directories descended
            rr = os.path.realpath(root)
            if rr in seen:   # (a link cycle)
                dirs[:] = []
                continue
            seen.add(rr)
            dirs[:] = sorted(x for x in dirs if x != "__pycache__")
            out.extend(os.path.join(root, f) for f in files)
    return sorted(out)


def jload(p, default=None):
    try:
        with open(p) as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def jdump(p, obj):
    tmp = p + ".tmp%d" % os.getpid()
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=1)
    os.replace(tmp, p)


def pkg_root(cfg):
    return cfg["fv"]


# ---------------------------------------------------------------------------------------------------------------- init
def strict_dir(what, v, must_exist=True):
    """a caller's directory argument, strictly: non-empty, (existing) and a directory, never "/" (also through
    links); anything else is a usage error: exit 2 before anything is created or copied"""
    ok = isinstance(v, str) and v != ""
    rp = os.path.realpath(v) if ok else ""
    if ok and must_exist:
        ok = os.path.isdir(v) and os.path.isdir(rp)
    if ok and not must_exist:
        ok = not os.path.lexists(v) or os.path.isdir(rp)
    if not ok or rp == "/":
        print(f"fvwork: {what} {v!r} is not a usable directory (empty, missing, not a directory, or /): no verdict",
              file=sys.stderr)
        sys.exit(2)
    return rp


def hex64(v):
    """a 64-hex sha256 pin; anything else (also an empty string) is a usage error (argparse: exit 2)"""
    if not re.fullmatch(r"[0-9a-f]{64}", v or ""):
        raise argparse.ArgumentTypeError("must be a sha256: 64 lowercase hex characters")
    return v


def cmd_init(a):
    strict_dir("--project", a.project); strict_dir("--challenge", a.challenge)   # before anything is created
    if a.adopt:
        strict_dir("--adopt", a.adopt)
    st = strict_dir("--state", a.state, must_exist=False)
    if os.path.exists(os.path.join(st, "config.json")):
        sys.exit(f"fvwork init: {st} is already initialized")
    os.makedirs(st, exist_ok=True)
    os.chmod(st, 0o700)
    fv = os.path.realpath(a.fv or os.environ.get("FASTVERIFY") or os.path.dirname(os.path.dirname(HERE)))
    ch = os.path.realpath(a.challenge)
    for f in ("challenge.export", "comparator.json"):
        if not os.path.isfile(os.path.join(ch, f)):
            sys.exit(f"fvwork init: {ch}/{f} missing (sound mode needs the official challenge export, pinned)")
    chd = os.path.join(st, "challenge")
    os.makedirs(chd, exist_ok=True)
    for f in ("challenge.export", "comparator.json"):
        shutil.copyfile(os.path.join(ch, f), os.path.join(chd, f))
        os.chmod(os.path.join(chd, f), 0o400)
    for f in ("lean-toolchain", "challenge.export.sha256", "comparator.json.sha256"):   # the inputs
        if os.path.isfile(os.path.join(ch, f)):   # bin/fastverify (the cold path) reads or validates besides the two
            shutil.copyfile(os.path.join(ch, f), os.path.join(chd, f))
    # a CLEAN snapshot of the project as submitted, taken before any build can touch a tree; the
    # cold path materializes --files requests over it (never over a build tree)
    src0 = os.path.join(st, "src0")
    r0 = subprocess.run(["rsync", "-a", "--delete", "--exclude=/.lake",   # only bin/fastverify's exclusion
                         os.path.realpath(a.project) + "/", src0 + "/"], capture_output=True, text=True)
    if r0.returncode != 0:
        sys.exit("fvwork init: cannot snapshot the project sources: " + r0.stderr.strip()[:300])
    got = sha256_file(os.path.join(chd, "challenge.export"))
    if got != a.challenge_sha256:
        sys.exit(f"fvwork init: challenge export sha256 {got} != pin {a.challenge_sha256}")
    cfg_got = sha256_file(os.path.join(chd, "comparator.json"))   # the comparator config's pin
    # the caller's pin is REQUIRED (argparse: 64 hex); it must match the copied config
    if cfg_got != a.comparator_sha256:
        print(f"fvwork init: comparator config sha256 {cfg_got} != pin {a.comparator_sha256}: refused", file=sys.stderr)
        sys.exit(2)   # no config.json written: the directory is not a state
    cm = jload(os.path.join(chd, "comparator.json"))["solution_module"]
    # A04's cross-version gate (veto only), as bin/fastverify runs it in sound mode: the challenge's release must be one
    # the 4.36 trusted check judges soundly; its extra comparator rules (4.37) apply to every verdict of this state
    xv = subprocess.run([PY, "-I", os.path.join(fv, "check", "xversion", "xvcheck.py"), os.path.join(chd, "challenge.export"),
                         os.path.join(chd, "comparator.json"), "--json", os.path.join(st, "xversion.json")],
                        capture_output=True, text=True)
    if xv.returncode != 0:
        sys.exit(f"fvwork init: cross-version gate exit {xv.returncode} ({xv.stdout.strip()[-300:]}): no state")
    rel = jload(os.path.join(st, "xversion.json"), {}).get("lean_version")
    if a.tc:
        tc = os.path.realpath(a.tc)
    else:
        comp = jload(os.path.join(fv, "config", "components.json"), {})
        tcn = open(os.path.join(a.project, "lean-toolchain")).read().strip()
        tc = ((comp.get("lean_toolchains") or {}).get(tcn) or {}).get("prefix") or \
            os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1")
    ws = os.path.realpath(a.packages or os.path.expanduser("~/light_lean/verify/challenge"))
    threads = a.threads or os.cpu_count()
    if a.build == "lake":
        return init_lake(a, st, fv, ch, chd, cm, tc, ws, threads, rel)
    rc = None   # exit of the cold run (None with --adopt)
    if a.adopt:
        out = os.path.realpath(a.adopt)
    else:
        out = os.path.join(st, "cold")
        if a.items == "auto":   # the untrusted B3 items lib/autotune.py picks for this project and host, minus merge
            import importlib.util
            sp = importlib.util.spec_from_file_location("fv_autotune", os.path.join(fv, "lib", "autotune.py"))
            atm = importlib.util.module_from_spec(sp)
            sp.loader.exec_module(atm)
            plan = atm.plan(os.path.realpath(a.project), ws, threads, fv)
            a.items = ",".join(u for u in plan["unsafe"] if u.split("=", 1)[0] != "merge")
            print("fvwork init: autotune items:", a.items, flush=True)
        if sha256_file(os.path.join(ch, "comparator.json")) != cfg_got:   # the config passed = the copy
            sys.exit("fvwork init: the comparator config changed while it was copied: refused")
        argv = [os.path.join(fv, "bin", "fastverify"), os.path.realpath(a.project), ch, out, "--preset", "sound",
                "--threads", str(threads), "--packages", ws, "--challenge-sha256", a.challenge_sha256,
                "--comparator-sha256", a.comparator_sha256, "--keep-work",   # the caller's pin
                "--overlap-targets", "none", "--unsafe", a.items]
        print("fvwork init: cold run:", " ".join(argv), flush=True)
        t0 = now()
        rc = subprocess.run(argv).returncode
        print(f"fvwork init: cold run exit {rc} after {now() - t0:.1f} s", flush=True)
    res = jload(os.path.join(out, "result.json"), {})
    try:
        uns = res["build"]["attempts"][0]["stage"]["unsafe"]
    except (KeyError, IndexError, TypeError):
        uns = []
    if "merge" in uns:
        sys.exit("fvwork init: the base run used `merge` (merged trees have no per-module outputs): re-run without it")
    proj = os.path.join(out, "work", "proj")
    plan = os.path.join(out, "log", "build-fast", "plan.jsonl")
    targets = os.path.join(out, "log", "export-targets.txt")
    no_plan = not (os.path.isdir(proj) and os.path.isfile(plan) and os.path.isfile(targets))
    if no_plan:
        # the fast build declined (official build: a root lakefile.lean, lean_lib globs, any other hand-off),
        # so there is no B3 build tree / plan. The v0.1 cold path (serve without --experimental-incremental) never uses
        # them - every request is a fresh bin/fastverify --preset sound run; --files requests use the clean snapshot src0 -
        # so the state is written with a cold base (as a cold-path advance writes it; serve --experimental-incremental
        # refuses such a base, exit 2). Fail closed: only a cold run that reached a sound verdict (ACCEPTED / REJECTED,
        # exit = verdict) makes a state; anything else is refused as before (no config.json).
        v = res.get("verdict")
        if v not in ("ACCEPTED", "REJECTED") or (rc is not None and VERDICT.get(rc) != v):
            sys.exit(f"fvwork init: {out} has no kept build tree / plan / targets and the cold run gave no sound verdict "
                     f"(exit {rc}, verdict {v!r}): no state")
        try:
            why = " / ".join(str(x["stage"].get("detail"))[:160] for x in res["build"]["attempts"]
                             if (x.get("stage") or {}).get("status") == "DECLINED")
        except (KeyError, TypeError, AttributeError):
            why = ""
        print(f"fvwork init: the base run has no B3 build tree / plan ({why or 'no fast build'}): state for the cold "
              "sound path only (serve --experimental-incremental refuses it)", flush=True)
    xa = []   # build transforms of rebuilt modules = the base run's (as tools/incr/incr-reverify.sh derives them)
    ktc_exempt = "skip-kernel-tc=except-translate" in uns   # sound-auto / the sound preset's per-module gate
    if not uns or "skip-kernel-tc" in uns or ktc_exempt:
        if not a.no_skip_kernel_tc:
            xa.append("-Ddebug.skipKernelTC=true")
    if not uns or "linter-off" in uns:
        xa.append("-Dlinter.all=false")
    lean = None   # the lean the base build actually ran (the T1 toolchain it chose), from the scheduler's start record
    try:
        with open(os.path.join(out, "log", "build-fast", "sched.out")) as f:
            for ln in f:
                if ln.startswith('{"event": "start"'):
                    s = json.loads(ln)
                    lean = s.get("lean_override") or s.get("lean")
                    break
    except (OSError, ValueError):
        pass
    if lean and (not os.access(lean, os.X_OK) or os.path.realpath(lean).startswith(os.path.realpath(tc) + "/")):
        lean = None   # the official toolchain's own lean: incr-build's default
    plug = os.path.join(out, "log", "build-fast", "fastexact", "libLightFastExact.so")
    stf = os.path.join(out, "log", "build-fast", "fastexact", "STATUS")
    plugin = plug if os.path.isfile(plug) and os.path.isfile(stf) and open(stf).read().startswith("active") else None
    planner = os.path.join(out, "log", "build-fast", "planner", "planner")
    planner = planner if os.access(planner, os.X_OK) else None
    # the export targets of THIS state's comparator config (as bin/fastverify / the 4.36 Lake compareIt derive them), not
    # the cold run's list: a state may judge a subset of the cold run's theorems (a smaller challenge config)
    with open(os.path.join(st, "targets.txt"), "w") as f:
        r = subprocess.run([PY, "-I", os.path.join(fv, "tools", "ci", "mktargets.py"), os.path.join(chd, "comparator.json")],
                           stdout=f, text=True)
    if r.returncode != 0:
        sys.exit("fvwork init: cannot derive the export targets (tools/ci/mktargets.py)")
    if os.path.isfile(targets) and \
            sorted(open(targets).read().split()) == sorted(open(os.path.join(st, "targets.txt")).read().split()):
        shutil.copyfile(targets, os.path.join(st, "targets.txt"))   # same set: keep the cold run's order (same export bytes)
    exp = os.path.join(out, "solution.export")
    exp = os.path.realpath(exp) if os.path.exists(exp) else None
    cfg = {"fv": fv, "project": os.path.realpath(a.project), "challenge_src": ch, "challenge_sha256": a.challenge_sha256,
           "solution_module": cm, "tc": tc, "packages": ws, "threads": threads, "unsafe": uns, "extra_args": xa,
           "ktc_exempt_translate": bool(ktc_exempt and not a.no_skip_kernel_tc),
           "lean": lean, "plugin": plugin, "planner": planner,
           "import_arts_empty": "sound-fast-path=importarts-empty" in uns, "closure_only": bool(a.closure_only),
           "created": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    cfg["build"] = "fast"
    cfg["release"] = rel
    cfg["comparator_sha256"] = a.comparator_sha256   # the CALLER's pin (= the copied config's sha256)
    cfg["comparator_pin_from_caller"] = True   # serve refuses a state whose pin was not given by the caller
    if no_plan:   # informational: the base below is a cold base
        cfg["base_build"] = "official (no B3 plan): cold sound path only"
    jdump(os.path.join(st, "config.json"), cfg)
    base = {"run": "cold", "proj": proj, "plan": plan, "export": exp, "src": proj, "src0": os.path.join(st, "src0"),
            "export_sha256": (res.get("export") or {}).get("sha256"), "verdict": res.get("verdict"),
            "export_of": proj if exp else None,   # the tree this export is the export of (see Service._verify)
            "t": now()}
    if no_plan:   # a cold base: no build tree, plan or export of a build tree; the clean snapshot only
        base.update({"proj": None, "plan": None, "export": None, "export_of": None, "src": base["src0"], "cold": True,
                     "init_no_plan": True})

    os.makedirs(os.path.join(st, "runs"), exist_ok=True)
    jdump(os.path.join(st, "base.json"), base)
    print(json.dumps({"state": st, "base_verdict": base["verdict"], "export": base["export"], "unsafe": uns,
                      "cold_only": no_plan}))


def init_lake(a, st, fv, ch, chd, cm, tc, ws, threads, rel):
    """--build lake: the OFFICIAL incremental build of any supported release (the release's `lake build <solution module>`
    in build/official-build.sh's sandbox on a persistent tree, Lake's own traces decide what is rebuilt) + the release's
    official exporter (tools/ci/official-incr.sh --no-check); the trusted check is the same as in fast mode."""
    tg = os.path.join(st, "targets.txt")
    with open(tg, "w") as f:
        r = subprocess.run([PY, "-I", os.path.join(fv, "tools", "ci", "mktargets.py"), os.path.join(chd, "comparator.json")],
                           stdout=f, text=True)
    if r.returncode != 0:
        sys.exit("fvwork init: cannot derive the export targets")
    out = os.path.join(st, "runs", "00000")
    os.makedirs(out)
    src = os.path.join(out, "src")
    r = subprocess.run(["rsync", "-a", "--exclude=/.lake", "--exclude=.git", os.path.realpath(a.project) + "/", src + "/"])
    print("fvwork init: cold official lake build + export (tools/ci/official-incr.sh)", flush=True)
    t0 = now()
    rc = subprocess.run([os.path.join(fv, "tools", "ci", "official-incr.sh"), os.path.join(st, "lake"), src, chd,
                         os.path.join(out, "a1-lake"), "--targets", tg, "--packages", ws, "--fv", fv, "--solution-only",
                         "--no-check"], env=dict(os.environ, FASTVERIFY=fv), capture_output=True, text=True).returncode
    summ = jload(os.path.join(out, "a1-lake", "summary.json"), {})
    print(f"fvwork init: cold lake build exit {summ.get('build_exit')}, export exit {summ.get('export_exit')} after "
          f"{now() - t0:.1f} s", flush=True)
    exp = os.path.join(out, "a1-lake", "solution.export")
    if summ.get("export_exit") != 0 or not os.path.isfile(exp):
        sys.exit(f"fvwork init: the cold official build/export failed (rc {rc}): see {out}/a1-lake/build.log")
    cfg = {"fv": fv, "project": os.path.realpath(a.project), "challenge_src": ch, "challenge_sha256": a.challenge_sha256,
           "solution_module": cm, "tc": tc, "packages": ws, "threads": threads, "build": "lake", "release": rel,
           "created": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    jdump(os.path.join(st, "config.json"), cfg)
    base = {"run": "00000", "proj": None, "plan": None, "src": src, "export": exp, "export_sha256": sha256_file(exp),
            "export_of": src, "verdict": None, "t": now()}
    jdump(os.path.join(st, "base.json"), base)
    print(json.dumps({"state": st, "build": "lake", "release": rel, "export": exp, "cold_s": round(now() - t0, 1)}))


# --------------------------------------------------------------------------------------------------------- warm pool
class Warm:
    """One pre-warmed `pleanchecker_incr --incremental=DIR` server (full mode) that was given the base export as an
    UNTRUSTED snapshot. The trusted check attaches to it with --incr-dir DIR (one final per server process)."""

    def __init__(self, d, plc, threads, snap, nice):
        self.d, self.snap = d, snap
        self.t0 = now()
        self.ready_t = None
        self.dead = False
        os.makedirs(d, exist_ok=True)
        env = dict(os.environ, INCR_NICE=str(nice))
        self.p = subprocess.Popen([os.path.join(SVC.fv, "overlap", "incr-server.sh"), d, plc, str(threads)],
                                  env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
        self.fd = None
        # the server opens its FIFO for reading after start-up; a non-blocking open fails with ENXIO until then (a blocking
        # open would hang the daemon forever if the server died first)
        t_end = now() + 60
        while self.fd is None and now() < t_end and self.p.poll() is None:
            try:
                self.fd = os.open(os.path.join(d, "cmd"), os.O_WRONLY | os.O_NONBLOCK)
            except OSError:
                time.sleep(0.05)
        if self.fd is None:
            self.dead = True
            return
        try:   # keep the write end open (the server reads lines; EOF would end its command loop)
            os.set_blocking(self.fd, True)
            os.write(self.fd, f"snap {snap}\n".encode())
        except OSError:
            self.dead = True

    def ready(self):
        if self.ready_t:
            return True
        if self.p.poll() is not None:
            self.dead = True
            return False
        try:
            with open(os.path.join(self.d, "server.log"), errors="replace") as f:
                log = f.read()
        except OSError:
            return False
        if "snapshot 1 ingested" in log or "snapshot dropped" in log:
            self.ready_t = now()
            return True
        return False

    def stop(self):
        try:
            if self.fd is not None:
                os.close(self.fd)
        except OSError:
            pass
        self.fd = None
        try:
            os.killpg(self.p.pid, signal.SIGTERM)
        except OSError:
            pass
        try:
            self.p.wait(timeout=10)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(self.p.pid, signal.SIGKILL)
            except OSError:
                pass


class WarmCheck:
    """--check warm: the persistent warm sound check (fastverify/check/warm/fvcheckd.py, a TRUSTED component)
    as a sidecar, preloaded with the pinned challenge export and the daemon's base export (which fvcheckd verifies from
    scratch with both kernels at start-up). A request's full export is judged with check_full; ACCEPTED / REJECTED from it
    are the verdict; anything else (FALLBACK_REQUIRED, DECLINED, no answer) falls back to the unchanged check script."""

    def __init__(self, svc, base_export):
        self.svc, self.base = svc, base_export
        self.d = os.path.join(svc.st, "warmd")
        shutil.rmtree(self.d, ignore_errors=True)
        os.makedirs(self.d, mode=0o700)
        self.script = os.path.join(svc.fv, "check", "warm", "fvcheckd.py")
        self.log = open(os.path.join(svc.st, "warmd.log"), "a")
        wp = svc.warm_pins()
        self.p = subprocess.Popen([PY, "-I", self.script, "serve", "--state", self.d, "--challenge", svc.chx,
                                   "--challenge-sha256", svc.cfg["challenge_sha256"], "--config", svc.cfgp,
                                   "--config-sha256", sha256_file(svc.cfgp), "--base", base_export,
                                   "--threads", str(svc.threads)] + (["--pins", wp] if wp else []),
                                  stdout=self.log, stderr=subprocess.STDOUT,
                                  start_new_session=True)
        self.ready = False
        self.t0 = now()

    def is_ready(self):
        if not self.ready and self.p.poll() is None and os.path.exists(os.path.join(self.d, "ready.json")):
            self.ready = True
            self.svc.log(event="warmd-ready", startup_s=round(now() - self.t0, 1))
        return self.ready and self.p.poll() is None

    def check(self, xo, timeout):
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(timeout)
        try:
            s.connect(os.path.join(self.d, "sock"))
            s.sendall((json.dumps({"op": "check_full", "export": xo, "config": self.svc.cfgp, "timeout": timeout})
                       + "\n").encode())
            f = s.makefile("r")
            return json.loads(f.readline())
        finally:
            s.close()

    def check_delta(self, delta, timeout):
        """the warm check's delta query: E_eff = (base \\ dirty) + delta, the base being the export this sidecar verified at start"""
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(timeout)
        try:
            s.connect(os.path.join(self.d, "sock"))
            s.sendall((json.dumps({"op": "check_delta", "delta": delta, "config": self.svc.cfgp, "timeout": timeout})
                       + "\n").encode())
            f = s.makefile("r")
            return json.loads(f.readline())
        finally:
            s.close()

    def stop(self):
        try:
            os.killpg(self.p.pid, signal.SIGTERM)
            self.p.wait(timeout=20)
        except (OSError, subprocess.TimeoutExpired):
            try:
                os.killpg(self.p.pid, signal.SIGKILL)
            except OSError:
                pass


# ----------------------------------------------------------------------------------------------------------- service
class Service:
    def __init__(self, a):
        self.st = os.path.realpath(a.state)
        self.cfg = jload(os.path.join(self.st, "config.json"))
        if not self.cfg:
            sys.exit(f"fvwork: {self.st} is not initialized (fvwork.py init)")
        self.fv = self.cfg["fv"]
        self.threads = a.threads or self.cfg["threads"]
        self.jobs = a.jobs
        # threads of ONE request's build / export / check (concurrent requests share the daemon's CPU budget)
        self.jthreads = a.job_threads or max(2, self.threads // max(1, self.jobs))
        self.check_kind = a.check
        # without --experimental-incremental every request takes the COLD sound path
        # (bin/fastverify --preset sound on exactly the submitted tree: fresh build, export, check; nothing reused); the
        # incremental machinery (incremental builds, --mode, --check frontier / warm, --build lake, --copy-mode, the memo)
        # is EXPERIMENTAL and its ACCEPTED / CONDITIONAL is never counted (NO-VERDICT, "provisional")
        self.incremental = bool(getattr(a, "experimental_incremental", False))
        if not self.incremental and a.check == "sound" and self.cfg.get("build") != "lake" and \
                not (self.cfg.get("comparator_sha256") and self.cfg.get("comparator_pin_from_caller")):
            # the cold path forwards the comparator pin recorded at init; an older state has none
            print("fvwork serve: this state records no comparator pin given by the caller (initialized by an older version; "
                  "--comparator-sha256 is required with --challenge-sha256): re-initialize it with fvwork "
                  "init ... --challenge-sha256 HEX --comparator-sha256 HEX", file=sys.stderr)
            sys.exit(2)
        b0 = jload(os.path.join(self.st, "base.json"), {}) or {}
        if self.incremental and b0.get("cold") and self.cfg.get("build") != "lake":
            print("fvwork serve: " + ("this state's base run had no B3 build tree / plan (official build at "
                                      "init)" if b0.get("init_no_plan") else
                                      "the base of this state was advanced by the cold path (no build tree)") +
                  ": the EXPERIMENTAL incremental machinery needs a state of its own (fvwork init)", file=sys.stderr)
            sys.exit(2)
        if not self.incremental:
            why = ("--check " + a.check) if a.check != "sound" else ("--build lake (incremental official builds)"
                                                                      if self.cfg.get("build") == "lake" else None)
            if why:
                print(f"fvwork serve: {why} uses the EXPERIMENTAL incremental machinery (not part of the default sound path); "
                      "add --experimental-incremental to run it (its ACCEPTED is never counted), or use the default "
                      "cold sound path (--check sound)", file=sys.stderr)
                sys.exit(2)
        self.check_script = os.path.join(self.fv, "check", "frontier", "check-frontier.sh") if a.check == "frontier" \
            else os.path.join(self.fv, "check", "sound", "check-sound-svc.sh")
        self.warmd = None
        if a.check == "warm" and a.copy_mode == "hardlink":   # the warm delta check trusts the
            # STORED base: with hard-linked request trees an untrusted elaboration rewrites base files in place
            sys.exit("fvwork serve: --check warm cannot be combined with --copy-mode hardlink (request code could rewrite the "
                     "stored base the warm delta check trusts); use reflink or farm")
        if a.check == "warm":   # fail closed: the served base tree and the warm daemon's base export can diverge after an advance
            sys.exit("fvwork serve: --check warm is not available in this release (the served base tree and the warm "
                     "daemon's base export can diverge after an advance, so a later request can be judged against a stale base); "
                     "use --check sound")
        if a.check == "warm" and not os.path.isfile(os.path.join(self.fv, "check", "warm", "fvcheckd.py")):
            sys.exit("fvwork serve: --check warm needs the published fastverify/check/warm/fvcheckd.py")
        if not os.access(self.check_script, os.X_OK):
            sys.exit(f"fvwork serve: check script {self.check_script} missing")
        self.allowed, self.allowed_sha = None, "-"
        if a.allowed:   # private immutable copy: the caller's file may change while the daemon serves
            ash = sha256_file(a.allowed)
            self.allowed = os.path.join(self.st, "challenge", "allowed.%s.txt" % ash[:16])
            if not os.path.exists(self.allowed):
                shutil.copyfile(a.allowed, self.allowed + ".tmp")
                os.chmod(self.allowed + ".tmp", 0o400)
                os.replace(self.allowed + ".tmp", self.allowed)
            if sha256_file(self.allowed) != ash:
                sys.exit("fvwork serve: the private copy of --allowed does not match")
            self.allowed_sha = ash
        gpath = os.path.join(self.fv, "tools", "guard", "fvguard.py")
        # default: a one-hour wall limit on every untrusted build / export (an endless elaboration would hold a
        # --jobs slot forever); --guard none disables, --guard SPEC replaces it
        self.guard = None if a.guard == "none" else (a.guard or ("wall=3600" if os.path.isfile(gpath) else None))
        if self.guard and not os.path.isfile(gpath):
            sys.exit("fvwork serve: --guard needs tools/guard/fvguard.py")
        self.pinned = os.path.realpath(a.pinned) if a.pinned else None   # tools/frontier/frontier.py pin output
        if self.pinned and not os.path.isfile(os.path.join(self.pinned, "frontier.json")):
            sys.exit("fvwork serve: --pinned DIR needs a frontier pin (tools/frontier/frontier.py pin ... DIR)")
        self.expdiff = a.expdiff if a.expdiff and os.access(a.expdiff, os.X_OK) else None
        xh = os.path.join(self.fv, "tools", "dupfind", "bin", "exphash")
        self.exphash = xh if os.access(xh, os.X_OK) else None   # delta drift (statement hashes; untrusted info)
        self.hash_lock, self.hash_cache = threading.Lock(), {}
        self.drift_default = a.drift
        self.acache = os.path.join(self.st, "acache")   # check-frontier.sh --a-cache: private like the state dir
        if a.check == "frontier":
            os.makedirs(self.acache, mode=0o700, exist_ok=True)
            os.chmod(self.acache, 0o700)
        self.delta_max = 5000   # --check warm delta path: largest importer cone exported as a delta (else full export)
        self.warm_full_max = int(getattr(a, "warm_full_max", 4.0) * 1e9)   # largest export sent to the warm check whole
        self.delta_only = bool(getattr(a, "delta_only", False))   # --check warm: no full-export fallback (screening)
        self.manifest_lock = threading.Lock()
        self.pins = os.path.realpath(a.pins) if a.pins else None   # another release's trusted-check pins
        if self.pins:   # Boundary B4: a pins*.env of THIS package's check/sound/, as bin/fastverify --pins
            pd = os.path.realpath(os.path.join(self.fv, "check", "sound"))
            if os.path.dirname(self.pins) != pd and not os.path.isabs(a.pins):   # relative: also from the package root
                self.pins = os.path.realpath(os.path.join(self.fv, a.pins))
            if os.path.dirname(self.pins) != pd or not os.path.basename(self.pins).startswith("pins") \
                    or not self.pins.endswith(".env"):
                sys.exit(f"fvwork serve: --pins {a.pins}: must name a pins*.env file in {pd} (Boundary B4)")
        if self.pins and not os.path.isfile(self.pins):
            sys.exit(f"fvwork serve: --pins {a.pins}: no such file")
        if self.pins and a.check == "warm" and not self.warm_pins():
            sys.exit("fvwork serve: --pins (another release's trusted check) and --check warm: the warm check has no "
                     "pins for this release (check/warm/pins-<release>.env)")
        self.nwarm = 0 if self.pins else a.warm   # the pre-warmed legs are 4.36 pleanchecker_incr servers
        if not self.incremental:   # the cold path judges with bin/fastverify's own check (no pre-warmed legs)
            self.nwarm = 0
        self.mode = a.mode
        self.warm_nice = a.warm_nice
        self.keep_runs = a.keep_runs
        self.lock = threading.RLock()
        self.sem = threading.Semaphore(self.jobs)
        self.build_lock = threading.Lock()
        self.copy_mode = a.copy_mode
        self.refill_now = threading.Event()
        self.slow_lane = a.slow_lane
        self.merge_lock = threading.Lock()
        self.inuse = {}         # base run -> number of running requests that started from it (never garbage-collected)
        self.children = set()   # in-flight child processes of requests (own sessions; terminated on stop)
        self.base = jload(os.path.join(self.st, "base.json"))
        self.chx = os.path.join(self.st, "challenge", "challenge.export")
        ltc = os.path.join(self.st, "challenge", "lean-toolchain")
        if not self.incremental and not os.path.isfile(ltc):   # bin/fastverify needs the challenge's toolchain
            srcl = os.path.join(self.cfg.get("challenge_src") or "", "lean-toolchain")
            try:
                if os.path.isfile(srcl):
                    shutil.copyfile(srcl, ltc)
                elif self.cfg.get("release"):
                    open(ltc, "w").write("leanprover/lean4:v%s\n" % self.cfg["release"])
            except OSError:
                pass
        self.cfgp = os.path.join(self.st, "challenge", "comparator.json")
        self.pool = []          # Warm servers
        self.warm_seq = 0
        self.req_seq = len(os.listdir(os.path.join(self.st, "runs")))
        self.stats = {"requests": 0, "accepted": 0, "rejected": 0, "conditional": 0, "no_verdict": 0, "warm_used": 0,
                      "started": now()}
        self.stopping = False
        self.plc = None
        for ln in open(os.path.join(self.fv, "check", "sound", "pins.env")):
            p = ln.split()
            if len(p) >= 4 and p[0] == "PIN" and p[1] == "pleanchecker_incr":
                self.plc = p[3]
        self.reuse = a.reuse_identical and self.incremental   # the cold path never consults the memo
        self.cfg_sha = sha256_file(self.cfgp)
        # everything of the trusted check whose change must invalidate a memoized verdict (re-hashed per request)
        self.trust_files = [self.check_script, self.cfgp] + [os.path.join(self.fv, *x) for x in (
            ("check", "sound", "pins.env"), ("check", "sound", "check-sound.sh"), ("check", "sound", "check-sound-svc.sh"),
            ("config", "components.json"), ("toolchains", "leanprover--lean4---v4.36.0.json"))]
        if getattr(self, "pins", None):
            self.trust_files.append(self.pins)
        self.hide = None if getattr(a, "no_hide", False) else self.hide_file()
        if self.hide:
            self.trust_files.append(self.hide)
        if self.check_kind == "frontier":
            self.trust_files += [os.path.join(self.fv, *x) for x in (("check", "frontier", "pins.env"),
                                                                   ("tools", "frontier", "frontier.py"))]
        if self.check_kind == "frontier" and a.pinned:   # the pinned frontier challenge decides the open statements
            self.trust_files += [os.path.join(os.path.realpath(a.pinned), f) for f in ("frontier.json", "challenge.export")]
        if self.check_kind == "warm":   # every file of the trusted warm check (scripts, pins, provenance)
            wd = os.path.join(self.fv, "check", "warm")
            self.trust_files += sorted(os.path.join(wd, f) for f in os.listdir(wd) if os.path.isfile(os.path.join(wd, f)))
        # the explicit list above missed files the check scripts read themselves (check/xversion/
        # xvcheck.py, releases.json, lib/toolchain.py, other releases' manifests, ...): trust_digest() now also covers EVERY
        # file under check/, config/, lib/ and toolchains/ (verdict_files), so a gate change never re-reports an older
        # verdict; hashed once in the background at start (check/notary alone is ~1 GB); later digests only stat the files
        self.vsha = StatSha()
        self.vprewarm = threading.Thread(target=(lambda: [self.vsha(f) for f in verdict_files(self.fv)]) if self.incremental
                                         else (lambda: None), daemon=True)
        self.vprewarm.start()
        self.memo = {}
        vj = os.path.join(self.st, "verdicts.jsonl")
        if self.reuse:   # the memo is only trusted from a private, non-symlinked log of this user
            stt = os.lstat(self.st)
            if stt.st_uid != os.getuid() or (stt.st_mode & 0o077) or os.path.islink(self.st):
                sys.exit(f"fvwork serve: --reuse-identical needs a private state dir (owner {os.getuid()}, mode 0700)")
            if os.path.lexists(vj) and (os.path.islink(vj) or os.lstat(vj).st_uid != os.getuid()):
                sys.exit("fvwork serve: verdicts.jsonl is not a regular file of this user")
        for ln in open(vj) if self.reuse and os.path.isfile(vj) else []:
            try:
                r = json.loads(ln)
                if r.get("exit") in (0, 1, 3) and r.get("verdict") == VERDICT[r["exit"]] and isinstance(r.get("key"), str):
                    self.memo[r["key"]] = r
            except (ValueError, KeyError, TypeError):
                pass
        self.icache = os.path.join(self.st, "icache")
        os.makedirs(self.icache, exist_ok=True)
        os.chmod(self.icache, 0o700)

    def guarded(self, argv, tag, work):
        """--guard SPEC: run an UNTRUSTED step (build / export) under tools/guard/fvguard.py (whole-tree memory,
        processes, wall clock, CPU, output limits; a violation kills the tree and exits 125 -> NO-VERDICT here, never a
        verdict). The trusted check is not wrapped."""
        if not self.guard:
            return argv
        g = [PY, "-I", os.path.join(self.fv, "tools", "guard", "fvguard.py")]
        for item in self.guard.split(","):
            k, _, v = item.partition("=")
            if k.strip():
                g += ["--" + k.strip(), v.strip()]
        return g + ["--json", work + f".{tag}.guard.json", "--"] + argv

    def run(self, argv, timeout=None, **kw):
        """subprocess.run replacement for request work: the child gets its own session (process group) and is registered,
        so `stop` (and SIGTERM) terminate every in-flight build / export / check instead of orphaning them"""
        if self.stopping:
            raise OSError("daemon is stopping")
        cap = kw.pop("capture_output", False)
        if cap:
            kw.setdefault("stdout", subprocess.PIPE); kw.setdefault("stderr", subprocess.PIPE)
        p = subprocess.Popen(argv, start_new_session=True, **kw)
        with self.lock:
            self.children.add(p)
        try:
            out, err = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            self.killpg(p)
            out, err = p.communicate()
        finally:
            with self.lock:
                self.children.discard(p)
        return subprocess.CompletedProcess(argv, p.returncode, out, err)

    @staticmethod
    def killpg(p, grace=5.0):
        try:
            os.killpg(p.pid, signal.SIGTERM)
        except OSError:
            return
        try:
            p.wait(timeout=grace)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except OSError:
                pass

    def log(self, **k):
        k["t"] = round(now(), 3)
        with self.lock:
            with open(os.path.join(self.st, "events.jsonl"), "a") as f:
                f.write(json.dumps(k) + "\n")

    # ---- warm pool
    def refill(self):
        """keep self.nwarm servers fed with the CURRENT base export (stale ones are replaced in the background)"""
        if not self.plc or not self.nwarm:
            return
        with self.lock:
            snap = self.base.get("export")
            if not snap or not os.path.isfile(snap):
                return
            live = []
            for w in self.pool:
                w.ready()   # updates w.dead
                if w.dead:
                    try:
                        tail = open(os.path.join(w.d, "server.log"), errors="replace").read()[-600:]
                    except OSError:
                        tail = None
                    w.stop(); shutil.rmtree(w.d, ignore_errors=True)
                    self.log(event="warm-dead", dir=w.d, rc=w.p.returncode, log_tail=tail)
                else:
                    live.append(w)
            fresh = [w for w in live if w.snap == snap]
            stale = [w for w in live if w.snap != snap]
            # a stale server (fed with an older base export) is still useful - only what differs is replayed - so it is
            # retired only once a fresh one is READY; warming servers are never killed because the base moved on
            if any(w.ready_t for w in fresh):
                for w in stale:
                    w.stop(); shutil.rmtree(w.d, ignore_errors=True)
                    self.log(event="warm-retire", dir=w.d)
                stale = []
            while len(fresh) < self.nwarm:
                self.warm_seq += 1
                d = os.path.join(self.st, "warm", "w%04d" % self.warm_seq)
                fresh.append(Warm(d, self.plc, self.jthreads, snap, self.warm_nice))
                self.log(event="warm-start", dir=d, snap=snap)
            self.pool = fresh + stale

    def take_warm(self):
        with self.lock:
            best = None
            for w in self.pool:
                if w.ready() and not w.dead:
                    if best is None or (w.snap == self.base.get("export") and best.snap != w.snap):
                        best = w
            if best:
                self.pool.remove(best)
        if best:   # start the replacement at once (fed with the current base): back-to-back requests stay warm.
            # It must be spawned by the long-lived warm_loop thread: incr-server.sh execs `bwrap --die-with-parent`,
            # whose PR_SET_PDEATHSIG fires when the spawning THREAD exits - a server started from a short-lived thread
            # was SIGKILLed at once (the 'warm-dead rc -9' events)
            self.refill_now.set()
        return best

    def warm_loop(self):
        """the ONLY thread that starts warm servers (see take_warm: PDEATHSIG is per thread)"""
        while not self.stopping:
            try:
                self.refill()
            except Exception as e:  # noqa: BLE001 - the pool is an optimization; never fatal
                self.log(event="warm-error", error=repr(e)[:300])
            self.refill_now.wait(1.0)
            self.refill_now.clear()

    # ---- request handling
    def materialize(self, req, rdir, base=None):
        """sources of the requested state -> rdir/src (no .git/.lake); returns a description"""
        src = os.path.join(rdir, "src")
        if "tree" in req:
            if not isinstance(req["tree"], str) or not req["tree"] or not os.path.isabs(req["tree"]):   # never '' / cwd
                raise ValueError("tree must be an absolute path")
            tree = os.path.realpath(req["tree"])
            if tree == "/":   # never stage /
                raise ValueError("tree must not be /")
            if not os.path.isdir(tree):
                raise ValueError(f"tree {tree} is not a directory")
            # the cold path judges byte-for-byte the tree a direct bin/fastverify run judges: only
            # its own exclusion (the top-level .lake); the experimental path keeps its older list
            exc = ["--exclude=/.lake", "--exclude=.git", "--exclude=/.fvwork"] if self.incremental else ["--exclude=/.lake"]
            r = self.run(["rsync", "-a", "--delete"] + exc + [tree + "/", src + "/"], capture_output=True, text=True)
            if r.returncode != 0:
                raise ValueError("rsync: " + r.stderr.strip()[:300])
            return {"kind": "tree", "path": tree}
        if "git" in req:
            if not isinstance(req["git"], str) or not req["git"] or not os.path.isabs(req["git"]):   # never '' / cwd
                raise ValueError("git must be an absolute path")
            repo, rev = os.path.realpath(req["git"]), req.get("rev", "HEAD")
            if repo == "/":
                raise ValueError("git must not be /")
            if not re.fullmatch(r"[0-9A-Za-z._/@^~-]{1,200}", rev) or rev.startswith("-"):
                raise ValueError("bad rev")   # no option injection into `git archive` (e.g. '-o<file>')
            os.makedirs(src)
            # git (repository config: filters, fsmonitor) and tar run in a sandbox: read-only /, no network, only the
            # fresh source directory writable - a hostile repository or archive can write nowhere else
            sb = ["env", "-i", "/usr/bin/bwrap", "--ro-bind", "/", "/", "--tmpfs", "/tmp",
                  "--ro-bind", repo, repo,   # a repository under /tmp stays visible (read-only) over the tmpfs
                  "--dev", "/dev", "--proc", "/proc", "--bind", src, src, "--unshare-all", "--die-with-parent", "--new-session",
                  "--setenv", "PATH", "/usr/bin:/bin", "--setenv", "HOME", "/tmp", "--"]
            # pipefail: a failing `git archive` (e.g. a blob missing from a partial clone - no network in the sandbox)
            # must not leave a silently truncated tree that tar extracted without error
            if self.incremental:
                script = ('set -o pipefail; git -c core.fsmonitor=false -c safe.directory="$1" '
                          '-C "$1" archive --format=tar "$2" | tar -x --no-same-owner -C "$3"')
            else:   # a plain checkout of the commit into src (a private index under /tmp; the
                # repository is read-only), so the tree equals the commit (git archive honours export-ignore / export-subst)
                script = ('set -e; export GIT_INDEX_FILE=/tmp/fvwork-index; G="git -c core.fsmonitor=false -c safe.directory=$1"; '
                          '$G -C "$1" --work-tree="$3" read-tree "$2"; $G -C "$1" --work-tree="$3" checkout-index -a -f')
            r = self.run(sb + ["/bin/bash", "-c", script, "sh", repo, rev, src], capture_output=True, text=True, timeout=600)
            if r.returncode != 0 or not os.listdir(src):
                hint = ""
                if any(k in r.stderr for k in ("promisor", "missing", "fetch", "cannot read")):
                    hint = " (partial/blobless clone? the sandbox has no network: use a full clone or --files)"
                raise ValueError(f"git archive {rev} failed: {r.stderr.strip()[:200]}{hint}")
            return {"kind": "git", "repo": repo, "rev": rev}
        if "files" in req:   # changed files over the BASE sources: {"rel/path.lean": "content" | null (delete)}
            # fast mode: SPARSE - src holds only the written files and S/runs/N/changed.json lists the exact change set,
            # so incr-build syncs just those paths (no whole-tree walk: ~1 min on a 149k-file repository); it re-checks
            # path confinement against the copied project tree. Lake mode syncs whole trees: full copy of the base sources.
            sparse = self.cfg.get("build") != "lake" and self.incremental   # the cold path needs the whole tree
            if sparse:
                os.makedirs(src, exist_ok=True)
            else:
                bse = base if base is not None else self.base   # the request's captured base
                base_proj = bse.get("src") or bse["proj"]
                if not self.incremental:   # only a CLEAN source snapshot, never a build tree
                    base_proj = bse.get("src0")
                    if not base_proj or not os.path.isdir(base_proj):
                        raise ValueError("this state has no clean source snapshot of its base (initialized by an older "
                                         "version): re-init it, or send the whole tree (--tree / --git)")
                r = self.run(["rsync", "-a", "--exclude=/.lake", base_proj + "/", src + "/"], capture_output=True)
                if r.returncode != 0:
                    raise ValueError("cannot copy the base sources")
            rsrc = os.path.realpath(src)
            writes, deletes = [], []
            if not isinstance(req["files"], dict) or len(req["files"]) > 10000:
                raise ValueError("files must be an object {relative path: content | null}")
            for rel, content in req["files"].items():
                if not isinstance(rel, str) or not (content is None or isinstance(content, str)) or "\0" in rel \
                        or os.path.isabs(rel):
                    raise ValueError(f"bad entry {rel!r}")
                q = os.path.normpath(os.path.join(src, rel))
                if not q.startswith(src + "/") or "/.lake/" in q + "/" or q.endswith("/.lake") or "/.git/" in q + "/":
                    raise ValueError(f"bad path {rel}")
                # no writes through symlinks (a symlinked directory in the project could point anywhere)
                par = os.path.dirname(q)
                while not os.path.exists(par):
                    par = os.path.dirname(par)
                if not (os.path.realpath(par) + "/").startswith(rsrc + "/") or os.path.islink(q):
                    raise ValueError(f"bad path {rel} (symlink)")
                if content is None:
                    deletes.append(os.path.relpath(q, src))
                    if os.path.exists(q):
                        os.unlink(q)
                else:
                    writes.append(os.path.relpath(q, src))
                    os.makedirs(os.path.dirname(q), exist_ok=True)
                    with open(q, "w", encoding="utf-8") as f:
                        f.write(content)
            if sparse:
                jdump(os.path.join(rdir, "changed.json"), {"write": writes, "delete": deletes})
            return {"kind": "files", "n": len(req["files"]), "sparse": sparse}
        raise ValueError("request needs tree, git or files")

    def build(self, base, src, work, mode):
        c = self.cfg
        argv = [PY, "-I", os.path.join(self.fv, "tools", "incr", "incr-build.py"), "--base", base["proj"],
                "--base-plan", base["plan"], "--src", src, "--work", work, "--packages", c["packages"], "--tc", c["tc"],
                "--threads", str(self.jthreads), "--json", work + ".build.json"]
        chg = os.path.join(os.path.dirname(src), "changed.json")   # sparse --files request (materialize)
        if os.path.isfile(chg):
            argv += ["--changed", chg]
        for x in c["extra_args"]:
            argv.append("--extra-arg=" + x)
        if c.get("ktc_exempt_translate"):
            argv.append("--ktc-exempt-translate")
        if c.get("lean"):
            argv += ["--lean", c["lean"]]
        if c.get("plugin"):
            argv += ["--plugin", c["plugin"]]
        if c.get("planner"):
            argv += ["--planner", c["planner"]]
        if c.get("import_arts_empty"):
            argv.append("--import-arts-empty")
        if c.get("closure_only"):
            argv += ["--closure-of", c["solution_module"]]
        argv.append("--reuse-plan")
        if self.copy_mode == "hardlink":
            argv.append("--hardlink")
        elif self.copy_mode == "farm" and os.path.isfile(chg) and os.path.isfile(os.path.join(os.path.dirname(src), "farm")):
            argv.append("--farm")   # a sparse CANDIDATE: symlink farm over the (fixed) base instead of a tree copy
        if mode == "optimistic":
            argv.append("--optimistic")
        elif mode == "interface":
            argv.append("--interface")
        env = dict(os.environ, FASTVERIFY=self.fv)
        t0 = now()
        r = self.run(self.guarded(argv, "build", work), capture_output=True, text=True, env=env)
        b = jload(work + ".build.json", {}) or {}
        if r.returncode == 125 and self.guard:
            g = jload(work + ".build.guard.json", {}) or {}
            b.update({"exit": 2, "guard_violation": g.get("violation"), "guard_detail": g.get("detail")})
            b["wall_s"] = round(now() - t0, 3)
            return 2, b
        b["wall_s"] = round(now() - t0, 3)
        return r.returncode, b

    def diagnostics(self, work):
        """compiler feedback of the rebuilt modules (failures: the scheduler's stdout head = lean's JSON messages)"""
        out = []
        for fn in sorted(os.listdir(os.path.join(work, "log"))) if os.path.isdir(os.path.join(work, "log")) else []:
            if not (fn.startswith("sched") and fn.endswith(".out")):
                continue
            for ln in open(os.path.join(work, "log", fn), errors="replace"):
                if not ln.startswith('{"event": "module"'):
                    continue
                try:
                    r = json.loads(ln)
                except ValueError:
                    continue
                if r.get("rc") == 0 and not r.get("error_msg"):
                    continue
                msgs = []
                for m in (r.get("stdout_head") or "").splitlines():
                    try:
                        j = json.loads(m)
                        msgs.append({k: j.get(k) for k in ("severity", "pos", "data", "fileName") if k in j})
                    except ValueError:
                        if m.strip():
                            msgs.append({"severity": "error" if "error" in m else "information", "data": m[:500]})
                out.append({"module": r.get("module"), "rc": r.get("rc"), "error": r.get("error_msg"),
                            "messages": msgs[:20], "stderr": (r.get("stderr_head") or "")[:500]})
        return out

    def export(self, work, xo, farm_base=None):
        c = self.cfg
        et = min(self.jthreads, 128)   # bin/fastverify's E1_MAX_THREADS
        argv = [os.path.join(self.fv, "export", "export.sh"), "--lean-path",
                open(os.path.join(work, "log", "lean_path.txt")).read().strip(), "--module", c["solution_module"],
                "--targets-nl", os.path.join(self.st, "targets.txt"), "--toolchain", c["tc"], "--project",
                os.path.join(work, "proj"), "--binds", os.path.join(work, "log", "binds.tsv"), "--out", xo,
                "--threads", str(et), "--json", xo + ".json"]
        if farm_base:   # a --copy-mode farm candidate links into the fixed base project, which the
            argv += ["--ro", farm_base]   # export sandbox's S4 masks hide: that tree (this service's own) is bound read-only
        t0 = now()
        r = self.run(self.guarded(argv, "export", xo), capture_output=True, text=True)
        rc = 2 if (r.returncode == 125 and self.guard) else r.returncode
        return rc, round(now() - t0, 3)

    def check(self, xo, rdir, warm):
        argv = [self.check_script, xo, self.chx, self.cfgp,
                "--threads", str(self.jthreads), "--integrity-cache", self.icache, "--json", xo + ".check.json",
                "--log", xo + ".check.log"]
        if self.check_kind == "frontier" and self.allowed:
            argv += ["--allowed", self.allowed]
        if self.check_kind == "frontier" and self.pinned:
            argv += ["--pinned", self.pinned]
        if self.check_kind == "frontier":   # skip check A when the frontier challenge C' is unchanged
            argv += ["--a-cache", self.acache]
        if self.pins:
            argv += ["--pins", self.pins]
        if self.hide:
            argv += ["--hide", self.hide]
        if warm:
            argv += ["--incr-dir", warm.d]
        t0 = now()
        r = self.run(argv, capture_output=True, text=True)
        c = jload(xo + ".check.json", {}) or {}
        return r.returncode, c, round(now() - t0, 3)

    def lake_build_export(self, src, work, xo):
        """--build lake: tools/ci/official-incr.sh on the persistent official tree S/lake (sync + the release's `lake build
        <solution module>` in the official build sandbox + LEAN_PATH + the release's official exporter), no check"""
        c = self.cfg
        t0 = now()
        with self.build_lock:   # one persistent tree: builds are serialized (checks of earlier requests may overlap)
            os.makedirs(work, exist_ok=True)
            gr = self.run(self.guarded([os.path.join(self.fv, "tools", "ci", "official-incr.sh"), os.path.join(self.st, "lake"),
                                        src, os.path.join(self.st, "challenge"), work, "--targets",
                                        os.path.join(self.st, "targets.txt"), "--packages", c["packages"], "--fv", self.fv,
                                        "--solution-only", "--no-check"], "lake", work),
                          env=dict(os.environ, FASTVERIFY=self.fv), capture_output=True, text=True)
        if gr.returncode == 125 and self.guard:   # a limit was hit: no verdict (the summary may be missing or partial)
            g = jload(work + ".lake.guard.json", {}) or {}
            return {"build_exit": None}, {"exit": 2, "guard_violation": g.get("violation"),
                                          "guard_detail": g.get("detail"), "wall_s": round(now() - t0, 3)}, []
        sm = jload(os.path.join(work, "summary.json"), {}) or {}
        b = {"exit": sm.get("build_exit"), "build_s": sm.get("build_s"), "sync_s": sm.get("sync_s"),
             "lake_built": sm.get("lake_built"), "lake_jobs": sm.get("lake_jobs"), "wall_s": round(now() - t0, 3),
             "dirty": sm.get("lake_built")}
        diag = []
        try:
            log = open(os.path.join(work, "build.log"), errors="replace").read()
            for m in re.finditer(r"(?m)^(?:error|✖|.*: error): ?(.*)$", log):
                if len(diag) < 20:
                    diag.append({"module": None, "error": True,
                                 "messages": [{"severity": "error", "data": m.group(0)[:500]}]})
        except OSError:
            pass
        x = os.path.join(work, "solution.export")
        if sm.get("build_exit") == 0 and sm.get("export_exit") == 0 and os.path.isfile(x):
            os.replace(x, xo)
        return sm, b, diag

    def cold_attempt(self, rdir, src, ev):
        """the default: the COLD sound path - bin/fastverify --preset sound on exactly the submitted tree
        (a fresh build in its own work directory, the export, the trusted check; nothing of the base or of earlier requests
        is reused). Its exit / verdict is the answer. Under --guard the whole run is wrapped (a violation = NO-VERDICT)."""
        work = os.path.join(rdir, "a1-cold")
        argv = [os.path.join(self.fv, "bin", "fastverify"), src, os.path.dirname(self.chx), work, "--preset", "sound",
                "--threads", str(self.jthreads), "--packages", self.cfg["packages"],
                "--challenge-sha256", self.cfg["challenge_sha256"], "--export-dir", "none"]
        if self.pins:
            argv += ["--pins", self.pins]
        att = {"attempt": 1, "mode": "cold"}
        # bin/fastverify refuses --challenge-sha256 without --comparator-sha256: the sha256 of the
        # comparator config actually passed (the state's private copy), which must still be the one taken at serve start and
        # the init pin (if any); forwarded with --challenge-sha256
        try:
            csha = sha256_file(self.cfgp)
        except OSError:
            csha = None
        pin = self.cfg.get("comparator_sha256")   # recorded by init; serve refuses a state without it
        if csha is None or csha != self.cfg_sha or csha != pin:
            att.update({"outcome": "cold2", "build": {"exit": 2, "cold": True, "exact": True, "wall_s": 0.0,
                                                      "detail": "comparator config sha256 %s != pin %s / serve-time %s: refused"
                                                                % (csha, pin, self.cfg_sha)},
                        "check": {"verdict": None, "reason": "comparator config does not match its pin: refused"}})
            return 2, att, work, None
        argv[argv.index("--challenge-sha256"):argv.index("--challenge-sha256")] = ["--comparator-sha256", csha]
        ev({"event": "cold", "attempt": 1})
        t0 = now()
        with open(work + ".log", "w") as lf:
            r = self.run(self.guarded(argv, "cold", work), stdout=lf, stderr=subprocess.STDOUT)
        res = jload(os.path.join(work, "result.json"), {}) or {}
        rc = r.returncode if r.returncode in (0, 1) else 2
        b = {"exit": r.returncode, "cold": True, "exact": True, "wall_s": round(now() - t0, 3)}
        if r.returncode == 125 and self.guard:
            g = jload(work + ".cold.guard.json", {}) or {}
            b.update({"guard_violation": g.get("violation"), "guard_detail": g.get("detail")})
            rc = 2
        if rc in (0, 1) and res.get("verdict") != VERDICT.get(rc):   # the exit and the recorded verdict must agree
            rc = 2
            b["detail"] = f"bin/fastverify exit {r.returncode} but result verdict {res.get('verdict')!r}"
        att["build"] = b
        att["outcome"] = "cold%d" % rc
        att["check"] = {"verdict": res.get("verdict"),
                        "reason": str(res.get("verdict_basis") or res.get("reason") or res.get("why") or "")[:500],
                        "result": os.path.join(work, "result.json")}
        att["export_sha256"] = (res.get("export") or {}).get("sha256")
        ev({"event": "cold-done", "attempt": 1, "exit": rc, "wall_s": b["wall_s"]})
        return rc, att, work, None

    def attempt(self, base, src, rdir, k, mode, chal_ok, ev, req):
        if self.cfg.get("build") == "lake":
            mode = "lake"
        work = os.path.join(rdir, f"a{k}-{mode}")
        att = {"attempt": k, "mode": mode}
        if mode == "lake":
            xd = os.path.join(rdir, "x")
            os.makedirs(xd, exist_ok=True)
            xo = os.path.join(xd, f"solution{k}.export")
            sm, b, diag = self.lake_build_export(src, work, xo)
            att["build"] = b
            if diag:
                att["diagnostics"] = diag
            ev({"event": "build", "attempt": k, "mode": mode, "exit": b.get("exit"), "wall_s": b.get("build_s"),
                "dirty": b.get("dirty"), "diagnostics": diag})
            if sm.get("build_exit") != 0:
                att["outcome"] = "build1" if sm.get("build_exit") is not None else "build2"
                return (1 if sm.get("build_exit") is not None else 2), att, work, None
            att["export_s"] = sm.get("export_s")
            if sm.get("export_exit") != 0 or not os.path.isfile(xo):
                att["outcome"] = "export%s" % sm.get("export_exit")
                ev({"event": "export", "attempt": k, "exit": sm.get("export_exit"), "wall_s": sm.get("export_s")})
                # the release's official exporter failing on a built project = the official flow's export fails (REJECTED)
                return (1 if sm.get("export_exit") == 1 else 2), att, work, None
            return self.post_export(base, rdir, k, att, work, xo, chal_ok, ev, req, sm.get("export_s"))
        brc, b = self.build(base, src, work, mode)
        att["build"] = {x: b.get(x) for x in ("exit", "detail", "optimistic", "exact", "full_build_why", "stale", "modules",
                                               "seed", "dirty", "dirty_full",
                                               "n_changed", "n_added", "n_removed", "changed", "added", "plan_reused", "copy_s",
                                               "sync_s", "plan_s", "build_s", "sum_module_wall_s", "max_module_wall_s",
                                               "wall_s", "closure_of", "interface_waves", "guard_violation",
                                               "guard_detail")}
        diag = self.diagnostics(work)
        if diag:
            att["diagnostics"] = diag
        ev({"event": "build", "attempt": k, "mode": mode, "exit": brc, "wall_s": b.get("wall_s"),
            "dirty": b.get("dirty"), "diagnostics": diag})
        if brc != 0:
            att["outcome"] = f"build{brc}"
            return (1 if brc == 1 else 2), att, work, None
        dl = self.delta_attempt(base, rdir, k, att, work, chal_ok, ev, req)
        if dl is not None:
            return dl
        if self.delta_only and self.check_kind == "warm":
            # screening daemons on RH-size bases: the full export + whole-export check of a non-decisive delta costs a
            # node-hour; answer at once (no verdict) and leave the decision to the train's full check
            att["outcome"] = "delta-inconclusive"
            wdi = att.get("warmdelta") or {}
            att["note"] = "warm delta check inconclusive (serve --delta-only; the train's full check decides): " + str(
                wdi.get("tier2_reason") or wdi.get("reason") or wdi.get("skipped") or "no delta path")[:300]
            ev({"event": "check", "attempt": k, "exit": 2, "verdict": "NO-VERDICT", "backend": "warmdelta",
                "reason": att["note"]})
            return 2, att, work, None
        xd = os.path.join(rdir, "x")
        os.makedirs(xd, exist_ok=True)
        xo = os.path.join(xd, f"solution{k}.export")
        erc, es = self.export(work, xo, os.path.realpath(base["proj"]) if b.get("copy_mode") == "farm" and base.get("proj") else None)
        att["export_s"] = es
        if erc != 0:
            att["outcome"] = f"export{erc}"
            ev({"event": "export", "attempt": k, "exit": erc, "wall_s": es})
            return 2, att, work, None
        return self.post_export(base, rdir, k, att, work, xo, chal_ok, ev, req, es)

    def delta_attempt(self, base, rdir, k, att, work, chal_ok, ev, req):
        """--check warm on a 4.33.1 base whose export the warm sidecar verified: export only the REBUILT modules (the warm check's
        untrusted delta exporter, tools/delta-export) and ask fvcheckd check_delta. ACCEPTED / REJECTED from it are the
        verdict (the reviewed trusted warm check); anything else (FALLBACK_REQUIRED, DECLINED, no answer, delta export
        failure) -> None = the full export + the unchanged check. Skipped for drift / frontier requests."""
        wd = self.warmd
        # the delta is computed against base["proj"] (incr-build rebuilt the modules that differ from it) and
        # judged by fvcheckd against ITS base export wd.base; that is sound only if wd.base is the export of exactly the
        # tree base["proj"]: base["export_of"] records the tree an export was made from (Service._verify advances the base
        # export only with a fresh export of the new tree, else drops it), and wd.base must be that very export
        if wd is None or not wd.is_ready() or self.check_kind != "warm" or self.copy_mode == "hardlink" \
                or (self.cfg.get("release") != "4.33.1" and not self.warm_pins()) \
                or (self.want_drift(req) and not self.exphash) or not base.get("export") \
                or not base.get("export_of") or base.get("export_of") != (base.get("proj") or base.get("src")) \
                or os.path.realpath(wd.base) != os.path.realpath(base["export"]):
            return None
        exsh = os.path.join(self.fv, "tools", "delta-export", "export-delta.sh")
        dbin = "/scratch/fastverify-next/warm/714773ea/lean4export-delta" if self.cfg.get("release") == "4.33.1" else None
        if not os.access(exsh, os.X_OK) or (dbin and not os.access(dbin, os.X_OK)):
            return None
        t0 = now()
        mods, seen = [], set()
        for fp in sorted(glob.glob(os.path.join(work, "log", "plan-incr*.jsonl"))):
            for ln in open(fp, errors="replace"):
                try:
                    nm = json.loads(ln).get("name")
                except ValueError:
                    continue
                if nm and nm not in seen:
                    seen.add(nm)
                    mods.append(nm)
        # fvcheckd drops every base constant that reaches a changed one (kernel defeq may unfold theorem values) and
        # needs them back in the delta: an optimistic build left the clean importers' outputs in place, so their
        # (unchanged) modules join the delta. Their cone: the importers of the rebuilt modules in the build plan.
        if mods:
            deps = {}
            try:
                for ln in open(os.path.join(work, "log", "plan.jsonl"), errors="replace"):
                    try:
                        o = json.loads(ln)
                    except ValueError:
                        continue
                    if "name" in o:
                        deps[o["name"]] = o.get("deps") or []
            except OSError:
                return None
            keep = None
            if self.cfg.get("closure_only"):   # only the solution module's import closure was built / is exported
                keep, st = set(), [self.cfg["solution_module"]]
                while st:
                    m = st.pop()
                    if m not in keep:
                        keep.add(m)
                        st.extend(deps.get(m, ()))
            users = {}
            for m, ds in deps.items():
                if keep is not None and m not in keep:
                    continue
                for d in ds:
                    users.setdefault(d, []).append(m)
            stack = list(mods)
            while stack:
                for u in users.get(stack.pop(), ()):
                    if u not in seen:
                        seen.add(u)
                        mods.append(u)
                        stack.append(u)
                if len(mods) > self.delta_max:
                    att["warmdelta"] = {"skipped": f"importer cone > {self.delta_max} modules: full export"}
                    return None
        xd = os.path.join(rdir, "x")
        os.makedirs(xd, exist_ok=True)
        dx, dm = os.path.join(xd, f"delta{k}.ndjson"), os.path.join(xd, f"delta{k}.mods")
        with open(dm, "w") as f:
            f.write("".join(m + "\n" for m in mods))
        info = {"modules": len(mods)}
        if mods:
            argv = [exsh, os.path.join(work, "proj"), "@" + dm, dx, "--packages", self.cfg["packages"], "--toolchain",
                    self.cfg["tc"]] + (["--bin", dbin] if dbin else []) + ["--threads", "1"]
            r = self.run(self.guarded(argv, "delta", dx), capture_output=True, text=True)
            info["export_exit"] = r.returncode
            if r.returncode != 0 or not os.path.isfile(dx) or os.path.getsize(dx) == 0:
                info["seconds"] = round(now() - t0, 3)
                att["warmdelta"] = info
                return None
        else:
            with open(dx, "w") as f:
                f.write('{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},'
                        '"lean":{"version":"4.33.1"}}}\n')
        os.chmod(dx, 0o444)
        info["delta_bytes"] = os.path.getsize(dx)
        info["export_s"] = round(now() - t0, 3)
        if not chal_ok():
            att["outcome"] = "challenge-pin"
            return 2, att, work, None
        t1 = now()
        try:
            wr = wd.check_delta(dx, 900)
        except (OSError, ValueError) as e:
            wr = {"verdict": "NO-ANSWER", "exit": 2, "reason": repr(e)[:200]}
        info.update({x: wr.get(x) for x in ("verdict", "exit", "reason", "wall_ms", "input_sha256", "base_sha256")})
        info["check_s"] = round(now() - t1, 3)
        att["warmdelta"] = info
        self.log(event="warmdelta", run=os.path.basename(rdir), tier=1, modules=len(mods), bytes=info.get("delta_bytes"),
                 verdict=wr.get("verdict"), reason=str(wr.get("reason") or "")[:300], check_s=info["check_s"])
        missing = "not found in solution" in str(wr.get("reason") or "")   # a gap in the delta, not a verdict
        if missing and mods:   # tier 2: the transitive closure of the cone minus the base's constants
            man = self.delta_manifest(wd)
            if man:
                dx2 = os.path.join(xd, f"delta{k}t2.ndjson")
                argv = [exsh, os.path.join(work, "proj"), "@" + dm, dx2, "--packages", self.cfg["packages"],
                        "--toolchain", self.cfg["tc"]] + (["--bin", dbin] if dbin else []) + [
                        "--threads", str(min(16, self.jthreads)), "--exclude", man]
                t2 = now()
                r = self.run(self.guarded(argv, "delta2", dx2), capture_output=True, text=True)
                info["tier2_export_exit"], info["tier2_export_s"] = r.returncode, round(now() - t2, 3)
                if r.returncode == 0 and os.path.isfile(dx2) and os.path.getsize(dx2) > 0:
                    os.chmod(dx2, 0o444)
                    info["tier2_delta_bytes"] = os.path.getsize(dx2)
                    t1 = now()
                    try:
                        wr = wd.check_delta(dx2, 900)
                    except (OSError, ValueError) as e:
                        wr = {"verdict": "NO-ANSWER", "exit": 2, "reason": repr(e)[:200]}
                    info.update({"tier2_" + x: wr.get(x) for x in ("verdict", "exit", "reason", "wall_ms")})
                    self.log(event="warmdelta", run=os.path.basename(rdir), tier=2, bytes=info.get("tier2_delta_bytes"),
                             verdict=wr.get("verdict"), reason=str(wr.get("reason") or "")[:300],
                             check_s=round(now() - t1, 3))
                    info["check_s"] = round(info["check_s"] + now() - t1, 3)
                    info["export_s"] = round(info["export_s"] + info["tier2_export_s"], 3)
                    missing = "not found in solution" in str(wr.get("reason") or "")
        if wr.get("exit") in (0, 1) and wr.get("verdict") == VERDICT[wr["exit"]] and not missing \
                and wr.get("challenge_sha256") == self.cfg["challenge_sha256"] \
                and wr.get("base_sha256") and wr.get("base_sha256") == (base.get("export_sha256") or self.warm_base_sha(wd)):
            att["export_s"] = info["export_s"]
            att["check_s"] = info["check_s"]
            att["check"] = {"verdict": wr["verdict"], "exit": wr["exit"], "reason": wr.get("reason"),
                            "basis": "warm sound check, delta of %d rebuilt module(s) over the verified base export "
                                     "(check/warm/fvcheckd.py check_delta): %s" % (len(mods), wr.get("reason"))}
            att["outcome"] = "check%d-warmdelta" % wr["exit"]
            ev({"event": "check", "attempt": k, "exit": wr["exit"], "wall_s": att["check_s"], "verdict": wr["verdict"],
                "reason": wr.get("reason"), "backend": "warmdelta", "delta_modules": len(mods)})
            if self.want_drift(req) and self.exphash:
                att["drift"] = self.delta_drift(base, dx)
                ev({"event": "drift", "attempt": k, "statement_changed": att["drift"].get("statement_changed"),
                    "result": att["drift"].get("result")})
            return wr["exit"], att, work, None
        return None

    def warm_base_sha(self, wd):
        """sha256 of the warm sidecar's base export file (hashed once per sidecar), for the base_sha256 echo check
        when the base record carries no export_sha256"""
        with self.manifest_lock:
            if getattr(wd, "base_sha", None) is None:
                try:
                    wd.base_sha = sha256_file(wd.base)
                except OSError:
                    wd.base_sha = ""
            return wd.base_sha or None

    def delta_manifest(self, wd):
        """the base export's constant names (the warm-delta-extract manifest), made once per warm sidecar"""
        man = os.path.join(wd.d + ".manifest.txt")
        with self.manifest_lock:
            return self._delta_manifest(wd, man)

    def _delta_manifest(self, wd, man):
        if getattr(wd, "manifest_ok", None) is None:
            wde = "/scratch/fastverify-next/warm/v1/warm-delta-extract"
            r = subprocess.run([wde, "manifest", wd.base, man + ".tmp"], capture_output=True, text=True) \
                if os.access(wde, os.X_OK) else None
            wd.manifest_ok = bool(r is not None and r.returncode == 0 and os.path.isfile(man + ".tmp"))
            if wd.manifest_ok:
                os.replace(man + ".tmp", man)
        return man if wd.manifest_ok else None

    def post_export(self, base, rdir, k, att, work, xo, chal_ok, ev, req, es):
        os.chmod(xo, 0o444)
        att["export_bytes"] = os.path.getsize(xo)
        t0 = now()
        hres = {}

        def hashit():
            hres["sha"] = sha256_file(xo)
            hres["s"] = round(now() - t0, 3)
        hth = threading.Thread(target=hashit, daemon=True)
        hth.start()
        # the sha256 is needed BEFORE the check only for the memo lookup, drift and the warm sidecar's echo; otherwise
        # it runs concurrently with the check (a 61 GB export: ~3 min of single-threaded hashing off the critical path)
        deferred = not (self.reuse or self.want_drift(req) or (self.warmd is not None and self.warmd.is_ready()))
        if not deferred:
            hth.join()
            att["export_sha256"], att["export_sha256_s"] = hres["sha"], hres["s"]
        else:
            att["export_sha256"] = None
        ev({"event": "export", "attempt": k, "exit": 0, "wall_s": es, "bytes": att["export_bytes"],
            "sha256": att["export_sha256"]})
        if not chal_ok():
            att["outcome"] = "challenge-pin"
            return 2, att, work, xo
        dres, dth = {}, None
        bx = base.get("export")
        if self.want_drift(req) and bx and os.path.isfile(bx) and base.get("export_sha256") != att["export_sha256"]:
            dfun = (lambda: self.drift(bx, xo, xo)) if self.expdiff else (lambda: self.delta_drift(base, xo, full=True))
            dth = threading.Thread(target=lambda: dres.update(dfun()), daemon=True)
            dth.start()
        elif self.want_drift(req) and base.get("export_sha256") == att["export_sha256"]:
            dres.update({"result": "export byte-identical to the base export", "statement_changed": 0})
        key = self.memo_key(att["export_sha256"]) if not deferred else None
        td0 = self.trust_digest() if deferred else None
        hit = self.memo.get(key) if self.reuse else None
        if hit:   # opt-in (--reuse-identical): this exact export was judged by the trusted check before (same pins)
            att["check_s"] = 0.0
            att["check"] = {"verdict": hit["verdict"], "exit": hit["exit"], "reason": hit["reason"],
                            "basis": hit.get("basis"), "reused_from_run": hit["run"],
                            "reused": "byte-identical export (sha256 %s) judged by the trusted check in run %s with the "
                                      "same challenge export, comparator config and pinned binaries" % (
                                          att["export_sha256"][:16], hit["run"])}
            if "frontier" in hit:
                att["frontier"] = hit["frontier"]
            att["outcome"] = "check%d-reused" % hit["exit"]
            ev({"event": "check", "attempt": k, "exit": hit["exit"], "wall_s": 0.0, "verdict": hit["verdict"],
                "reason": hit["reason"], "reused_from_run": hit["run"]})
            if dth:
                dth.join()
            if dres:
                att["drift"] = dres
            return hit["exit"], att, work, xo
        xsz = os.path.getsize(xo) if os.path.isfile(xo) else 0
        if self.warmd is not None and self.warmd.is_ready() and xsz > self.warm_full_max:
            # a whole-export query of an RH-size export outlives the 900 s query budget; fvcheckd then kills the timed-out
            # kernel leg and the next query respawns it = a full re-verification of the base (C3c dry run, 17:20Z)
            att["warmd"] = {"skipped": "export %.1f GB > --warm-full-max %.1f GB: unchanged sound check"
                            % (xsz / 1e9, self.warm_full_max / 1e9)}
        elif self.warmd is not None and self.warmd.is_ready():
            t0 = now()
            try:
                wr = self.warmd.check(xo, 900)
            except (OSError, ValueError) as e:
                wr = {"verdict": "NO-ANSWER", "exit": 2, "reason": repr(e)[:200]}
            att["warmd"] = {k: wr.get(k) for k in ("verdict", "exit", "reason", "wall_ms", "input_sha256", "base_sha256")}
            att["warmd"]["seconds"] = round(now() - t0, 3)
            if wr.get("exit") in (0, 1) and wr.get("verdict") == VERDICT[wr["exit"]] \
                    and wr.get("input_sha256") == att["export_sha256"] \
                    and wr.get("challenge_sha256") == self.cfg["challenge_sha256"]:
                att["check_s"] = att["warmd"]["seconds"]
                att["check"] = {"verdict": wr["verdict"], "exit": wr["exit"], "reason": wr.get("reason"),
                                "basis": "warm sound check (check/warm/fvcheckd.py): " + str(wr.get("reason"))}
                att["outcome"] = "check%d-warmd" % wr["exit"]
                ev({"event": "check", "attempt": k, "exit": wr["exit"], "wall_s": att["check_s"],
                    "verdict": wr["verdict"], "reason": wr.get("reason"), "backend": "warmd"})
                if dth:
                    dth.join()
                if dres:
                    att["drift"] = dres
                return wr["exit"], att, work, xo
        warm = self.take_warm()
        att["warm"] = bool(warm)
        if warm:
            att["warm_snap_is_base"] = warm.snap == base.get("export")
            att["warm_age_s"] = round(now() - warm.t0, 1)
            self.stats["warm_used"] += 1
        crc, c, cs = self.check(xo, rdir, warm)
        if warm:
            try:
                tail = [l.strip()[:300] for l in open(os.path.join(warm.d, "server.log"), errors="replace")
                        if "[incr]" in l][-3:]
                att["warm_tail"] = tail
            except OSError:
                pass
            warm.stop()
            shutil.rmtree(warm.d, ignore_errors=True)
        att["check_s"] = cs
        att["check"] = {x: c.get(x) for x in ("verdict", "exit", "reason", "basis", "leg_ms", "wall_s", "claim",
                                               "frontier_size", "judge") if x in c}
        if isinstance(c.get("frontier"), list):
            att["frontier"] = [{k: e.get(k) for k in ("name", "type", "type_sha256") if k in e}
                               for e in c["frontier"] if isinstance(e, dict)]
        att["outcome"] = f"check{crc}"
        ev({"event": "check", "attempt": k, "exit": crc, "wall_s": cs, "verdict": c.get("verdict"),
            "reason": c.get("reason")})
        if dth:
            dth.join()
        if dres:
            att["drift"] = dres
            ev({"event": "drift", "attempt": k, "statement_changed": dres.get("statement_changed"),
                "result": dres.get("result")})
        if deferred:
            hth.join()
            att["export_sha256"], att["export_sha256_s"] = hres.get("sha"), hres.get("s")
            key = self.memo_key(att["export_sha256"]) if att["export_sha256"] and self.trust_digest() == td0 else None
        # memoize only if the trusted check's files did not change while it ran (the key is re-derived after the check)
        if crc in (0, 1, 3) and c.get("exit") == crc and c.get("verdict") == VERDICT[crc] and key \
                and self.memo_key(att["export_sha256"]) == key:
            rec = {"key": key, "run": os.path.basename(rdir), "attempt": k, "exit": crc, "verdict": c.get("verdict"),
                   "reason": c.get("reason"), "basis": c.get("basis"), "t": now()}
            if "frontier" in att:
                rec["frontier"] = att["frontier"]
            with self.lock:
                self.memo[key] = rec
                with open(os.path.join(self.st, "verdicts.jsonl"), "a") as f:
                    f.write(json.dumps(rec) + "\n")
        return crc, att, work, xo

    def drift(self, old_x, new_x, out):
        """statement drift between the base export and this one (expdiff, UNTRUSTED information for the user:
        which declarations of the targets' closure changed statement / kind, were removed, or got a new value)"""
        t0 = now()
        tsv = out + ".drift.tsv"
        r = self.run([self.expdiff, "diff", "-j", str(min(16, self.jthreads)), "--targets",
                            os.path.join(self.st, "targets.txt"), "--tsv", tsv, old_x, new_x],
                           capture_output=True, text=True, timeout=3600)
        d = {"vs_export": old_x, "seconds": round(now() - t0, 3), "exit": r.returncode}
        if r.returncode != 0:
            d["error"] = r.stderr.strip()[-300:]
            return d
        cnt, names = {}, {}
        try:
            with open(tsv) as f:
                next(f)
                for ln in f:
                    c = ln.rstrip("\n").split("\t")
                    if len(c) < 2:
                        continue
                    st = c[0]
                    cnt[st] = cnt.get(st, 0) + 1
                    if st.startswith(("STATEMENT-CHANGED", "kind-changed", "removed", "dropped")) or st == "added":
                        names.setdefault(st, [])
                        if len(names[st]) < 50:
                            names[st].append(c[1])
        except OSError as e:
            d["error"] = repr(e)
            return d
        d["counts"] = cnt
        d["names"] = names
        d["statement_changed"] = cnt.get("STATEMENT-CHANGED", 0)
        for ln in r.stdout.splitlines():
            if ln.startswith("RESULT"):
                d["result"] = ln.split("\t", 1)[-1]
        return d

    def tool_digest(self):
        """the digest over the explicit check files only: the frontier ledger's 'same check files' test"""
        h = hashlib.sha256()
        for f in self.trust_files:
            h.update(f.encode() + b"\0" + (sha256_file(f).encode() if os.path.isfile(f) else b"missing") + b"\n")
        return h.hexdigest()

    def trust_digest(self):
        h = hashlib.sha256()
        for f in self.trust_files:
            h.update(f.encode() + b"\0" + (sha256_file(f).encode() if os.path.isfile(f) else b"missing") + b"\n")
        h.update(b"verdict-files\n")   # every file under check/ config/ lib/ toolchains/ (stat-cached sha256)
        if self.vprewarm.is_alive():
            self.vprewarm.join()
        for f in verdict_files(self.fv):
            h.update(f.encode() + b"\0" + self.vsha(f).encode() + b"\n")
        return h.hexdigest()

    def memo_key(self, export_sha):
        return "%s:%s:%s:%s:%s:%s" % (export_sha, self.cfg["challenge_sha256"], self.cfg_sha, self.trust_digest(),
                                      self.check_kind, self.allowed_sha)

    def own_sorry(self, base, src, att):
        """UNTRUSTED retry heuristic: an optimistic attempt rejected for sorryAx whose edit itself ADDS a `sorry` token
        (outside a line comment) is rejected because of the edit, not because of stale importers -> no full-cone retry
        (the verdict stays the trusted check's REJECTED; this only saves time on placeholder states)"""
        why = ((att.get("check") or {}).get("reason") or "")
        if "sorryAx" not in why:
            return None
        import difflib
        bsrc = base.get("src") or base.get("proj")
        bb = att.get("build") or {}
        for rel in (bb.get("changed") or []) + (bb.get("added") or []):
            if not rel.endswith(".lean"):
                continue
            try:
                old = open(os.path.join(bsrc, rel), encoding="utf-8", errors="replace").read().splitlines()
            except OSError:
                old = []
            try:
                new = open(os.path.join(src, rel), encoding="utf-8", errors="replace").read().splitlines()
            except OSError:
                continue
            for ln in difflib.ndiff(old, new):
                if ln.startswith("+ ") and re.search(r"(^|[^\w.'])sorry([^\w'!?]|$)", ln[2:].split("--", 1)[0]):
                    return f"the edit adds `sorry` in {rel}: the sorryAx reject is the edit's own (no importer-cone retry)"
        return None

    @staticmethod
    def locate(frontier, src, budget_s=5.0):
        """UNTRUSTED display aid: for every open lemma, the file, line and the statement AS WRITTEN in
        the request's sources (the authoritative statement is the checker's `type`). Found by the last name component."""
        want = {}
        for e in frontier[:200]:
            n = e.get("name") or ""
            short = n.split(".")[-1]
            if short:
                want.setdefault(short, []).append(e)
        if not want:
            return
        pat = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(\S+)")
        t_end = now() + budget_s
        for root, dirs, files in os.walk(src):
            dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
            for fn in files:
                if not fn.endswith(".lean") or now() > t_end:
                    continue
                path = os.path.join(root, fn)
                try:
                    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
                except OSError:
                    continue
                for i, ln in enumerate(lines):
                    m = pat.match(ln)
                    if not m:
                        continue
                    short = m.group(1).split(".")[-1]
                    for e in want.get(short, []):
                        if "source" in e:
                            continue
                        stmt = []
                        for j in range(i, min(i + 30, len(lines))):
                            stmt.append(lines[j])
                            if ":=" in lines[j]:
                                break
                        txt = "\n".join(stmt)
                        e["source"] = {"file": os.path.relpath(path, src), "line": i + 1,
                                       "statement": txt.split(":=", 1)[0].rstrip()[:2000]}

    def hide_file(self):
        """(availability only) the published no-expose hide list of the check's Lean release - the --pins file's
        TC_VERSION, else check/sound/pins.env's - passed as --hide when the check script supports it, like bin/fastverify;
        a missing list = slower checks, never a different verdict"""
        try:
            if "--hide" not in open(self.check_script, encoding="utf-8", errors="replace").read():
                return None
            pf = self.pins or os.path.join(self.fv, "check", "sound", "pins.env")
            tc = next((ln.split("=", 1)[1].strip() for ln in open(pf) if ln.startswith("TC_VERSION=")), "")
        except OSError:
            return None
        if ":v" not in tc:
            return None
        h = os.path.join(self.fv, "check", "sound", "hide", "lean-%s-no-expose.txt" % tc.split(":v", 1)[1])
        return h if os.path.isfile(h) else None

    def warm_pins(self):
        """the warm-check pins for this state's release: None = the default (4.36 judge; 4.33.1 bases), else the path of
        check/warm/pins-<major><minor>.env (e.g. pins-437.env for 4.37.0-rc1) when the package has it"""
        rel = str(self.cfg.get("release") or "")
        if rel == "4.33.1" or not rel:
            return None
        parts = rel.split(".")
        p = os.path.join(self.fv, "check", "warm", "pins-%s%s.env" % (parts[0], parts[1] if len(parts) > 1 else ""))
        return p if os.path.isfile(p) else None

    def want_drift(self, req):
        return bool(self.expdiff or self.exphash) and bool(req.get("drift", self.drift_default))

    def base_hashes(self, bx):
        """{name: (kind, lvl_h, type_hk, value_hk)} of an export (exphash via the pinned tools/dupfind copy),
        made once per base export and cached on disk + in memory (UNTRUSTED information, never a verdict)"""
        with self.hash_lock:
            if self.hash_cache.get("export") == bx:
                return self.hash_cache["decls"]
            d = os.path.join(self.st, "hashes", hashlib.sha256(bx.encode()).hexdigest()[:16])
            tsv = os.path.join(d, "decls.tsv")
            if not os.path.isfile(tsv):
                shutil.rmtree(d, ignore_errors=True)
                r = subprocess.run([self.exphash, bx, d], capture_output=True, text=True)
                if r.returncode != 0 or not os.path.isfile(tsv):
                    return None
            self.hash_cache = {"export": bx, "decls": self.read_hashes(tsv)}
            return self.hash_cache["decls"]

    @staticmethod
    def read_hashes(tsv):
        out = {}
        with open(tsv, encoding="utf-8", errors="replace") as f:
            next(f, None)
            for ln in f:
                c = ln.rstrip("\n").split("\t")
                if len(c) >= 7:
                    out[c[1]] = (c[0], c[3], c[4], c[6])
        return out

    def delta_drift(self, base, dx, full=False):
        """statement drift of a DELTA request against the base: every declaration of the delta (rebuilt modules + their
        importer cone) compared by exphash's statement hash with the base's declaration of the same name (statement =
        kind + universe levels + type up to binder names/infos). Declarations the request REMOVED are not seen here."""
        t0 = now()
        bh = self.base_hashes(base["export"])
        d = {"tool": "exphash (delta vs base)", "vs_export": base["export"]}
        if bh is None:
            d["error"] = "exphash of the base export failed"
            return d
        od = dx + ".hash"
        shutil.rmtree(od, ignore_errors=True)
        r = subprocess.run([self.exphash, dx, od], capture_output=True, text=True)
        if r.returncode != 0:
            d["error"] = r.stderr.strip()[-300:]
            return d
        cnt, names = {}, {}
        cur = self.read_hashes(os.path.join(od, "decls.tsv"))
        if full:   # a whole export: base declarations that are gone are 'removed'
            for name in bh:
                if name not in cur:
                    cnt["removed"] = cnt.get("removed", 0) + 1
                    names.setdefault("removed", [])
                    if len(names["removed"]) < 50:
                        names["removed"].append(name)
            d["tool"] = "exphash (export vs base)"
        for name, (kind, lvl, typ, val) in cur.items():
            b = bh.get(name)
            st = "added" if b is None else ("kind-changed" if b[0] != kind else
                                           "STATEMENT-CHANGED" if (b[1], b[2]) != (lvl, typ) else
                                           "value-changed" if b[3] != val else "identical")
            cnt[st] = cnt.get(st, 0) + 1
            if st != "identical":
                names.setdefault(st, [])
                if len(names[st]) < 50:
                    names[st].append(name)
        d.update({"counts": cnt, "names": names, "statement_changed": cnt.get("STATEMENT-CHANGED", 0),
                  "result": "statement changed: %d, kind changed: %d, added: %d, value changed: %d (delta only)" % (
                      cnt.get("STATEMENT-CHANGED", 0), cnt.get("kind-changed", 0), cnt.get("added", 0),
                      cnt.get("value-changed", 0)) + ("" if not full else ", removed: %d" % cnt.get("removed", 0)),
                  "seconds": round(now() - t0, 3)})
        if full:
            d["result"] = d["result"].replace(" (delta only)", "")
        shutil.rmtree(od, ignore_errors=True)
        return d

    @staticmethod
    def ledger(prev, cur, same_tool=True):
        """progress ledger of the sorry frontier between the base state and this one (names -> statement hashes).
        Statement hashes are only compared when both frontiers come from the same check files (the hash is over the
        checker's own rendering of the type: a check update would otherwise report every open lemma as restated)"""
        if cur is None:
            return None
        p = {e["name"]: e.get("type_sha256") for e in (prev or []) if "name" in e}
        c = {e["name"]: e.get("type_sha256") for e in cur if "name" in e}
        return {"open": len(c), "closed_since_base": sorted(set(p) - set(c)), "new_since_base": sorted(set(c) - set(p)),
                "restated_since_base": sorted(n for n in set(p) & set(c) if p[n] != c[n]) if same_tool else [],
                "restated_comparable": same_tool, "base_known": prev is not None}

    def verify(self, req, ev):
        t_arr = now()
        # requests that may move the base (advance / merge) are serialized by the merge lock and read the base only once
        # they hold it: the base cannot change under them (a merge queue); candidates (advance=false) run concurrently
        merging = bool(req.get("merge")) or req.get("advance", True)
        ml = self.merge_lock if merging else None
        if ml:
            ml.acquire()
        try:
            return self._verify_sem(req, ev, t_arr)
        finally:
            if ml:
                ml.release()

    def _verify_sem(self, req, ev, t_arr):
        self.sem.acquire()
        released = threading.Event()
        lock = threading.Lock()

        def release():
            with lock:
                if not released.is_set():
                    released.set()
                    self.sem.release()
        # slow lane: a request still running after --slow-lane seconds stops counting against --jobs,
        # so one long or runaway elaboration does not block every other agent (it is still bounded by --guard)
        timer = threading.Timer(self.slow_lane, release) if self.slow_lane else None
        if timer:
            timer.daemon = True
            timer.start()
        try:
            t_start = now()
            with self.lock:
                self.req_seq += 1
                rid = self.req_seq
                base = dict(self.base)
                self.inuse[base.get("run")] = self.inuse.get(base.get("run"), 0) + 1
            try:
                return self._verify(req, ev, t_arr, t_start, rid, base)
            finally:
                with self.lock:
                    self.inuse[base.get("run")] -= 1
        finally:
            if timer:
                timer.cancel()
            release()

    def _verify(self, req, ev, t_arr, t_start, rid, base):
        if True:
            rdir = os.path.join(self.st, "runs", "%05d" % rid)
            os.makedirs(rdir)
            res = {"id": rid, "label": req.get("label"), "trust": "none" if self.incremental else "sound",
                   "base_run": base.get("run"),
                   "queue_s": round(t_start - t_arr, 3)}
            ev({"event": "start", "id": rid, "queue_s": res["queue_s"]})
            try:
                t0 = now()
                res["source"] = self.materialize(req, rdir, base)
                res["materialize_s"] = round(now() - t0, 3)
                if self.copy_mode == "farm" and not req.get("merge") and not req.get("advance", True):
                    open(os.path.join(rdir, "farm"), "w").close()   # candidates never become a base: farm allowed
            except (ValueError, OSError) as e:
                res.update({"verdict": "NO-VERDICT", "exit": 2, "why": f"bad request: {e}"})
                return res
            src = os.path.join(rdir, "src")
            # the pinned challenge export: hashed concurrently with the build, compared before every check
            hres = {}
            ht = threading.Thread(target=lambda: hres.setdefault("sha", sha256_file(self.chx)), daemon=True)
            ht.start()

            def chal_ok():
                ht.join()
                return hres.get("sha") == self.cfg["challenge_sha256"]
            mode = req.get("mode") or self.mode
            atts = []
            if not self.incremental:   # the cold sound path (v0.1 default)
                ht.join()
                rc, att, work, xo = self.cold_attempt(rdir, src, ev)
                atts.append(att)
                res["mode"] = "cold"
                res["attempts"] = atts
                res["exit"] = rc
                res["verdict"] = VERDICT.get(rc, "NO-VERDICT")
                res["why"] = (att.get("check") or {}).get("reason") or att.get("outcome")
                if att.get("export_sha256"):
                    res["export_sha256"] = att["export_sha256"]
                res["build_s"] = att["build"].get("wall_s")   # build + export + check of the cold run
                res["total_s"] = round(now() - t_start, 3)
                res["latency_s"] = round(now() - t_arr, 3)
                res["challenge_sha256"] = self.cfg["challenge_sha256"]
                # the judged tree becomes the base of later --files requests (merge: only an ACCEPTED patch enters)
                adv = req.get("advance", True) and rc in (0, 1) and (not req.get("merge") or rc == 0)
                with self.lock:
                    if adv and self.base.get("run") == base.get("run"):
                        nb = {"run": "%05d" % rid, "proj": None, "plan": None, "src": src, "src0": src, "export": None,
                              "export_sha256": None, "export_of": None, "verdict": res["verdict"], "t": now(), "cold": True,
                              "frontier": self.base.get("frontier"), "frontier_tool": self.base.get("frontier_tool")}
                        old = self.base
                        self.base = nb
                        jdump(os.path.join(self.st, "base.json"), nb)
                        res["base_advanced"] = True
                        threading.Thread(target=self.gc, args=(old, rid), daemon=True).start()
                    else:
                        res["base_advanced"] = False
                self.stats["requests"] += 1
                self.stats[{0: "accepted", 1: "rejected"}.get(rc, "no_verdict")] += 1
                jdump(os.path.join(rdir, "result.json"), res)
                self.log(event="verify", id=rid, verdict=res["verdict"], total_s=res["total_s"])
                return res
            rc, att, work, xo = self.attempt(base, src, rdir, 1, mode, chal_ok, ev, req)
            atts.append(att)
            b1 = att["build"]
            own = self.own_sorry(base, src, att)
            # retry with the full importer cone only if it differs from what was built: an optimistic attempt whose
            # cone = the edited modules (dirty_full == dirty) would rebuild and re-check the very same tree; a build
            # failure of an optimistic attempt is retried too (a stale clean importer between two edited modules can
            # break the elaboration of the second one), a failure of a complete cone is final
            differs = (mode == "interface" and not att["outcome"].startswith("build1")) or \
                (b1.get("optimistic") is True and (b1.get("dirty_full") or 0) > (b1.get("dirty") or 0))
            if rc not in (0, 3) and mode in ("optimistic", "interface") and differs \
                    and not att["outcome"].startswith("challenge") and not att["outcome"].startswith("build2") \
                    and att["outcome"] != "delta-inconclusive" \
                    and not req.get("optimistic_only") and not own:
                rc, att, work, xo = self.attempt(base, src, rdir, 2, "full", chal_ok, ev, req)
                atts.append(att)

            def inexact(a_):   # a fast build that kept importers of a changed module (EXPERIMENTAL modes)
                return self.cfg.get("build") != "lake" and (a_.get("build") or {}).get("exact") is not True
            if rc in (0, 3) and inexact(atts[-1]):
                # an ACCEPTED / CONDITIONAL from stale importers is provisional, never counted: confirm it with an exact build
                ev({"event": "provisional", "attempt": len(atts), "verdict": VERDICT.get(rc),
                    "why": "EXPERIMENTAL --mode %s kept importers of a changed module; confirming with an exact build" % mode})
                if not req.get("optimistic_only"):
                    rc, att, work, xo = self.attempt(base, src, rdir, len(atts) + 1, "full", chal_ok, ev, req)
                    atts.append(att)
                if rc in (0, 3) and inexact(atts[-1]):
                    res["provisional"] = VERDICT.get(rc)
                    res["trust"] = "none"
                    rc = 2
            elif inexact(atts[-1]):   # a REJECTED / no verdict of a build with stale importers: not a sound verdict either
                res["trust"] = "none"
            # the incremental machinery as a whole is EXPERIMENTAL: none of its ACCEPTED / CONDITIONAL is counted
            if rc in (0, 1, 3):   # rejections too: nothing of the machinery is a sound verdict
                res["provisional"] = VERDICT.get(rc)
                rc = 2
            res["trust"] = "none"
            res["mode"] = mode + " (EXPERIMENTAL incremental)"
            res["attempts"] = atts
            if own and len(atts) == 1 and rc not in (0, 3):
                res["retry_skipped"] = own
            res["exit"] = rc
            res["verdict"] = VERDICT.get(rc, "NO-VERDICT")
            last = atts[-1]
            res["why"] = (last.get("check") or {}).get("reason") or last.get("note") or last.get("outcome")
            if last.get("check"):
                res["basis"] = last["check"].get("basis")
            if xo and os.path.exists(xo):
                res["export"] = xo
            if last.get("export_sha256"):
                res["export_sha256"] = last["export_sha256"]
            if last.get("drift"):
                res["drift"] = last["drift"]
            if "frontier" in last:
                res["frontier"] = last["frontier"]
                self.locate(res["frontier"], os.path.join(work, "proj")
                            if os.path.isfile(os.path.join(rdir, "changed.json")) else src)
                td = self.tool_digest()   # unchanged ledger semantics: the explicit check files only
                res["ledger"] = self.ledger(base.get("frontier"), last["frontier"], base.get("frontier_tool") in (None, td))
                res["frontier_tool"] = td
            elif rc == 0:
                res["ledger"] = self.ledger(base.get("frontier"), []) if base.get("frontier") is not None else None
            res["build_s"] = round(sum((x["build"].get("wall_s") or 0) for x in atts), 3)
            res["export_s"] = round(sum((x.get("export_s") or 0) for x in atts), 3)
            res["check_s"] = round(sum((x.get("check_s") or 0) for x in atts), 3)
            res["total_s"] = round(now() - t_start, 3)
            res["latency_s"] = round(now() - t_arr, 3)
            res["challenge_sha256"] = self.cfg["challenge_sha256"]
            # advance the base: the new tree + plan (+ export, the next warm snapshot) if the build succeeded
            adv = req.get("advance", True) and not last["outcome"].startswith("build") and not inexact(last) and \
                last["outcome"] != "challenge-pin" and (self.cfg.get("build") == "lake" or
                                                        os.path.isfile(os.path.join(work, "log", "plan.jsonl")))
            if req.get("merge"):   # merge-queue semantics: only an ACCEPTED / CONDITIONAL patch enters the base
                adv = adv and rc in (0, 3)
            if self.delta_only and adv:
                # a --delta-only screening daemon never makes a full export, so an advanced base could never get
                # an export of its own tree again (every later request: delta-inconclusive): it never moves its base
                adv = False
                res["base_advance_skipped"] = "serve --delta-only never advances the base (requests are candidates)"
            with self.lock:
                if adv and self.base.get("run") == base.get("run"):
                    lake = self.cfg.get("build") == "lake"
                    # the new base's export is the export of exactly the new tree (xo, made from this
                    # attempt's work/proj) or NONE - never the previous base's export (a delta verdict, an export failure,
                    # delta-only: no export of this tree exists). With no export the next request takes the full export
                    # path (and the warm delta is not used: delta_attempt requires export_of == proj and wd.base == export)
                    fresh = bool(xo and os.path.exists(xo))
                    nproj = None if lake else os.path.join(work, "proj")
                    nsrc = os.path.join(rdir, "src") if lake else os.path.join(work, "proj")
                    nb = {"run": "%05d" % rid, "proj": nproj,
                          "plan": None if lake else os.path.join(work, "log", "plan.jsonl"),
                          "src": nsrc,
                          "export": xo if fresh else None,
                          "export_sha256": last.get("export_sha256") if fresh else None,
                          "export_of": (nproj or nsrc) if fresh else None,
                          "verdict": res["verdict"], "t": now(),
                          "frontier": res.get("frontier", [] if rc == 0 else self.base.get("frontier")),
                          "frontier_tool": res.get("frontier_tool", self.base.get("frontier_tool"))}
                    old = self.base
                    self.base = nb
                    jdump(os.path.join(self.st, "base.json"), nb)
                    res["base_advanced"] = True
                    # old trees are deleted in the background (a Mathlib-size tree takes seconds to delete on ext4)
                    threading.Thread(target=self.gc, args=(old, rid), daemon=True).start()
                else:
                    res["base_advanced"] = False
            self.stats["requests"] += 1
            self.stats[{0: "accepted", 1: "rejected", 3: "conditional"}.get(rc, "no_verdict")] += 1
            jdump(os.path.join(rdir, "result.json"), res)
            self.log(event="verify", id=rid, verdict=res["verdict"], total_s=res["total_s"])
            return res

    def gc(self, old, rid):
        """delete run directories that are neither the base nor among the last keep_runs (disk: reflink trees)"""
        with self.lock:
            runs = sorted(os.listdir(os.path.join(self.st, "runs")))
            keep = set(runs[-self.keep_runs:]) | {self.base.get("run")} | {r for r, n in self.inuse.items() if n > 0}
        for r in runs:
            if r not in keep and r.isdigit() and int(r) < rid:
                d = os.path.join(self.st, "runs", r)
                # never delete a tree a running job may use as its base (it started from it): only older than the
                # previous base
                if old.get("run") == r:
                    continue
                shutil.rmtree(os.path.join(d, "src"), ignore_errors=True)
                for x in os.listdir(d):
                    if x.startswith("a") and os.path.isdir(os.path.join(d, x)):
                        shutil.rmtree(os.path.join(d, x), ignore_errors=True)
                shutil.rmtree(os.path.join(d, "x"), ignore_errors=True)


SVC = None


class Handler(socketserver.StreamRequestHandler):
    def handle(self):
        try:
            line = self.rfile.readline(1 << 26)
            req = json.loads(line)
        except ValueError:
            return self.send({"error": "bad request"})
        op = req.get("op")
        if op == "verify":
            stream = bool(req.get("stream"))

            def ev(e):
                if stream:
                    try:
                        self.send(e)
                    except OSError:
                        pass
            try:
                res = SVC.verify(req, ev)
            except Exception as e:  # noqa: BLE001 - an internal error is never a verdict
                res = {"verdict": "NO-VERDICT", "exit": 2, "why": f"internal error: {e!r}"[:500]}
            res["final"] = True
            self.send(res)
        elif op == "status":
            with SVC.lock:
                self.send({"base": SVC.base, "stats": SVC.stats, "jobs": SVC.jobs, "threads": SVC.threads,
                           "check": SVC.check_kind,
                           "warmd": None if SVC.warmd is None else {"ready": SVC.warmd.is_ready(), "dir": SVC.warmd.d},
                           "warm": [{"dir": w.d, "ready": w.ready(), "snap_is_base": w.snap == SVC.base.get("export"),
                                     "age_s": round(now() - w.t0, 1)} for w in SVC.pool]})
        elif op == "stop":
            self.send({"stopping": True})
            threading.Thread(target=shutdown, daemon=True).start()
        else:
            self.send({"error": f"unknown op {op}"})

    def send(self, obj):
        self.wfile.write((json.dumps(obj) + "\n").encode())
        self.wfile.flush()


class Server(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True
    request_queue_size = 256   # the default listen backlog of 5 drops bursts of concurrent agents (EAGAIN)


SERVER = None


def shutdown():
    SVC.stopping = True
    with SVC.lock:
        for w in SVC.pool:
            w.stop()
        SVC.pool = []
        kids = list(SVC.children)
    for p in kids:   # in-flight requests: terminate their builds / exports / checks (answers become NO-VERDICT)
        SVC.killpg(p)
    if SVC.warmd is not None:
        SVC.warmd.stop()
    SERVER.shutdown()


def cmd_serve(a):
    global SVC, SERVER
    SVC = Service(a)
    sock = os.path.join(SVC.st, "sock")
    if os.path.exists(sock):
        try:
            request(SVC.st, {"op": "status"}, timeout=2)
            sys.exit("fvwork serve: a server is already running on " + sock)
        except OSError:
            os.unlink(sock)
    old = os.umask(0o177)
    SERVER = Server(sock, Handler)
    os.umask(old)
    with open(os.path.join(SVC.st, "server.pid"), "w") as f:
        f.write(str(os.getpid()))
    signal.signal(signal.SIGTERM, lambda *_: threading.Thread(target=shutdown, daemon=True).start())
    threading.Thread(target=SVC.warm_loop, daemon=True).start()
    if SVC.check_kind == "warm" and SVC.base.get("export"):   # started from the main thread (lives as long as the daemon)
        SVC.warmd = WarmCheck(SVC, SVC.base["export"])
    SVC.log(event="serve", threads=SVC.threads, jobs=SVC.jobs, warm=SVC.nwarm, mode=SVC.mode)
    print(json.dumps({"serving": sock, "threads": SVC.threads, "jobs": SVC.jobs, "warm": SVC.nwarm}), flush=True)
    try:
        SERVER.serve_forever()
    finally:
        SVC.stopping = True
        for w in SVC.pool:
            w.stop()
        try:
            os.unlink(sock)
        except OSError:
            pass


def request(state, obj, timeout=None, on_event=None):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    if timeout:
        s.settimeout(timeout)
    s.connect(os.path.join(os.path.realpath(state), "sock"))
    s.sendall((json.dumps(obj) + "\n").encode())
    f = s.makefile("r")
    last = None
    for ln in f:
        o = json.loads(ln)
        if o.get("final") or obj.get("op") != "verify":
            last = o
            break
        if on_event:
            on_event(o)
    s.close()
    if last is None:
        raise OSError("connection closed without an answer")
    return last


def cmd_verify(a):
    req = {"op": "verify", "advance": not a.no_advance, "stream": a.stream, "label": a.label}
    if a.mode:
        req["mode"] = a.mode
    if a.optimistic_only:
        req["optimistic_only"] = True
    if a.drift:
        req["drift"] = True
    if a.merge:
        req["merge"] = True
    for nm, v in (("--tree", a.tree), ("--git", a.git), ("--files", a.files)):   # strict paths: an empty
        if v is not None and (not v or not os.path.exists(v) or os.path.realpath(v) == "/"):   # or unresolvable path or /
            # is a usage error, never the cwd (and never /)
            print(f"fvwork verify: {nm} {v!r} does not exist (no verdict)", file=sys.stderr)
            sys.exit(2)
    if a.tree:
        req["tree"] = os.path.realpath(a.tree)
    elif a.git:
        req["git"], req["rev"] = os.path.realpath(a.git), a.rev
    elif a.files:
        try:
            req["files"] = json.load(open(a.files))
        except (OSError, ValueError) as e:   # an unreadable --files JSON is no verdict: exit 2
            print(f"fvwork verify: --files {a.files}: {e}", file=sys.stderr)
            sys.exit(2)
    else:
        print("fvwork verify: give --tree, --git/--rev or --files", file=sys.stderr)
        sys.exit(2)
    try:
        res = request(a.state, req, on_event=(lambda e: print(json.dumps(e), flush=True)) if a.stream else None)
    except (OSError, ValueError) as e:   # no daemon / a broken answer: exit 2, never 1
        print(json.dumps({"verdict": "NO-VERDICT", "exit": 2, "why": f"fvwork verify: no answer from the daemon: {e}"}), flush=True)
        sys.exit(2)
    print(json.dumps(res), flush=True)
    sys.exit(res.get("exit", 2) if res.get("exit") in (0, 1, 3) else 2)


def cmd_watch(a):
    """editor / terminal loop: poll a working tree, submit it on every change of a .lean / lakefile / manifest file, print
    one verdict line and the compiler messages as `file:line:col: severity: message` (VS Code problem-matcher format)"""
    tree = strict_dir("--tree", a.tree)   # non-empty, existing directory, never /

    def snap():
        out = {}
        for root, dirs, files in os.walk(tree):
            dirs[:] = [d for d in dirs if d not in (".lake", ".git", ".fvwork")]
            for fn in files:
                if fn.endswith(".lean") or fn in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"):
                    p = os.path.join(root, fn)
                    try:
                        st = os.stat(p)
                        out[os.path.relpath(p, tree)] = (st.st_mtime_ns, st.st_size)
                    except OSError:
                        pass
        return out
    last, n = None, 0
    print(f"[fvwork watch] {tree} (every {a.interval}s; Ctrl-C to stop)", flush=True)
    while True:
        cur = snap()
        if cur != last:
            if last is not None or a.initial:
                changed = sorted(k for k in set(cur) | set(last or {}) if cur.get(k) != (last or {}).get(k))
                n += 1
                t0 = now()
                try:
                    r = request(a.state, {"op": "verify", "tree": tree, "advance": True, "label": f"watch#{n}"})
                except OSError as e:
                    r = {"verdict": "NO-VERDICT", "why": f"daemon unavailable: {e}"}
                extra = ""
                if r.get("ledger"):
                    lg = r["ledger"]
                    extra = f" open={lg.get('open')} closed={len(lg.get('closed_since_base') or [])} new={len(lg.get('new_since_base') or [])}"
                print(f"[fvwork watch #{n}] {r.get('verdict')} in {now() - t0:.1f} s{extra} changed={changed[:5]} "
                      f"why={(r.get('why') or '')[:160]}", flush=True)
                for att in (r.get("attempts") or [])[:1]:
                    for d in att.get("diagnostics") or []:
                        mod = d.get("module") or ""
                        for m in d.get("messages") or []:
                            pos = m.get("pos") or {}
                            fn = m.get("fileName") or ""
                            if "/proj/" in fn:   # the daemon's per-request tree -> the user's relative path
                                fn = fn.split("/proj/", 1)[1]
                            if not fn or os.path.isabs(fn):
                                fn = mod.replace(".", "/") + ".lean" if mod else "?"
                            print(f"{fn}:{pos.get('line', 1)}:{pos.get('column', 0) + 1}: {m.get('severity', 'error')}: "
                                  f"{str(m.get('data', '')).splitlines()[0] if m.get('data') else ''}", flush=True)
                for e in (r.get("frontier") or [])[:20]:
                    src = e.get("source") or {}
                    print(f"{src.get('file', '?')}:{src.get('line', 1)}:1: warning: open lemma {e.get('name')}", flush=True)
            last = cur
        time.sleep(a.interval)


def cmd_simple(a, op):
    print(json.dumps(request(a.state, {"op": op}, timeout=30)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    p = sp.add_parser("init")
    p.add_argument("--state", required=True); p.add_argument("--project", required=True)
    p.add_argument("--challenge", required=True); p.add_argument("--challenge-sha256", required=True)
    p.add_argument("--comparator-sha256", required=True, type=hex64,
                   help="(REQUIRED with --challenge-sha256) the caller's sha256 of the comparator "
                        "config (64 hex; else refused, exit 2); recorded and forwarded to bin/fastverify by the cold path")
    p.add_argument("--packages"); p.add_argument("--threads", type=int); p.add_argument("--fv"); p.add_argument("--tc")
    p.add_argument("--items", default=DEFAULT_ITEMS,
                   help="B3 items of the cold run (comma list) or 'auto' = lib/autotune.py's choice minus merge")
    p.add_argument("--adopt", metavar="OUT")
    p.add_argument("--build", default="fast", choices=["fast", "lake"],
                   help="fast = the sound preset's B3 build + incr-build.py + E1 (Lean 4.33.1); lake = the official "
                        "incremental lake build + the release's official exporter (any supported release)")
    p.add_argument("--closure-only", action="store_true",
                   help="rebuild only the import closure of the comparator's solution module (what lake comparator builds)")
    p.add_argument("--no-skip-kernel-tc", action="store_true",
                   help="rebuilt modules keep the build-time kernel check (Mathlib-like code with @[to_dual])")
    p = sp.add_parser("serve")
    p.add_argument("--state", required=True); p.add_argument("--jobs", type=int, default=1)
    p.add_argument("--warm", type=int, default=0,
                   help="pre-warmed Lean-kernel legs kept ready (default 0: warm is experimental and not part of v0.1; "
                        "pass --warm 1 to opt in)")
    p.add_argument("--warm-nice", type=int, default=10)
    p.add_argument("--threads", type=int); p.add_argument("--keep-runs", type=int, default=4)
    p.add_argument("--experimental-incremental", action="store_true",
                   help="EXPERIMENTAL (not part of the default sound path): use the incremental machinery (incremental builds, "
                        "--mode, --check frontier / warm, --build lake, --copy-mode, the memo) instead of the default COLD "
                        "sound path (bin/fastverify --preset sound on every submitted tree); its ACCEPTED / CONDITIONAL "
                        "is never counted (NO-VERDICT, \"provisional\")")
    p.add_argument("--mode", default="full", choices=["full", "optimistic", "interface"],
                   help="full (default) = EXACT: every reverse dependency of every changed module is rebuilt, as a fresh build "
                        "would; optimistic / interface = EXPERIMENTAL fast paths that keep importers: their "
                        "ACCEPTED is only provisional (confirmed by an exact build; never counted on its own)")
    p.add_argument("--job-threads", type=int, help="threads of one request (default: threads / jobs)")
    p.add_argument("--check", default="sound", choices=["sound", "frontier", "warm"],
                   help="sound = check/sound/check-sound-svc.sh (ACCEPTED/REJECTED); frontier = check/frontier/"
                        "check-frontier.sh (CONDITIONAL modulo the reported sorry frontier, exit 3; never ACCEPTED "
                        "unless there is no sorry at all); warm = check/warm/fvcheckd.py sidecar (fallback: sound)")
    p.add_argument("--allowed", help="(frontier) file of lemma names the frontier may contain (others -> REJECTED)")
    p.add_argument("--pinned", metavar="DIR",
                   help="(frontier) a frontier pin (tools/frontier/frontier.py pin): the open lemmas AND their statements "
                        "are fixed - an agent cannot restate an open lemma (goalposts pinned)")
    p.add_argument("--expdiff", default=os.environ.get("FVWORK_EXPDIFF"),
                   help="expdiff binary (tools/compress/expdiff/build.sh): statement-drift reports")
    p.add_argument("--drift", action="store_true", help="drift report on every request (else only with \"drift\": true)")
    p.add_argument("--copy-mode", default="reflink", choices=["reflink", "hardlink", "farm"],
                   help="per-request tree copy: reflink (XFS/btrfs copy-on-write, else a full copy; default) or hardlink "
                        "(fast on ext4, but the project's elaboration-time code can rewrite shared base files IN PLACE: "
                        "trusted repositories only, and refused with --check warm, whose delta check trusts the stored base "
                        "(a rewritten base can turn into a false ACCEPTED there); with a whole-export check a rewritten base "
                        "only changes what the next export contains, and that export is checked in full) or farm "
                        "(sparse CANDIDATE "
                        "requests get a symlink farm over the fixed base - no tree copy at all, for RH-size trees with "
                        "millions of build files; the base itself is read-only in every build sandbox; other requests: "
                        "reflink)")
    p.add_argument("--slow-lane", type=float, default=120.0,
                   help="a request running longer than this many seconds stops counting against --jobs (0 = off)")
    p.add_argument("--guard", metavar="SPEC",
                   help="resource limits for the untrusted build and export of every request (tools/guard/fvguard.py), e.g. "
                        "'mem=64G,procs=4096,wall=1800,out=64M' (a violation = NO-VERDICT); default 'wall=3600'; 'none' = off")
    p.add_argument("--delta-only", action="store_true",
                   help="--check warm screening daemons: when the warm DELTA check is not decisive, answer NO VERDICT "
                        "(outcome delta-inconclusive, with the judge's reason) instead of a full export + whole-export check "
                        "(a node-hour on RH-size bases); such a daemon never advances its base (every request is a candidate)")
    p.add_argument("--warm-full-max", type=float, default=4.0, metavar="GB",
                   help="--check warm: largest whole export (GB) judged by the warm sidecar's check_full; larger ones (a "
                        "non-decisive delta on an RH-size base) go to the unchanged sound check, so a timed-out whole-export "
                        "query cannot kill the sidecar's kernel legs (default 4)")
    p.add_argument("--no-hide", action="store_true",
                   help="do not pass the release's published no-expose hide list (check/sound/hide/) to the check")
    p.add_argument("--pins", metavar="FILE",
                   help="pins file of the trusted check built from ANOTHER official release (check-sound v3, e.g. "
                        "FASTVERIFY/check/sound/pins-437.env for Lean 4.37.0-rc1 projects): passed to the check script as "
                        "--pins; the 4.36 pre-warmed legs are then off; part of the --reuse-identical memo key")
    p.add_argument("--reuse-identical", action="store_true",
                   help="re-report the trusted check's earlier verdict for a BYTE-IDENTICAL export (same challenge export, "
                        "comparator config, pinned binaries) instead of re-running it (default off)")
    p = sp.add_parser("verify")
    p.add_argument("--state", required=True); p.add_argument("--tree"); p.add_argument("--git"); p.add_argument("--rev")
    p.add_argument("--files"); p.add_argument("--no-advance", action="store_true"); p.add_argument("--stream", action="store_true")
    p.add_argument("--label"); p.add_argument("--mode", choices=["full", "optimistic", "interface"],
                                              help="per request; optimistic / interface are EXPERIMENTAL (see serve --mode)")
    p.add_argument("--optimistic-only", action="store_true",
                   help="no full-cone retry after a non-accept (candidate proofs of a fixed statement)")
    p.add_argument("--drift", action="store_true", help="statement-drift report vs the base (needs serve --expdiff)")
    p.add_argument("--merge", action="store_true",
                   help="merge-queue semantics: judged against the base current when its turn comes, enters the base "
                        "only if ACCEPTED / CONDITIONAL (merges are serialized; candidates with --no-advance run concurrently)")
    p = sp.add_parser("watch", help="poll a working tree and verify it on every change (editor / terminal loop)")
    p.add_argument("--state", required=True); p.add_argument("--tree", required=True)
    p.add_argument("--interval", type=float, default=1.0)
    p.add_argument("--initial", action="store_true", help="also verify the tree once at start")
    for c in ("status", "stop"):
        p = sp.add_parser(c); p.add_argument("--state", required=True)
    a = ap.parse_args()
    if a.cmd == "init":
        cmd_init(a)
    elif a.cmd == "serve":
        cmd_serve(a)
    elif a.cmd == "verify":
        cmd_verify(a)
    elif a.cmd == "watch":
        cmd_watch(a)
    else:
        cmd_simple(a, a.cmd)


if __name__ == "__main__":
    main()

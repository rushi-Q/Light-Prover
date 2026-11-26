#!/usr/bin/python3 -I
"""batchverify.py — SOUND per-attempt verdicts for MANY independent proof attempts in one batch.

    batchverify.py --pset PSET --attempts DIR --out OUT --challenge-sha256 HEX [--threads N] [--jobs J]
                   [--packages WS] [--toolchain TC] [--fv FASTVERIFY] [--skip-kernel-tc] [--no-confirm]

PSET  = a problem set: PSET/challenge.export (the OFFICIAL export of the problem set's challenge file: every problem's
        statement := sorry, produced by the official Lean + official exporter), PSET/comparator.json (permitted_axioms;
        its theorem_names = all problems).
DIR   = one file per attempt, DIR/<theorem>.lean: a complete Lean module that must declare `theorem <theorem>` (the
        problem's name in the challenge). At most one attempt per problem per batch.

What it does (all of it UNTRUSTED orchestration around the unchanged TRUSTED check `check/sound/check-sound.sh`):
  1. build: every attempt is compiled as its own module `Attempt.<theorem>` by the OFFICIAL lean (or --toolchain) in
     bwrap (read-only /, home hidden, no network, env cleared), J at a time, against the trusted packages only (an attempt
     cannot import another attempt), each process writing only into a private directory; with --snapshot-cache the
     official lean's `--incr-header-save` snapshot of `import Mathlib` replaces the import of attempts with exactly that
     header (`--incr-load`); a compile timeout gives NO-VERDICT; a failure under a speed-up without a positional error of
     the attempt is re-compiled plainly (--confirm-failures);
  2. export: the native exporter E1 (`export/export.sh`, closure guard) with exactly the attempt modules of the current
     candidate set S as root modules, restricted to the targets Lake's comparator derives for S (builtins, the theorems
     of S, the permitted axioms, the kernel primitives, the definitions);
  3. check: `check-sound.sh EXPORT PSET/challenge.export CFG_S` where CFG_S = PSET/comparator.json with
     theorem_names := S (everything else unchanged);
  4. verdicts: every theorem of an ACCEPTED check is ACCEPTED; after a REJECTED check (or a declined export) the
     candidates are split - theorems named by the check's error lines, holders of an illegal axiom's or a duplicate
     constant's name (grepped in their .olean) go alone, else a k-ary split - and re-checked in parallel rounds; a theorem
     is REJECTED only when its own singleton check rejected it (or its attempt does not compile / does not declare it);
     anything else = NO-VERDICT. (--root-module: the older path with one root module importing every compiled attempt.)
  5. credit: an accepted theorem t is credited to the attempt file t.lean only if Attempt.t itself declares t (trivial for a
     singleton check or when no other module of the set contains the name; else the export of Attempt.t alone with
     target t must succeed) - otherwise attempt A proving B's theorem would earn B's attempt an ACCEPTED.
  For rewards, NO-VERDICT must be counted like REJECTED.

Why an ACCEPTED here is sound (the only verdict logic, function `verdicts`): a theorem t is reported ACCEPTED iff
check-sound.sh exited 0 on (an export, the pinned official challenge export, a config whose theorem_names contain t and
whose other fields equal PSET/comparator.json); t is only ever a candidate if the attempt file <t>.lean is in the batch. check-sound.sh exit 0 = the official judge code (compareAt, checkAxioms)
found t's statement equal to the challenge's and only permitted axioms in t's closure, and the official 4.36 kernel and
gruszka accepted every declaration of the export (S1 (2)-(4)); S1 (1) = the challenge export's sha256 is checked
against --challenge-sha256 before every check. Build, export, the splitting and the log / .olean hints can only
produce a reject or no verdict for some attempt, never an accept of a theorem that the trusted check
did not accept in a check whose config listed it.
"""
import argparse, concurrent.futures as cf, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.realpath(__file__))
BWRAP = "/usr/bin/bwrap"
GUARD_EXIT = 125       # an attempt's compile ended by a resource limit (tools/guard): NO-VERDICT, never a verdict
# host resource failures (as build/sched.py): with --limits an attempt that ends with one of these is a resource
# failure (e.g. RLIMIT_DATA hit inside lean), not a compile error -> NO-VERDICT instead of REJECTED
RES_FAIL = ('Cannot allocate memory', 'out of memory', 'failed to create thread', 'std::bad_alloc',
            'Resource temporarily unavailable', 'Too many open files', 'No space left on device')


def load_guard():
    sys.path.insert(0, os.path.join(HERE, "guard"))
    try:
        import fvguard
    finally:
        sys.path.pop(0)
    return fvguard
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def reset_child_signals():
    """a caller that ignores SIGCHLD makes every child's exit status read as 0 (env -i keeps the
    disposition): restore the default and clear the inherited signal mask before anything starts"""
    import signal as _sg
    if hasattr(_sg, "SIGCHLD"):
        _sg.signal(_sg.SIGCHLD, _sg.SIG_DFL)
    try:
        _sg.pthread_sigmask(_sg.SIG_SETMASK, set())
    except (AttributeError, OSError, ValueError):
        pass


# an attempt file DIR/<theorem>.lean may name a NAMESPACED theorem (QACheck.addZero): dot-separated plain
# identifier components (no «...»), compiled as the module Attempt.<theorem> = PROJ/Attempt/<c1>/.../<cn>.lean
QNAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 24), b""):
            h.update(b)
    return h.hexdigest()


def refuse(msg):
    """a job-level refusal is no verdict: exit 2 (SystemExit with a string would exit 1)"""
    print(msg, file=sys.stderr, flush=True)
    raise SystemExit(2)


def private_pset(a):
    """copy PSET/challenge.export and PSET/comparator.json ONCE into a private directory (0700, on
    OUT's filesystem, removed at exit), verify the copy against --challenge-sha256, and point a.pset at it: the judge
    selection, the cross-version gate and every check then read exactly the pinned bytes"""
    import atexit
    base = os.path.dirname(os.path.realpath(a.out)) or "."
    try:
        os.makedirs(base, exist_ok=True)   # a fresh nested output hierarchy is created
        priv = tempfile.mkdtemp(prefix=".batchverify-pset.", dir=base)
    except OSError as e:
        refuse(f"batchverify: cannot create the private problem-set copy next to {a.out} ({e}): refused (no verdict)")
    atexit.register(shutil.rmtree, priv, True)
    for name in ("challenge.export", "comparator.json"):
        src, dst = os.path.join(a.pset, name), os.path.join(priv, name)
        cp = subprocess.run(["cp", "--reflink=auto", "--", src, dst], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        if cp.returncode != 0 or not os.path.isfile(dst) or os.path.islink(dst):
            refuse(f"batchverify: {src}: cannot make the private copy ({cp.stderr.decode('utf-8', 'replace').strip()[:160]}): "
                   "refused (no verdict)")
        os.chmod(dst, 0o444)
    if sha256_file(os.path.join(priv, "challenge.export")) != a.challenge_sha256:
        refuse("batchverify: challenge export sha256 != --challenge-sha256: refuse (no verdict)")
    a.pset_given = os.path.realpath(a.pset)
    a.pset = priv


def pset_judge(a):
    """the problem set's OWN release decides the judge, as bin/fastverify --preset sound:
    a Lean >= 4.37 problem set (meta line of PSET/challenge.export, read with the gate's strict parser and release table)
    gets the pins*.env whose TC_VERSION names that release; an explicit --pins of another release, or no installed judge
    of that release, is refused (exit 2). Earlier releases keep the given / default judge (the gate admits them)."""
    import importlib.util
    fv = os.path.realpath(a.fv)
    try:
        spec = importlib.util.spec_from_file_location("bv_xvcheck_sel", os.path.join(fv, "check", "xversion", "xvcheck.py"))
        xv = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(xv)
        with open(os.path.join(a.pset, "challenge.export"), "rb") as f:
            ver, gh, _fmt = xv.parse_meta_line(f.readline(1 << 20))
        newer = tuple(int(x) for x in ver.split("-")[0].split(".")) >= (4, 37, 0)
    except Exception as e:   # noqa: BLE001 - unreadable: a job refusal, never the default judge
        refuse(f"batchverify: the problem set's challenge export release cannot be read ({str(e)[:160]}): refused (no verdict)")
    want = "leanprover/lean4:v" + ver
    if getattr(a, "toolchain", None) is None:   # the compiler follows the problem set's release
        try:
            tcs = json.load(open(os.path.join(fv, "config", "components.json"))).get("lean_toolchains") or {}
        except (OSError, ValueError):
            tcs = {}
        a.toolchain = (tcs.get(want) or {}).get("prefix")
        if not a.toolchain or not os.path.isdir(a.toolchain):
            refuse(f"batchverify: the problem set is from Lean {ver} and no compiler of that release is registered "
                   f"(config/components.json lean_toolchains {want}); give --toolchain explicitly: refused (no verdict)")
    if not newer:
        return
    d = os.path.join(fv, "check", "sound")

    def tcv(p):
        try:
            return next((ln.split("=", 1)[1].strip() for ln in open(p, encoding="utf-8") if ln.startswith("TC_VERSION=")),
                        "leanprover/lean4:v4.36.0")
        except OSError:
            return None
    if a.pins:
        pp = os.path.realpath(a.pins if os.path.isabs(a.pins) else os.path.join(fv, a.pins))
        if tcv(pp) != want:
            refuse(f"batchverify: the problem set is from Lean {ver} but --pins {a.pins} is the judge of {tcv(pp)}: a "
                   f"{ver} problem set is judged only by its own release's judge (refused, no verdict)")
        return
    import glob as _glob
    for f in sorted(_glob.glob(os.path.join(d, "pins-*.env"))):
        if tcv(f) == want:
            a.pins = f
            return
    refuse(f"batchverify: the problem set is from Lean {ver} and no judge of that release is installed "
           f"(check/sound/pins-*.env with TC_VERSION={want}); the 4.36 judge never judges it (refused, no verdict)")


def target_missing(text, t):
    """the exporter's text says that the target t is missing / unknown - matched with every
    spelling of t's own name removed first, so a theorem NAMED e.g. missing_case never decides a rejection"""
    s = text or ""
    for x in sorted({t, t.replace(".", "/"), t.rsplit(".", 1)[-1]}, key=len, reverse=True):
        if x:
            s = s.replace(x, "<t>")
    return re.search(r"missing|unknown constant|not found", s) is not None


def export_declares_theorem(path, t):
    """does the NDJSON export at `path` contain a THEOREM record whose name is the atomic name t
    (t matches NAME_RE: one string component, no escapes)? Fail-closed: only canonical compact records are recognised (a
    name record '{"in":K,"str":{"pre":0,"str":"t"}}' and, after it, a '{"thm":{...,"name":K,...}}' record, both parsed with
    json; the export format defines every index before its use); anything unusual, an unreadable file, an empty or
    meta-only export -> False (= not owned). Never raises."""
    if not isinstance(t, str) or not QNAME_RE.fullmatch(t):   # no trailing line feed
        return False
    # a namespaced t = c1. ... .cn: the name record chain from the root (pre 0) through c1, ..., cn
    comps = t.split(".")
    cpats = {('"str":"%s"' % c).encode() for c in comps}
    depth = {0: 0}   # name index -> number of leading components of t it spells (0 = the anonymous root)
    pats = {}
    try:
        with open(path, "rb") as f:
            for ln in f:
                if ln.startswith(b'{"in":'):
                    if any(pat in ln for pat in cpats):
                        try:
                            o = json.loads(ln)
                        except ValueError:
                            continue
                        s = o.get("str") if isinstance(o, dict) else None
                        k = o.get("in") if isinstance(o, dict) else None
                        d = depth.get(s.get("pre")) if isinstance(s, dict) and type(s.get("pre")) is int else None
                        if d is not None and d < len(comps) and s.get("str") == comps[d] and type(k) is int and k not in depth:
                            depth[k] = d + 1
                            if d + 1 == len(comps):
                                pats[k] = b'"name":%d' % k
                elif pats and ln.startswith(b'{"thm":'):
                    for k, pb in pats.items():
                        if pb in ln:
                            try:
                                o = json.loads(ln)
                            except ValueError:
                                continue
                            th = o.get("thm") if isinstance(o, dict) else None
                            if isinstance(th, dict) and type(th.get("name")) is int and th["name"] == k:
                                return True
    except OSError:
        return None   # unreadable is not "absent": the caller gives no verdict
    return False


# top-level directories an untrusted sandbox still sees (system dirs, pseudo filesystems, and the ones
# the sandbox already replaces by a tmpfs); EVERY other top-level directory (/scratch, /data, /mnt, /opt, ...: service state
# dirs with their sockets / FIFOs, other batches' and tenants' files) is hidden behind an empty tmpfs (toplevel_masks)
SBX_KEEP = frozenset(("bin", "sbin", "lib", "lib32", "lib64", "libx32", "usr", "etc", "dev", "proc", "sys", "nix", "gnu",
                      "home", "root", "tmp", "run", "var"))


def toplevel_dirs():
    return ["/" + d for d in sorted(os.listdir("/"))
            if d not in SBX_KEEP and os.path.isdir("/" + d) and not os.path.islink("/" + d)]


def toplevel_masks():
    """bwrap args hiding every non-system top-level dir (pair with toplevel_remount_ro() AFTER the binds)"""
    return [x for d in toplevel_dirs() for x in ("--tmpfs", d)]


def toplevel_remount_ro(extra=()):
    """the masks read-only again after the binds (only visibility changes: a write there fails with EROFS as before)"""
    return [x for d in toplevel_dirs() + list(extra) for x in ("--remount-ro", d)]


def rm_tree(p):
    """remove the directory tree p of ANY depth and with any modes inside, never raising: an
    untrusted compile can leave a tree ~1000+ levels deep in its private dir, and shutil.rmtree recurses once per level
    (RecursionError, which ignore_errors does not catch); GNU rm / chmod (fts, iterative) take over"""
    try:
        shutil.rmtree(p)
        return
    except FileNotFoundError:
        return
    except Exception:  # noqa: BLE001 - RecursionError, PermissionError (a mode-000 subdir), ...
        pass
    env = {"PATH": "/usr/bin:/bin", "LANG": "C"}
    for cmd in (["/bin/chmod", "-R", "u+rwx", "--", p], ["/bin/rm", "-rf", "--one-file-system", "--", p]):
        try:
            subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env,
                           timeout=900)
        except Exception:  # noqa: BLE001 - best effort
            pass


def sandbox(tc, ws, rw, ro=(), env=None, chdir="/", mask=()):
    """the untrusted compile sandbox: read-only /, the S4 masks (/home /root /run /tmp /var + toplevel_masks()), then an
    empty tmpfs over every directory in `mask` (the caller's state / batch dirs), THEN the binds (toolchain,
    packages, `ro`, `rw`): only what is bound explicitly is visible below a masked directory."""
    a = [BWRAP, "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp",
         "--dir", "/tmp/home", "--tmpfs", "/run", "--tmpfs", "/var"] + toplevel_masks()
    # (a directory below /dev or /proc, e.g. an export dir in /dev/shm, is never visible: --dev / --proc replace them)
    mask = [p for p in mask if not (p + "/").startswith(("/dev/", "/proc/"))]
    # parents first, a mask inside another one dropped (it is hidden already; remounting it would fail)
    mask = [p for i, p in enumerate(sorted(set(mask), key=len))
            if not any(p != q and p.startswith(q.rstrip("/") + "/") for q in sorted(set(mask), key=len)[:i])]
    for p in mask:
        a += ["--tmpfs", p]
    a += ["--dev", "/dev", "--proc", "/proc", "--clearenv", "--ro-bind", tc, tc, "--ro-bind", ws, ws]
    for p in ro:
        a += ["--ro-bind", p, p]
    for p in rw:
        a += ["--bind", p, p]
    a += toplevel_remount_ro(mask)
    e = {"PATH": f"{tc}/bin:/usr/bin:/bin", "HOME": "/tmp/home", "LANG": "C.UTF-8"}
    e.update(env or {})
    for k, v in e.items():
        a += ["--setenv", k, v]
    return a + ["--unshare-all", "--die-with-parent", "--new-session", "--chdir", chdir, "--"]


class Batch:
    def __init__(self, a):
        self.a = a
        self._export_id = os.urandom(8).hex()      # this batch's export file names
        self.pins = None
        if getattr(a, "pins", None):      # as bin/fastverify --pins: a pins*.env of this package's check/sound/
            d = os.path.realpath(os.path.join(a.fv, "check", "sound"))
            pp = os.path.realpath(a.pins if os.path.isabs(a.pins) else os.path.join(a.fv, a.pins))
            if os.path.dirname(pp) != d or not os.path.basename(pp).startswith("pins") or not pp.endswith(".env") \
                    or not os.path.isfile(pp):
                refuse(f"batchverify: --pins {a.pins}: must name a pins*.env file in {d}")
            self.pins = None if pp == os.path.join(d, "pins.env") else pp
        self.out = os.path.realpath(a.out)
        os.makedirs(self.out, mode=0o700, exist_ok=False)
        os.chmod(self.out, 0o700)   # the batch's own files (per-check configs, exports) are private
        if os.stat(self.out).st_mode & 0o077:
            refuse(f"batchverify: {self.out} cannot be made private (0700): refused (no verdict)")
        self.proj = os.path.join(self.out, "proj")
        self.lib = os.path.join(self.proj, "build", "lib", "lean")
        os.makedirs(os.path.join(self.lib, "Attempt"))
        os.makedirs(os.path.join(self.proj, "Attempt"))
        self.logd = os.path.join(self.out, "log")
        os.makedirs(self.logd)
        self.privd = os.path.join(self.out, "priv")
        os.makedirs(self.privd)
        self.ws_pk = os.path.join(os.path.realpath(a.packages), ".lake", "packages")
        self.tc = os.path.realpath(a.toolchain)
        self.lp_ws = ":".join([os.path.join(self.ws_pk, d, ".lake", "build", "lib", "lean")
                               for d in sorted(os.listdir(self.ws_pk))])
        self.lp = self.lp_ws + ":" + self.lib   # export / root module; attempts see only the trusted packages
        self.fv = os.path.realpath(a.fv)
        self.cfg = json.load(open(os.path.join(a.pset, "comparator.json")))
        self.chx = os.path.realpath(os.path.join(a.pset, "challenge.export"))
        self.events = []
        import threading
        self.lock = threading.Lock()
        import ast   # the package's own PRIMITIVES list (lib/fastverify.py), so that the targets stay in sync
        tree = ast.parse(open(os.path.join(self.fv, "lib", "fastverify.py")).read())
        self.primitives = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
                               and any(getattr(t, "id", None) == "PRIMITIVES" for t in n.targets))
        self.t0 = time.time()
        self.res = {"attempts": {}, "checks": [], "exports": [], "build": {}}
        self.ncheck = 0
        # --limits (default off): per-attempt resource limits of the compile (tools/guard/fvguard.py); a limit hit
        # ends the attempt's sandbox and gives NO-VERDICT (availability only: it can never produce an ACCEPTED)
        self.guard = self.limits = None
        if getattr(a, "limits", None):
            self.guard = load_guard()
            self.limits = self.guard.Limits.parse(a.limits) if isinstance(a.limits, str) else a.limits

    def ev(self, **k):
        k["t"] = round(time.time() - self.t0, 3)
        with self.lock:
            self.events.append(k)
            print(json.dumps(k), flush=True)

    def sandbox_masks(self):
        """directories hidden (empty tmpfs) in every compile sandbox of this batch before its
        own binds: the batch dir (every attempt's source, .olean, log, export, config) and the export dir"""
        return [self.out] + ([os.path.realpath(self.a.export_dir)] if getattr(self.a, "export_dir", None) else [])

    # ------------------------------------------------------------------ build
    def compile(self, mod, src, extra=(), plain=False):
        rel = mod.replace(".", "/")
        dst = os.path.join(self.proj, rel + ".lean")
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(src, dst) if src else None
        ol = os.path.join(self.lib, rel + ".olean")
        il = os.path.join(self.lib, rel + ".ilean")
        os.makedirs(os.path.dirname(ol), exist_ok=True)
        # each lean process writes only into its own private directory (the outputs are moved into the shared lib dir
        # after it exited), so one attempt's elaboration-time code (or an `initialize` run when the root imports it)
        # cannot write another attempt's .olean
        priv = tempfile.mkdtemp(prefix="out.", dir=self.privd)
        pol, pil = os.path.join(priv, "m.olean"), os.path.join(priv, "m.ilean")
        opts = ["-Ddebug.skipKernelTC=true"] if self.a.skip_kernel_tc and not plain else []
        # an attempt sees only its OWN source file (the batch dir is masked: no other attempt's source,
        # .olean, log or export is visible); a root module (--root-module) also needs the attempts' .olean files it imports
        ro = [dst] + ([self.lib] if mod.startswith("Batch") else [])
        if not plain and getattr(self, "snap", None) and src and self.header_of(src) == self.snap_header:
            # UNTRUSTED speed-up: the official lean's header snapshot (--incr-header-save of a file with exactly this
            # header) replaces the import; the .olean was byte-identical to a plain compile in our A/B test; the trusted
            # check re-establishes everything from the export anyway
            opts.append("--incr-load=" + self.snap)
            ro.append(os.path.dirname(self.snap))
        # an attempt is compiled against the trusted packages only (it cannot import another attempt's module)
        lp = self.lp if mod.startswith("Batch") else self.lp_ws
        inner = self.limits.inner_prefix() if self.limits and not mod.startswith("Batch") else []
        argv = sandbox(self.tc, self.ws_pk, rw=[priv], ro=ro, env={"LEAN_PATH": lp},
                       chdir=self.proj, mask=self.sandbox_masks()) + inner + [os.path.join(self.tc, "bin", "lean"), *opts, *extra, "-o", pol, "-i", pil, dst]
        t = time.time()
        if self.limits and not mod.startswith("Batch"):
            p = self.guarded(argv, priv)
        else:
            try:
                p = subprocess.run(argv, capture_output=True, text=True, env={}, timeout=self.a.attempt_timeout)
            except subprocess.TimeoutExpired as e:   # bwrap --die-with-parent: the sandbox dies with the killed process
                p = subprocess.CompletedProcess(argv, 124, (e.stdout or b"").decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or ""),
                                                f"batchverify: compile timeout after {self.a.attempt_timeout} s")
            if p.returncode in (128 + 9, -9):   # SIGKILL (bwrap reports 128+sig): lean never kills itself - an OOM / cgroup
                # kill of the host, not a compile error -> no verdict (before: a plain re-compile, then REJECTED)
                p = subprocess.CompletedProcess(argv, GUARD_EXIT, p.stdout, p.stderr + "\nbatchverify: the compile was killed "
                                                "(SIGKILL: out of memory / cgroup limit of the host) - no verdict")
        rc = p.returncode
        if rc == 1 and not (p.stdout or "").strip() and (p.stderr or "").startswith("bwrap: "):
            # the SANDBOX did not start (bwrap's own error: a bind source missing, no user namespace,
            # ...): the attempt was never compiled -> no verdict (never REJECTED). lean reports compile errors on stdout.
            rc = GUARD_EXIT
            p = subprocess.CompletedProcess(argv, rc, p.stdout, p.stderr + "\nbatchverify: sandbox start failure: "
                                            "the attempt was not compiled (no verdict)")
        if rc == 0:
            try:
                import stat as _st
                for x in (pol, pil):   # only regular files written by the process (no symlinks / FIFOs it left behind)
                    if not _st.S_ISREG(os.lstat(x).st_mode):
                        raise OSError(f"{os.path.basename(x)} is not a regular file")
                os.replace(pol, ol)
                os.replace(pil, il)
            except OSError as e:
                rc, p.stderr = 2, p.stderr + f"\nbatchverify: output missing or not a regular file ({e})"
        rm_tree(priv)   # depth-safe: an attempt's deep tree there can never raise out of the batch
        with open(os.path.join(self.logd, mod + ".build.log"), "w") as f:
            f.write(p.stdout + p.stderr)
        return rc, round(time.time() - t, 3), p.stdout + p.stderr

    def guarded(self, argv, priv):
        """the compile under tools/guard: wall = min(--attempt-timeout, limits.wall); rlimits + the tree watchdog
        (memory incl. the sandbox's private tmpfs, processes, threads, output, bytes written into the private output
        dir). -> CompletedProcess-like: rc 124 = timeout (as before), GUARD_EXIT = another limit (NO-VERDICT), else the
        lean's own status; with limits, a failure that reports a host resource error is GUARD_EXIT too."""
        g, L = self.guard, self.limits
        lim = g.Limits(**L.__dict__)
        lim.wall = min(x for x in (L.wall, self.a.attempt_timeout) if x) if (L.wall or self.a.attempt_timeout) else None
        r = g.run(argv, lim, env={}, disk=[(priv, L.disk)] if L.disk or L.disk_files else ())
        out, err = r.stdout, r.stderr
        if r.violation == "wall":
            rc = 124
            err += f"\nbatchverify: compile timeout after {lim.wall} s (tools/guard)"
        elif r.violation:
            rc = GUARD_EXIT
            err += f"\nbatchverify: resource limit: {r.detail} (tools/guard; no verdict)"
        else:
            rc = r.exit_status
            # a lean killed by a signal inside the sandbox: bwrap reports 128+sig. Under limits SIGKILL / SIGXCPU / SIGXFSZ
            # are resource ends (RLIMIT_CPU / RLIMIT_FSIZE / an OOM kill), never a compile result
            if rc in (128 + 9, 128 + 24, 128 + 25, -9, -24, -25):
                err += f"\nbatchverify: the compile was killed by signal {rc - 128 if rc > 0 else -rc} under --limits (no verdict)"
                rc = GUARD_EXIT
            elif rc not in (0, None) and any(x in out or x in err for x in RES_FAIL):
                rc = GUARD_EXIT
                err += "\nbatchverify: the compile failed with a host resource error under --limits (no verdict)"
        with self.lock:
            self.res.setdefault("guard", []).append({"rc": rc, "violation": r.violation, "detail": r.detail,
                                                     "peak": r.peak, "wall_s": r.wall_s})
        return subprocess.CompletedProcess(argv, rc, out, err)

    @staticmethod
    def header_of(path):
        """the import lines of a module (leading imports after blank lines / line comments), as a tuple"""
        imps = []
        for ln in open(path, encoding="utf-8", errors="replace"):
            t = ln.strip()
            if not t or t.startswith("--"):
                continue
            if t.startswith("import "):
                imps.append(" ".join(t.split()))
                continue
            break
        return tuple(imps)

    def make_snapshot(self):
        """one header snapshot of `import Mathlib` (official lean --incr-header-save), shared by all attempts;
        --snapshot-cache DIR keeps it across batches (a verifier service builds it once). The snapshot is made in a
        fresh directory and renamed into place (DIR/<key>/), so concurrent batches never see a partial file."""
        base = os.path.realpath(self.a.snapshot_cache) if self.a.snapshot_cache else os.path.join(self.out, "snap")
        os.makedirs(base, exist_ok=True)
        hdr = self.a.snapshot_header + "\n"
        key = hashlib.sha256((hdr + self.tc + self.ws_pk).encode()).hexdigest()[:16]
        d = os.path.join(base, key)
        if os.path.isfile(os.path.join(d, "hdr.snap")):
            self.snap, self.snap_header = os.path.join(d, "hdr.snap"), self.header_of(os.path.join(d, "Hdr.lean"))
            self.res["build"]["snapshot_s"] = 0.0
            self.ev(stage="header-snapshot", reused=d)
            return
        tmp = tempfile.mkdtemp(prefix="tmp.", dir=base)
        src = os.path.join(tmp, "Hdr.lean")
        with open(src, "w") as f:
            f.write(hdr)
        argv = sandbox(self.tc, self.ws_pk, rw=[tmp], env={"LEAN_PATH": self.lp_ws}, chdir=tmp, mask=self.sandbox_masks()) + [
            os.path.join(self.tc, "bin", "lean"), "--incr-header-save=" + os.path.join(tmp, "hdr.snap"), src]
        t = time.time()
        p = subprocess.run(argv, capture_output=True, text=True, env={})
        sec = round(time.time() - t, 3)
        self.res["build"]["snapshot_s"] = sec
        self.ev(stage="header-snapshot", exit=p.returncode, s=sec)
        if p.returncode != 0 or not os.path.isfile(os.path.join(tmp, "hdr.snap")):
            shutil.rmtree(tmp, ignore_errors=True)
            return
        # the snapshot file name is recorded inside it (deps file) -> keep the name, rename the directory
        try:
            os.rename(tmp, d)
        except OSError:          # another batch was faster: use its snapshot
            shutil.rmtree(tmp, ignore_errors=True)
        if os.path.isfile(os.path.join(d, "hdr.snap")):
            self.snap, self.snap_header = os.path.join(d, "hdr.snap"), self.header_of(os.path.join(d, "Hdr.lean"))

    def needs_confirm(self, n, out):
        """--confirm-failures: all = every failure under a speed-up is re-compiled plainly; errors (default) = only
        failures that do not report an error at a source position of the attempt (an elaboration error of the attempt's
        own code under the header snapshot is taken as is: the snapshot gave byte-identical .olean files in every A/B and
        never changed a verdict on 108 honest attempts); with --skip-kernel-tc every failure is confirmed (skip-kernel-tc
        changes elaboration); none = never."""
        if not (getattr(self, "snap", None) or self.a.skip_kernel_tc) or self.a.confirm_failures == "none":
            return False
        if self.a.confirm_failures == "all" or self.a.skip_kernel_tc:
            return True
        return re.search(r"Attempt/" + re.escape(n.replace(".", "/")) + r"\.lean:\d+:\d+: error", out) is None

    def build_attempts(self, names):
        t = time.time()
        if self.a.snapshot_header:
            self.make_snapshot()
        ok = []

        def host_stop(rc, out, own=None):
            # lean stopped by a signal (bwrap reports 128+N; e.g. SIGXFSZ = 153 under a file-size
            # limit) or a resource error is not a compile error of the attempt: no verdict, never REJECTED
            if rc in (0, 124, GUARD_EXIT):
                return rc, out
            if rc < 0 or rc > 128 or re.search(r"File size limit exceeded|File too large|EFBIG|CPU time limit exceeded", out):
                return GUARD_EXIT, out + f"\nbatchverify: the compile was stopped by a signal / resource limit (exit {rc}) - no verdict"
            # a REJECTED needs a compile that ran and reported a source error of the attempt (lean's
            # 'FILE:LINE:COL: error'); a compiler that did not start (bwrap / exec failure, exit 126 / 127), a missing output
            # file or any other failure is no verdict
            # and only a diagnostic POSITIONED IN THE ATTEMPT'S OWN FILE, with no dependency-load /
            # damaged-installation error (a broken installed .olean is reported at the attempt's import line).
            # An unknown module prefix is a dependency error too - except 'Attempt': importing another attempt is
            # the attempt's own error (attempts never see each other)
            if rc != 1 or re.search(r"^(error: )?bwrap: |execvp|batchverify: output missing", out, re.M) or \
                    re.search(r"failed to read file|failed to open file|invalid header|incompatible header|object file .* does not exist|"
                              r"unknown module prefix '(?!Attempt')|unknown package|No such file or directory", out) or \
                    not re.search((re.escape(own) if own else r"\S+") + r":\d+:\d+: error", out):
                return GUARD_EXIT, out + f"\nbatchverify: the compile did not report a source error of the attempt (exit {rc}) - no verdict"
            return rc, out

        def build_one(n):
            src = os.path.join(self.a.attempts, n + ".lean")
            rc, sec, out = self.compile("Attempt." + n, src)
            own = os.path.join(self.proj, *("Attempt." + n).split(".")) + ".lean"   # the file lean compiled (compile's dst)
            rc, out = host_stop(rc, out, own)
            confirmed = False
            if rc not in (0, 124, GUARD_EXIT) and self.needs_confirm(n, out):
                # a failure under an untrusted speed-up is confirmed by a plain compile with the official lean before it
                # can become a REJECTED (availability, not soundness); runs in the worker, in parallel with the others
                rc, sec2, out = self.compile("Attempt." + n, src, plain=True)
                rc, out = host_stop(rc, out, own)
                sec, confirmed = sec + sec2, True
            return rc, sec, out, confirmed

        with cf.ThreadPoolExecutor(self.a.jobs) as ex:
            futs = {ex.submit(build_one, n): n for n in names}
            for fu in cf.as_completed(futs):
                n = futs[fu]
                rc, sec, out, confirmed = fu.result()
                r = self.res["attempts"].setdefault(n, {})
                if confirmed:
                    r["confirmed_plain"] = True
                r.update({"build_exit": rc, "build_s": sec})
                if rc == 0:
                    ok.append(n)
                elif rc == 124:      # the official build would not finish either: no verdict (never a guess)
                    r["verdict"], r["why"] = "NO-VERDICT", f"compile timeout ({self.a.attempt_timeout} s)"
                elif rc == GUARD_EXIT:   # a resource limit ended the compile (--limits) or the sandbox did not start: no verdict
                    r["verdict"] = "NO-VERDICT"
                    last = next((ln for ln in out.splitlines()[::-1] if "batchverify: " in ln), "")
                    r["why"] = (last if "sandbox start failure" in last else "resource limit / no source error: " + last)[:300]
                else:
                    r["verdict"] = "REJECTED"
                    r["why"] = "attempt does not compile (official lean): " + (
                        next((ln for ln in out.splitlines() if "error" in ln), out.strip()[:200]))[:300]
        self.res["build"]["attempts_s"] = round(time.time() - t, 3)
        self.ev(stage="build-attempts", n=len(names), ok=len(ok), s=self.res["build"]["attempts_s"])
        return sorted(ok)

    def build_root(self, names, tag):
        """root module importing the given attempts; returns (rc, clashing attempt names)"""
        mod = "Batch" + tag
        src = os.path.join(self.out, mod + ".lean")
        with open(src, "w") as f:
            f.write("".join(f"import Attempt.{n}\n" for n in names))
        rc, sec, out = self.compile(mod, src)
        self.ev(stage="build-root", mod=mod, n=len(names), exit=rc, s=sec)
        bad = set()
        if rc != 0:
            for n in names:   # an import clash names the modules involved ('... already contains ... Attempt.X')
                if re.search(r"\bAttempt\." + re.escape(n) + r"\b", out):
                    bad.add(n)
        return rc, mod, bad

    # ------------------------------------------------------------------ export + check
    def xvcheck(self):
        """check/xversion/xvcheck.py of the package (the judges' Lean-name parser), loaded once"""
        if getattr(self, "_xv", None) is None:
            import importlib.util
            spec = importlib.util.spec_from_file_location("bv_xvcheck", os.path.join(self.fv, "check", "xversion", "xvcheck.py"))
            self._xv = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(self._xv)
        return self._xv

    def export_targets(self, names):
        """the target list Lake's 4.36 comparator derives (= bin/fastverify read_inputs): builtin ++ theorems ++ axioms
        ++ primitives ++ definitions"""
        axs = list(self.cfg["permitted_axioms"])
        # Lake's `legalAxioms.contains ``Quot.sound` on PARSED names (xvcheck.parse_lean_name)
        if getattr(self, "_quot_builtin", None) is None:
            xv = self.xvcheck()
            self._quot_builtin = xv.parse_lean_name("Quot.sound") in {xv.parse_lean_name(x) for x in axs if isinstance(x, str)}
        builtin = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if self._quot_builtin else []
        return builtin + list(names) + axs + self.primitives + list(self.cfg.get("definition_names") or [])

    def export(self, root, names, tag, threads=None):
        tf = os.path.join(self.out, f"targets.{tag}.txt")
        with open(tf, "w") as f:
            f.write("\n".join(self.export_targets(names)) + "\n")
        binds = os.path.join(self.out, "binds.tsv")
        if not os.path.exists(binds):
            with open(binds, "w") as f:
                f.write(f"{self.ws_pk}\t{self.ws_pk}\n")
        exd = self.a.export_dir or self.out
        # unique per Batch object: tools/fvserve runs many batches concurrently in ONE process with ONE shared
        # export dir and the same tags ('r0', ...); a name of pid + tag let concurrent batches overwrite each other's export
        # and check another batch's export (an attempt ACCEPTED on a sibling's proof of the same theorem)
        xid = getattr(self, "_export_id", None)
        if xid is None:
            xid = self._export_id = os.urandom(8).hex()
        out = os.path.join(exd, f"bv-{os.getpid()}-{xid}-{tag}.export")
        t = time.time()
        p = subprocess.run([os.path.join(self.fv, "export", "export.sh"), "--lean-path", self.lp, "--module", root or " ".join("Attempt." + n for n in names),
                            "--targets-nl", tf, "--toolchain", self.tc, "--project", self.proj, "--binds", binds,
                            "--out", out, "--threads", str(min(threads or self.a.threads, 128))],
                           capture_output=True, text=True, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"})
        sec = round(time.time() - t, 3)
        with open(os.path.join(self.logd, f"export.{tag}.log"), "w") as f:
            f.write(p.stdout + p.stderr)
        size = os.path.getsize(out) if p.returncode == 0 and os.path.exists(out) else None
        with self.lock:
            self.res["exports"].append({"tag": tag, "n": len(names), "exit": p.returncode, "s": sec, "size": size})
        self.ev(stage="export", tag=tag, n=len(names), exit=p.returncode, s=sec, size=size)
        return (out if p.returncode == 0 else None), p.stdout + p.stderr

    def check(self, export, names, tag, threads=None):
        if sha256_file(self.chx) != self.a.challenge_sha256:      # S1(1): the pinned official challenge export
            refuse("batchverify: challenge export sha256 != --challenge-sha256: refuse (no verdict)")
        cfg = dict(self.cfg)
        cfg["theorem_names"] = list(names)
        cfgp = os.path.join(self.out, f"comparator.{tag}.json")
        # the judge's comparator pin is the digest of the SERIALIZED in-memory config, written 0600
        # into the private OUT: a file changed on disk afterwards no longer matches the pin the judge verifies
        cfg_bytes = json.dumps(cfg, indent=1).encode()
        fd = os.open(cfgp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "wb") as f:
            f.write(cfg_bytes)
        cfg_sha = hashlib.sha256(cfg_bytes).hexdigest()
        js = os.path.join(self.logd, f"check.{tag}.json")
        t = time.time()
        # the problem set is held by the service owner: the judge verifies its private copies against
        # the pinned challenge export and the sha256 of the config this batch wrote (computed here, never client input),
        # as tools/fvserve does
        idpins = ["--challenge-sha256", self.a.challenge_sha256, "--comparator-sha256", cfg_sha]
        p = subprocess.run([os.path.join(self.fv, "check", "sound", "check-sound.sh"), export, self.chx, cfgp,
                            "--threads", str(threads or self.a.threads), "--json", js, "--log", os.path.join(self.logd, f"check.{tag}.log")]
                           + (["--pins", self.pins] if getattr(self, "pins", None) else []) + idpins,
                           capture_output=True, text=True)
        sec = round(time.time() - t, 3)
        reason = ""
        try:
            reason = json.load(open(js)).get("reason", "")
        except (OSError, ValueError):
            pass
        try:   # error lines of the check log (kernel errors name the failing declaration) - only used to guide splitting;
            # progress lines (e.g. pleanchecker's 'longest job (NAME ...)') are left out so they do not name innocent attempts
            text = "\n".join(ln for ln in open(os.path.join(self.logd, f"check.{tag}.log"), errors="replace").read()[-400000:]
                             .splitlines() if re.search(r"error|\(kernel\)|mismatch|Illegal|not match", ln, re.I))
        except OSError:
            text = ""
        rec = {"tag": tag, "theorems": list(names), "exit": p.returncode, "s": sec, "reason": reason[:400],
               "config": cfgp, "config_sha256": sha256_file(cfgp)}
        with self.lock:
            self.ncheck += 1
            self.res["checks"].append(rec)
        self.ev(stage="check", tag=tag, n=len(names), exit=p.returncode, s=sec, reason=reason[:160])
        return p.returncode, reason + "\n" + text

    # ------------------------------------------------------------------ verdict logic (the only trusted-relevant part)
    def confirm_ownership(self):
        """Credit assignment: a check of a set S proves that SOME root module of the export
        declares each theorem of S. An accepted theorem t is credited to its own attempt only if Attempt.t is that module:
        trivially when S = {t} or when no other attempt module of S even contains the name t in its .olean; otherwise
        the export of Attempt.t ALONE with target t must succeed (attempts cannot import each other, and a name declared
        by two modules of S makes the set's export decline, so that module is then Attempt.t). Only restricts ACCEPTED.
        "succeeds" is established from the CONTENT of that export, fail-closed and identical on every export
        path (export.sh, fvserve's native fast path, fvserve --warm-check): the export file of Attempt.t alone must contain a
        theorem record named t (export_declares_theorem). An exporter that exits 0 without t (e.g. a delta / meta-only
        export of an empty attempt) gives 'not found' -> not owned -> REJECTED; an unreadable export -> NO-VERDICT."""
        owned, notowned = {}, {}
        # a TYPED reason per not-owned theorem: 'absent' (its own export has no theorem
        # record t) is a rejection; 'unreadable' never is; 'declined' only if the exporter reported t missing
        self._own_kind = {}
        need = set()
        for c in self.res["checks"]:
            if c["exit"] != 0:
                continue
            S = c["theorems"]
            for t in S:
                if t in owned:
                    continue
                # Lean strings in .olean files are NUL-terminated: a module declaring t holds the bytes 't\0' (for a
                # namespaced t those of its LAST component; a module whose .olean cannot be read counts as holding them)
                key = t.rsplit(".", 1)[-1].encode() + b"\x00"
                others = [n for n in S if n != t and self.olean_may_hold(n, key)]
                if not others:
                    owned[t] = "check " + c["tag"]
                else:
                    need.add(t)
        need -= set(owned)
        if need:
            with cf.ThreadPoolExecutor(max(1, min(len(need), self.a.par))) as ex:
                res = dict(zip(sorted(need), ex.map(lambda t: self.export(None, [t], "own-" + t, 4), sorted(need))))
            for t, (exp, why) in res.items():
                if exp is not None:
                    if not os.path.isfile(exp):
                        notowned[t] = "ownership export of Attempt." + t + " is unreadable"; self._own_kind[t] = "unreadable"
                    elif (dt := export_declares_theorem(exp, t)) is None:
                        notowned[t] = "ownership export of Attempt." + t + " could not be read (I/O error)"
                        self._own_kind[t] = "unreadable"
                    elif dt:
                        owned[t] = "check of a set + Attempt." + t + " alone exports " + t
                    else:   # exporter exit 0 but no theorem record t (meta-only / empty / other constants only)
                        notowned[t] = "theorem " + t + " not found in the export of Attempt." + t + " alone"
                        self._own_kind[t] = "absent"
                    try:
                        os.unlink(exp)
                    except OSError:
                        pass
                else:
                    notowned[t] = why; self._own_kind[t] = "declined"
        self.res["ownership"] = {"confirmed_by_export": sorted(set(need) & set(owned)), "not_owned": sorted(notowned)}
        return owned, notowned

    def verdicts(self):
        """ACCEPTED iff some check-sound.sh run exited 0 with a config listing the theorem (config = PSET's with
        theorem_names replaced) and the pinned challenge, and the theorem is credited to its own attempt
        (confirm_ownership); REJECTED iff the attempt did not compile / declare the theorem, or its singleton check exited
        1; else NO-VERDICT. For rewards, NO-VERDICT must count like REJECTED (a hostile attempt can steer a set check to
        DECLINED, e.g. by a declaration name that injects an error line)."""
        owned, notowned = self.confirm_ownership()
        rej = set()
        for c in self.res["checks"]:
            if c["exit"] == 1 and len(c["theorems"]) == 1:
                rej.update(c["theorems"])
        for n, r in self.res["attempts"].items():
            if n in owned:
                r["verdict"], r["why"] = "ACCEPTED", "check-sound.sh ACCEPTED a check whose config listed it (" + owned[n] + ")"
            elif r.get("verdict") == "REJECTED":
                pass
            elif n in notowned:
                # REJECTED only when a SUCCESSFUL ownership export lacks the theorem record ('absent');
                # an exporter / host failure ('declined') or an unreadable export is no verdict - its text is never searched
                kind = getattr(self, "_own_kind", {}).get(n, "declined")
                if kind == "absent" or (kind == "declined" and self.export_says_target_absent(notowned[n], n)):
                    r["verdict"] = "REJECTED"
                    r["why"] = "the theorem is not declared by its own attempt (another attempt of the batch declares it)"
                else:
                    r["verdict"], r["why"] = "NO-VERDICT", "ownership export declined: " + notowned[n].strip()[-200:]
            elif n in rej:
                r["verdict"] = "REJECTED"
                r["why"] = "its singleton check-sound.sh run REJECTED it: " + next(
                    c["reason"] for c in self.res["checks"] if c["theorems"] == [n] and c["exit"] == 1)[:200]
            else:
                r["verdict"], r["why"] = "NO-VERDICT", r.get("why", "no check gave a verdict")

    # ------------------------------------------------------------------ driver
    def try_set(self, root, names, tag, threads):
        """export + check one candidate set -> (rc, text): rc 0/1/2 = check verdict, 3 = export declined"""
        ex, why = self.export(root, names, tag, threads)
        if ex is None:
            return 3, why
        try:
            return self.check(ex, names, tag, threads)
        finally:
            try:
                os.unlink(ex)
            except OSError:
                pass

    def olean_path(self, n):   # the module Attempt.<n>: Attempt/<c1>/.../<cn>.olean
        return os.path.join(self.lib, "Attempt", *n.split(".")) + ".olean"

    def export_says_target_absent(self, text, t):
        """the exporter's own structured decline for exactly the requested target - 'target constant <t>
        not found in environment (declining)' (export/native exporter) - with <t> equal to t as a LEAN name: the module
        loaded and t is not in it. No other text is searched (a host / exporter failure is no verdict)."""
        m = re.search(r"target constant (.+?) not found in environment \(declining\)", text or "")
        if not m:
            return False
        try:
            xv = self.xvcheck()
            a, b = xv.parse_lean_name(m.group(1)), xv.parse_lean_name(t)
            return a is not None and a == b
        except Exception:   # noqa: BLE001 - no parser: exact spelling only
            return m.group(1) == t

    def olean_may_hold(self, n, key):
        """True unless the .olean of Attempt.<n> was READ and does not contain key: a missing or
        unreadable file (any I/O error) counts as 'may declare', so it never lets ownership be credited unconfirmed"""
        try:
            with open(self.olean_path(n), "rb") as f:
                return key in f.read()
        except OSError:
            return True

    def olean_bytes(self, n):
        try:
            with open(self.olean_path(n), "rb") as f:
                return f.read()
        except OSError:
            return b""

    @staticmethod
    def named_in(n, text):
        return re.search(r"(?<![A-Za-z0-9_.])" + re.escape(n) + r"(?![A-Za-z0-9_])", text) is not None

    def solve(self, root, names, tag):
        """parallel rounds: every candidate set of a round is exported + checked concurrently (P slots, threads/P each).
        A rejected set is split: theorems its check log names go alone, the rest into k parts. Singletons end."""
        P = max(1, self.a.par)
        work = [(tag, list(names))]
        rnd = 0
        while work:
            par = min(P, len(work))
            thr = max(1, self.a.threads // par)
            with cf.ThreadPoolExecutor(par) as ex:
                res = list(ex.map(lambda w: self.try_set(root, w[1], w[0], thr), work))
            self.ev(stage="round", round=rnd, sets=len(work), slots=par, threads_each=thr,
                    accepted=sum(1 for r in res if r[0] == 0))
            nxt = []
            for (tg, S), (rc, text) in zip(work, res):
                if rc == 0:
                    continue
                if len(S) == 1:
                    if rc == 3:
                        r = self.res["attempts"][S[0]]
                        if self.export_says_target_absent(text, S[0]):   # structured only
                            r["verdict"] = "REJECTED"
                            r["why"] = "the theorem is not declared by the attempt (export: target missing)"
                        else:
                            r["why"] = "export declined: " + (text.strip().splitlines() or [""])[-1][:200]
                    continue
                named = [n for n in S if self.named_in(n, text)]
                d = re.search(r"duplicate constant '([^']+)'", text) if rc == 3 else None
                if d:   # export declined: two candidate modules declare the same name -> holders go alone
                    comp = d.group(1).split(".")[-1].encode()
                    named = [n for n in S if comp in self.olean_bytes(n)]
                m = re.search(r"Illegal axiom detected: '([^']+)'", text)
                if m and not named:   # heuristic (guides the split only): attempts whose .olean mentions the axiom
                    comp = m.group(1).split(".")[-1].encode()
                    named = [n for n in S if comp in self.olean_bytes(n)]
                rest = [n for n in S if n not in named]
                if named and (rest or (d and len(named) > 1)):
                    nxt += [(f"{tg}n{i}", [n]) for i, n in enumerate(named)]
                    if rest:
                        nxt.append((tg + "r", rest))
                    continue
                k = max(2, min(len(S), self.a.split))
                parts = [S[i::k] for i in range(k)]
                nxt += [(f"{tg}s{i}", p) for i, p in enumerate(parts) if p]
            work = nxt
            rnd += 1

    def run(self):
        if sha256_file(self.chx) != self.a.challenge_sha256:      # S1(1), checked again before every check
            refuse("batchverify: challenge export sha256 != --challenge-sha256: refuse (no verdict)")
        # run the cross-version gate once per batch regardless of --pins (matches lib/fastverify.py:
        # refuses unadmitted releases even with --pins pins-437.env, and enforces release comparator rules)
        xv = os.path.join(self.fv, "check", "xversion", "xvcheck.py")
        if not os.path.isfile(xv):
            refuse("batchverify: check/xversion/xvcheck.py missing: refuse (no verdict)")
        xjf = os.path.join(self.logd, "xversion.json")
        xp = subprocess.run(["/usr/bin/python3", "-I", xv, self.chx, os.path.join(self.a.pset, "comparator.json"),
                             "--json", xjf], capture_output=True, text=True)
        try:
            xj = json.load(open(xjf))
        except (OSError, ValueError):
            xj = {"verdict": "DECLINED", "reason": (xp.stdout + xp.stderr).strip()[-300:]}
        self.res["xversion"] = xj
        # target resolution: DIR/<theorem>.lean must name a theorem of the problem set exactly (a plain or
        # namespaced name, QNAME_RE). A file that names none was never judged: NO-VERDICT, never REJECTED (before: any
        # dotted name, e.g. the configured QACheck.addZero, was REJECTED as "not a theorem name" with zero checks run)
        names = sorted(f[:-5] for f in os.listdir(self.a.attempts) if f.endswith(".lean"))
        thms = {x for x in (self.cfg.get("theorem_names") or []) if isinstance(x, str)}
        # compared as Lean names: QACheck.addZero.lean names the configured QACheck.«addZero»
        pln = self.xvcheck().parse_lean_name
        canon = {pln(x) for x in thms} - {()}
        bad = [n for n in names if not QNAME_RE.fullmatch(n) or (n not in thms and pln(n) not in canon)]
        for n in bad:
            self.res["attempts"][n] = {"verdict": "NO-VERDICT", "why": (
                "not a theorem name of the problem set (target resolution: the file is not judged)" if QNAME_RE.fullmatch(n)
                else "unsupported attempt file name: <theorem>.lean must spell a theorem_names entry with plain identifier "
                     "components (target resolution: the file is not judged)")}
        names = [n for n in names if n not in bad]
        if xp.returncode == 1 and xj.get("verdict") == "REJECTED":
            why = "cross-version gate: " + str(xj.get("reason") or "rejected by release comparator rule")
            for n in names:
                self.res["attempts"][n] = {"verdict": "REJECTED", "why": why}
            self.res["seconds"] = round(time.time() - self.t0, 3)
            self.res["n_checks"] = 0
            self.res["summary"] = {v: sum(1 for r in self.res["attempts"].values() if r.get("verdict") == v)
                                   for v in ("ACCEPTED", "REJECTED", "NO-VERDICT")}
            self.res["events"] = self.events
            with open(os.path.join(self.out, "batch.json"), "w") as f:
                json.dump(self.res, f, indent=1)
            print(json.dumps({"summary": self.res["summary"], "seconds": self.res["seconds"], "checks": 0}))
            return
        if xp.returncode != 0:
            refuse(f"batchverify: cross-version gate exit {xp.returncode} ({xj.get('reason')}): refuse (no verdict)")
        ok = self.build_attempts(names)
        if not self.a.root_module:
            # default: no root module; every export takes exactly the candidate attempt modules as its root modules,
            # so an attempt outside the candidate set is not even loaded, and clashing attempts (duplicate names) make
            # only the exports that contain both decline -> they are separated by the splitting
            if ok:
                self.solve(None, ok, "r0")
            ok = []
        rnd = 0
        while ok:
            rc, root, clash = self.build_root(ok, str(rnd))
            if rc != 0:
                if not clash:
                    for n in ok:
                        self.res["attempts"][n]["why"] = "root module failed without naming an attempt"
                    break
                keep = [n for n in ok if n not in clash]
                if not keep:        # every remaining attempt clashes: one per round
                    keep, clash = ok[:1], set(ok[1:])
                rc, root, clash2 = self.build_root(keep, str(rnd) + "k")
                if rc != 0:
                    for n in keep:
                        self.res["attempts"][n]["why"] = "root module failed"
                    ok = sorted(clash)
                    rnd += 1
                    continue
                self.solve(root, keep, f"r{rnd}")
                ok = sorted(clash)
            else:
                self.solve(root, ok, f"r{rnd}")
                ok = []
            rnd += 1
        self.verdicts()
        self.res["seconds"] = round(time.time() - self.t0, 3)
        self.res["n_checks"] = self.ncheck
        self.res["summary"] = {v: sum(1 for r in self.res["attempts"].values() if r.get("verdict") == v)
                               for v in ("ACCEPTED", "REJECTED", "NO-VERDICT")}
        self.res["events"] = self.events
        with open(os.path.join(self.out, "batch.json"), "w") as f:
            json.dump(self.res, f, indent=1)
        print(json.dumps({"summary": self.res["summary"], "seconds": self.res["seconds"], "checks": self.ncheck}))


def verify_toolchain(fv, toolchain, packages):
    """the --toolchain tree must match its pinned manifest exactly as bin/fastverify verifies the trees it
    builds with (lib/toolchain.py verify ROOT ID: sha256 + mode of every file, no extra/missing entry, pinned version
    lines); ID = the elan directory name of the tree (leanprover--lean4---vX.Y.Z[-rcN]) or the config/components.json
    entry whose prefix is this tree. The packages workspace must exist. Anything else: no batch (exit 2, fail closed).
    -> (realpath of the toolchain, its id)"""
    def refuse(msg):
        print(f"batchverify: {msg}: refuse (no verdict)", file=sys.stderr)
        sys.exit(2)
    real = os.path.realpath(toolchain)
    if not os.path.isdir(real):
        refuse(f"--toolchain {toolchain} is not a directory")
    if not os.path.isdir(os.path.join(os.path.realpath(packages), ".lake", "packages")):
        refuse(f"--packages {packages} has no .lake/packages")
    m = re.fullmatch(r"leanprover--lean4---(v[0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?)", os.path.basename(real))
    tid = "leanprover/lean4:" + m.group(1) if m else None
    if tid is None:
        try:
            comp = json.load(open(os.path.join(fv, "config", "components.json"), encoding="utf-8"))
            tid = next((k for k, v in comp.get("lean_toolchains", {}).items()
                        if isinstance(v, dict) and os.path.realpath(str(v.get("prefix", ""))) == real), None)
        except (OSError, ValueError):
            tid = None
    if tid is None:
        refuse(f"--toolchain {toolchain}: cannot tell which official release it is (no elan toolchain directory name, "
               "not a config/components.json prefix)")
    tv = os.path.join(fv, "lib", "toolchain.py")
    if not os.path.isfile(tv):
        refuse("lib/toolchain.py missing")
    try:
        r = subprocess.run(["/usr/bin/python3", "-I", tv, "verify", real, tid], capture_output=True, text=True,
                           env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "HOME": "/nonexistent"}, timeout=900)
    except (OSError, subprocess.SubprocessError) as e:
        refuse(f"toolchain verification failed to run ({e})")
    if r.returncode != 0:
        refuse(f"--toolchain {real} does not match the pinned manifest of {tid}: "
               + " ".join((r.stderr or r.stdout).strip().splitlines()[-2:])[:400])
    return real, tid



def default_packages():
    """Default trusted Lake workspace: $FV_PACKAGES, else <repository root>/verify/challenge if it exists, else None."""
    p = os.environ.get("FV_PACKAGES")
    if p:
        return p
    p = os.path.join(os.path.dirname(os.path.realpath(os.path.join(HERE, ".."))), "verify", "challenge")
    return p if os.path.isdir(p) else None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pset", required=True)
    ap.add_argument("--attempts", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--challenge-sha256", required=True)
    ap.add_argument("--pins", default=None, help="pins file of the trusted check, e.g. check/sound/pins-437.env (the judge "
                    "built from Lean 4.37.0-rc1): passed to check-sound.sh --pins; a pins*.env of this package's check/sound/")
    ap.add_argument("--threads", type=int, default=os.cpu_count())
    ap.add_argument("--jobs", type=int, default=0)
    ap.add_argument("--packages", default=default_packages(),
                    help="trusted Lake workspace with .lake/packages (default: $FV_PACKAGES, else <repository root>/verify/challenge "
                         "if present)")
    ap.add_argument("--toolchain", default=None, help="the compiler's Lean toolchain prefix (default: the registered toolchain "
                    "of the problem set's release, config/components.json lean_toolchains)")
    ap.add_argument("--fv", default=os.path.join(HERE, ".."))
    ap.add_argument("--export-dir", default=None,
                    help="where the intermediate exports are written; must be private to the verifier (not writable by "
                         "submitters: the trusted check reads the export several times)")
    ap.add_argument("--skip-kernel-tc", action="store_true")
    ap.add_argument("--snapshot-cache", default=None, help="directory keeping the header snapshot across batches")
    ap.add_argument("--snapshot-header", default="import Mathlib",
                    help="header for one --incr-header-save snapshot used by attempts with exactly this header ('' = off)")
    ap.add_argument("--root-module", action="store_true",
                    help="old path: compile a root module importing every compiled attempt and export that")
    ap.add_argument("--confirm-failures", choices=["errors", "all", "none"], default="errors",
                    help="which compile failures under a speed-up are re-compiled plainly before REJECTED (see needs_confirm)")
    ap.add_argument("--attempt-timeout", type=float, default=600, help="seconds per attempt compile (then NO-VERDICT)")
    ap.add_argument("--limits", default=None,
                    help="per-attempt resource limits of the compile, e.g. 'mem=8G,nproc=512,procs=64,cpu=900,fsize=1G,"
                         "out=64M,disk=2G' (tools/guard/fvguard.py; default off): a limit hit -> NO-VERDICT")
    ap.add_argument("--par", type=int, default=8, help="concurrent export+check slots during isolation")
    ap.add_argument("--split", type=int, default=4, help="k-ary split of a rejected set without a named culprit")
    a = ap.parse_args()
    if not re.fullmatch(r"[0-9a-f]{64}", a.challenge_sha256):   # a usage error, exit 2
        ap.error("--challenge-sha256 must be 64 lowercase hex digits")
    if not a.packages:   # (release) no repository-relative workspace and no --packages / $FV_PACKAGES: a usage error
        ap.error("no trusted package workspace: pass --packages DIR or set FV_PACKAGES")
    private_pset(a)   # ONE private copy of the problem set's inputs, checked against the pin
    pset_judge(a)   # before anything is created; reads the private copy
    a.jobs = a.jobs or a.threads
    verify_toolchain(os.path.realpath(a.fv), a.toolchain, a.packages)
    b = Batch(a)
    b.run()
    att = b.res.get("attempts") or {}
    if att and getattr(b, "ncheck", 0) == 0 and all((r or {}).get("verdict") == "NO-VERDICT" for r in att.values()):
        # nothing was judged (e.g. no usable compiler / exporter): the job did not complete -> exit 2
        print("batchverify: no attempt could be judged (no check ran): job incomplete (exit 2)", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    reset_child_signals()
    import signal as _sg

    def _cancel(signum, frame):   # a cancelled batch tears down normally (private copy removed), exit 2
        raise SystemExit(2)
    for _s in (_sg.SIGTERM, _sg.SIGINT, _sg.SIGHUP):
        if _sg.getsignal(_s) is not _sg.SIG_IGN:   # keep nohup's / the shell's ignores
            _sg.signal(_s, _cancel)
    try:
        main()
    except SystemExit:
        raise
    except BaseException:   # a job-level failure (existing --out, missing problem-set file,
        import traceback    # any exception) is no verdict: exit 2, never Python's 1 (= REJECTED)
        traceback.print_exc()
        print("batchverify: job-level failure (no verdict)", file=sys.stderr)
        sys.exit(2)

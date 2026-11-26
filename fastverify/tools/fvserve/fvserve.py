#!/usr/bin/python3 -I
"""fvserve.py — a persistent SOUND verification service for proof attempts (additive, default-off).

    fvserve.py serve  --state DIR --pset NAME=PSETDIR:SHA256 [--pset ...] [--threads N] [--max-inflight K]
                      [--max-batch B] [--packages WS] [--toolchain TC] [--fv FASTVERIFY] [--export-dir DIR]
                      [--check-script PATH] [--check-arg ARG ...] [--warmup NAME:THEOREM:FILE] [--keep N]
                      [--no-fast-export] [--snapshot-header HDR] [--skip-kernel-tc] [--attempt-timeout S]
    fvserve.py submit --state DIR --pset NAME --theorem T FILE [--timeout S]      -> one JSON object (the verdict)
    fvserve.py stats  --state DIR            fvserve.py stop --state DIR

What it is. A prover (a model in an attempt -> verify -> feedback loop, best-of-N sampling, an RL reward pipeline)
submits single proof attempts of the theorems of a PROBLEM SET (PSETDIR/challenge.export = the OFFICIAL export of the
problem set's challenge file, every statement := sorry, made once by the official Lean + official exporter;
PSETDIR/comparator.json). The service answers each attempt with a per-attempt verdict (ACCEPTED / REJECTED /
NO-VERDICT), the compiler output of the attempt (feedback for the model) and the stage times. It pays the fixed costs
of a verification ONCE per service start instead of once per attempt:
  * component preflight (pins, self-test of the trusted check, the exporter's preflight)        - once
  * header snapshot of the common import (`import Mathlib`, official lean --incr-header-save)   - once
  * page cache warm-up (a warm-up attempt through the whole path)                               - once
  * the native exporter's sha256 / version / smoke test (export.sh repeats them per run, ~0.7 s) - once (untrusted)
and it batches concurrent attempts of DIFFERENT theorems into one export + one trusted check (adaptive: attempts that
arrive while K batches are in flight wait and leave together; an idle service dispatches each attempt at once).

Soundness (unchanged trusted base). The verdict of every attempt is decided by the UNCHANGED verdict logic of
tools/batchverify.py (class Batch, methods verdicts / confirm_ownership / solve, inherited here
without change): an attempt is ACCEPTED iff a run of the trusted check (check/sound/check-sound.sh, or the script
given with --check-script) exited 0 on (an export, the pinned official challenge export, a config = the problem set's
comparator.json with theorem_names := a set containing the attempt's theorem) and the theorem is credited to its own
attempt. This file only changes UNTRUSTED parts: when attempts are run (queueing, batching), the header snapshot
reuse, and how the untrusted native exporter is invoked (FastBatch.export: the same binary, sandbox and closure guard
as export/export.sh, its preflight done once; any failure falls back to export.sh itself). Build, export, queueing and
batching can only lose a verdict (REJECTED / NO-VERDICT for some attempt), never create an ACCEPT: that needs exit 0
of the trusted check. The challenge export of each problem set is copied into the private state directory at start
and its sha256 is compared with the pinned value at start and before every check (Batch.check). Attempts are compiled
by the official lean in bwrap (no network, read-only /, home hidden, private output dir), exactly as batchverify does.
For rewards, NO-VERDICT must count like REJECTED.
"""
import argparse, collections, concurrent.futures as cf, hashlib, json, os, re, shutil, signal, socket, socketserver
import subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.realpath(__file__))


def default_toolchain():
    """Default official Lean 4.33.1 toolchain: the one registered in config/components.json (tools/configure.py),
    else ${ELAN_HOME:-~/.elan}/toolchains/leanprover--lean4---v4.33.1."""
    try:
        with open(os.path.join(os.path.realpath(os.path.join(HERE, "..", "..")), "config", "components.json"), encoding="utf-8") as f:
            p = json.load(f)["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
        if p:
            return p
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return os.path.join(os.environ.get("ELAN_HOME") or os.path.expanduser("~/.elan"), "toolchains",
                        "leanprover--lean4---v4.33.1")


def default_packages():
    """Default trusted Lake workspace: $FV_PACKAGES, else <repository root>/verify/challenge if it exists, else None."""
    p = os.environ.get("FV_PACKAGES")
    if p:
        return p
    p = os.path.join(os.path.dirname(os.path.realpath(os.path.join(HERE, "..", ".."))), "verify", "challenge")
    return p if os.path.isdir(p) else None


NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
MAX_SOURCE = 1 << 20


def load_xvcheck(fv):
    """check/xversion/xvcheck.py of the package at fv (the judges' Lean-name parser), loaded by path"""
    import importlib.util
    spec = importlib.util.spec_from_file_location("fvserve_xvcheck", os.path.join(fv, "check", "xversion", "xvcheck.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 24), b""):
            h.update(b)
    return h.hexdigest()


def file_sha_or_none(p):
    """sha256 of a file, None if it cannot be read"""
    try:
        return sha256_file(p)
    except OSError:
        return None


def resolve_pins(fv, given):
    """--pins: like bin/fastverify --pins (lib/fastverify.py resolve_pins) - a pins*.env file inside THIS
    package's check/sound/ (no caller paths; the trusted check re-validates it), or None for the default 4.36 pins.env."""
    if not given:
        return None
    d = os.path.realpath(os.path.join(fv, "check", "sound"))
    p = os.path.realpath(given if os.path.isabs(given) else os.path.join(fv, given))
    if os.path.dirname(p) != d or not os.path.basename(p).startswith("pins") or not p.endswith(".env") \
            or not os.path.isfile(p):
        raise SystemExit(f"fvserve: --pins {given}: must name a pins*.env file in {d}")
    return None if p == os.path.join(d, "pins.env") else p


def lean_version(tc):
    """`TC/bin/lean --version` (one line), "" if it cannot be run."""
    try:
        return subprocess.run([os.path.join(tc, "bin", "lean"), "--version"], capture_output=True, text=True,
                              env={"PATH": "/usr/bin:/bin"}, timeout=60).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return ""


# the releases on which the header-snapshot / fork-server elaboration was A/B-validated against plain lean: only there an
# elaboration error under the speed-up is taken without a plain re-compile. 4.33.1: byte-identical .olean files, no verdict
# changed (108 honest attempts). 4.37.0-rc1: 1,944 real Goedel-8B attempts with every speed-up failure
# re-compiled plainly: 0 of 992 flipped (plain lean never compiled what the fork server failed), 0 verdict differences
SPEEDUP_VALIDATED = ("Lean (version 4.33.1,", "Lean (version 4.37.0-rc1,")


def native_for_toolchain(comp, v):
    """the native exporter entry for the toolchain's release (v = `TC/bin/lean --version`), chosen as
    export/export.sh's select_native does: the natives_other entry whose lean_version equals v, else the default entry
    (which then declines other releases at its preflight, and export.sh decides)."""
    for e in comp.get("natives_other", []):
        if v and e.get("lean_version") == v:
            return e
    return comp["native"]


def fork_matches_toolchain(binary, tc_given, tc_real):
    """fork/build.sh links fvfork against ITS toolchain's libleanshared with an absolute runpath TC/bin/../lib/lean;
    a worker built for another release cannot load this release's header snapshot (it would only fail or be restarted
    again and again), so it is used only if its runpath names this toolchain."""
    try:
        data = open(binary, "rb").read()
    except OSError:
        return False
    return any((t.rstrip("/") + "/bin/../lib/lean").encode() in data for t in {tc_given or "", tc_real or ""} if t)


def clean_stale_export_dirs(parent):
    """a service that was killed (OOM, SIGKILL) leaves its private export dir behind - on /dev/shm that is RAM. Remove
    only dirs named by this code (fvserve-exports.p<PID>.*), owned by us, whose service process is gone (no such pid, or the
    pid now runs something else). Untagged or live dirs are never touched (other services may share the uid)."""
    try:
        names = os.listdir(parent)
    except OSError:
        return
    for n in names:
        m = re.match(r"^fvserve-exports\.p(\d+)\.", n)
        if not m:
            continue
        d = os.path.join(parent, n)
        try:
            if os.lstat(d).st_uid != os.getuid() or not os.path.isdir(d) or os.path.islink(d):
                continue
            pid = int(m.group(1))
            try:
                alive = b"fvserve.py" in open(f"/proc/{pid}/cmdline", "rb").read()
            except OSError:
                alive = False
            if not alive and pid != os.getpid():
                shutil.rmtree(d, ignore_errors=True)
        except OSError:
            pass


def tail_text(path, n):
    """the last n bytes of a file as text ('' if unreadable) - never reads a huge log into memory"""
    try:
        with open(path, "rb") as f:
            f.seek(0, 2)
            size = f.tell()
            f.seek(max(0, size - n))
            b = f.read(n)
        return (f"[... {size - n} bytes dropped ...]\n" if size > n else "") + b.decode("utf-8", "replace")
    except OSError:
        return ""


def load_guard(fv):
    sys.path.insert(0, os.path.join(fv, "tools", "guard"))
    try:
        import fvguard
    finally:
        sys.path.pop(0)
    return fvguard


def load_batchverify(fv):
    sys.path.insert(0, os.path.join(fv, "tools"))
    import batchverify
    sys.path.pop(0)
    return batchverify


# error texts of a fork child's sandbox denial (lean's IO.Error for EACCES / EPERM / ENOSYS)
SANDBOX_DENIAL_RE = re.compile(r"permission denied|operation not permitted|function not implemented", re.I)


# ----------------------------------------------------------------------------------------------------------- batches
def make_fastbatch(bv):
    class FastBatch(bv.Batch):
        """batchverify.Batch with service hooks. Inherited unchanged: compile, build_attempts, make_snapshot, solve,
        try_set, confirm_ownership, verdicts, run (the verdict logic). Overridden: ev (no stdout), export (untrusted
        fast path with fallback to export.sh), check (configurable trusted check script, else identical)."""
        svc = None

        def ev(self, **k):
            k["t"] = round(time.time() - self.t0, 3)
            with self.lock:
                self.events.append(k)

        def export(self, root, names, tag, threads=None):
            s = self.svc
            # the ownership export of confirm_ownership (tag 'own-<t>') never uses the delta exporter: it
            # takes the same path as without --warm-check (native fast path / export.sh, target t), so cold and warm
            # services establish ownership identically (and confirm_ownership requires a theorem record t in the file)
            if s.warm_check and not getattr(self, "_force_full_export", False) and not str(tag).startswith("own-"):
                t = time.time()
                r = s.delta_export(self, root, names, tag)
                if r is not None:
                    out, log, size, mods = r
                    sec = round(time.time() - t, 3)
                    if not hasattr(self, "_delta_info"):
                        self._delta_info = {}
                    self._delta_info[out] = (root, list(names), tag, threads, mods)
                    with self.lock:
                        self.res["exports"].append({"tag": tag, "n": len(names), "exit": 0, "s": sec, "size": size, "delta": True, "tier": 1})
                    self.ev(stage="export", tag=tag, n=len(names), exit=0, s=sec, size=size, delta=True)
                    return out, log
            if not s.fast_export:
                return super().export(root, names, tag, threads)
            t = time.time()
            r = s.native_export(self, root, names, tag, threads)
            if r is None:          # anything unusual: the package's own export stage decides (same result as batchverify)
                out, log = super().export(root, names, tag, threads)
                self.res["exports"][-1]["fast_fallback"] = True
                return out, log
            out, log, size, tn, tg = r
            sec = round(time.time() - t, 3)
            with self.lock:
                self.res["exports"].append({"tag": tag, "n": len(names), "exit": 0, "s": sec, "size": size, "fast": True,
                                            "native_s": tn, "guard_s": tg})
            self.ev(stage="export", tag=tag, n=len(names), exit=0, s=sec, size=size, fast=True)
            return out, log

        def sandbox_masks(self):
            """every compile sandbox of a service batch hides the WHOLE service state dir (its
            socket, every batch dir = other tenants' sources / .olean / exports, the fork server's files, warm state) and
            the export dir; only the attempt's own source, its private output dir, the snapshot are bound back"""
            return [self.svc.state] + ([os.path.realpath(self.a.export_dir)] if getattr(self.a, "export_dir", None) else [])

        def build_attempts(self, names):
            """batchverify's build_attempts (unchanged) + an early report: an attempt whose compile verdict is final after
            the build (REJECTED: does not compile / NO-VERDICT: compile timeout; `verdicts()` never changes these) is answered
            before the batch's export + check run"""
            ok = super().build_attempts(names)
            cb = getattr(self, "early_cb", None)
            if cb:
                cb(self, {n: dict(r) for n, r in self.res["attempts"].items() if n not in ok and r.get("verdict")})
            return ok

        def compile(self, mod, src, extra=(), plain=False):
            """untrusted fast path: the fork server (same official elaboration code, header snapshot loaded once); any
            server problem -> batchverify's compile (official lean). Mirrors Batch.compile: private output dir,
            regular-file check, log file; returns (rc, seconds, output)."""
            fk = self.svc.fork
            if fk is not None and fk.dead:
                self.svc.maybe_restart_fork()      # this attempt uses the official lean; later ones the new server
            if (fk is None or fk.dead or plain or extra or not src or not mod.startswith("Attempt.") or not getattr(self, "snap", None)
                    or self.header_of(src) != self.snap_header):
                return super().compile(mod, src, extra, plain)
            rel = mod.replace(".", "/")
            dst = os.path.join(self.proj, rel + ".lean")
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(src, dst)
            ol = os.path.join(self.lib, rel + ".olean")
            il = os.path.join(self.lib, rel + ".ilean")
            os.makedirs(os.path.dirname(ol), exist_ok=True)
            # the child's private dir lives in the fork server's own writable dir (STATE/fork), with a
            # copy of the source at the same relative path (compiler messages still name 'Attempt/<n>.lean')
            priv = tempfile.mkdtemp(prefix="fk.", dir=self.svc.forkd)
            fsrc = os.path.join(priv, rel + ".lean")
            os.makedirs(os.path.dirname(fsrc), exist_ok=True)
            shutil.copyfile(dst, fsrc)
            t = time.time()
            rc = fk.compile(fsrc, priv, mod, self.a.attempt_timeout, getattr(self, "limits", None))
            out = tail_text(os.path.join(priv, "log"), 200000)   # only the tail: a child may have written gigabytes
            # the child compiled the private copy fsrc: its diagnostics name fsrc. Map exactly that path back to the
            # batch's own file dst, so batchverify's rule (a REJECTED needs an error positioned in the attempt's OWN file)
            # sees the attempt's errors; an error in any other (imported) file keeps its own path and still never counts
            out = out.replace(fsrc + ":", dst + ":")
            if isinstance(rc, tuple):   # the child's tree was killed (timeout / resource limit): FINAL, no verdict -
                kind, detail = rc       # the official lean would run the same elaboration code (no second compile)
                bv.rm_tree(priv)
                if kind == "timeout":
                    code, msg = 124, f"\nfvserve: compile timeout after {self.a.attempt_timeout} s (fork server child killed)"
                else:
                    code = getattr(bv, "GUARD_EXIT", 124)
                    msg = f"\nbatchverify: resource limit: {detail} (fork server child killed; no verdict)"
                with open(os.path.join(self.logd, mod + ".build.log"), "w") as f:
                    f.write(out + msg)
                self.svc.log(event="fork-kill", mod=mod, kind=kind, detail=str(detail)[:200])
                with self.svc.lock:
                    self.svc.stats["fork_" + kind] += 1
                return code, round(time.time() - t, 3), out + msg
            if rc not in (0, 1):     # server unusable, crash, child setup failure -> the official lean decides
                bv.rm_tree(priv)
                self.svc.log(event="fork-fallback", mod=mod, rc=rc)
                with self.svc.lock:
                    self.svc.stats["fork_fallback"] += 1
                return super().compile(mod, src, extra, plain)
            if rc == 1 and SANDBOX_DENIAL_RE.search(out):
                # the fork child's sandbox (Landlock read/exec allowlist, seccomp: no process creation)
                # is stricter than the official lean's: a failure that MAY come from it (EACCES / EPERM / ENOSYS reported)
                # is decided by the official lean in batchverify's per-attempt sandbox, never taken as a REJECT
                bv.rm_tree(priv)
                self.svc.log(event="fork-sandbox-confirm", mod=mod)
                with self.svc.lock:
                    self.svc.stats["fork_sandbox_confirm"] += 1
                return super().compile(mod, src, extra, plain)
            if rc == 0:
                try:
                    import stat as _st
                    pol = os.path.join(priv, "m.olean")
                    if not _st.S_ISREG(os.lstat(pol).st_mode):
                        raise OSError("m.olean is not a regular file")
                    os.replace(pol, ol)
                    with open(il, "w") as f:   # the exporter reads only the .olean; keep batchverify's layout
                        f.write("{}")
                except OSError as e:
                    rc, out = 2, out + f"\nfvserve: fork output missing or not a regular file ({e})"
            bv.rm_tree(priv)
            with open(os.path.join(self.logd, mod + ".build.log"), "w") as f:
                f.write(out)
            with self.svc.lock:
                self.svc.stats["fork_compiles"] += 1
            return rc, round(time.time() - t, 3), out

        def check(self, export, names, tag, threads=None):
            # identical to batchverify.Batch.check except for the script path and extra arguments (svc.check_argv)
            if bv.sha256_file(self.chx) != self.a.challenge_sha256:      # S1(1): the pinned official challenge export
                raise SystemExit("challenge export sha256 != --challenge-sha256: refuse")
            cfg = dict(self.cfg)
            cfg["theorem_names"] = list(names)
            cfgp = os.path.join(self.out, f"comparator.{tag}.json")
            with open(cfgp, "w") as f:
                json.dump(cfg, f, indent=1)
            js = os.path.join(self.logd, f"check.{tag}.json")
            logf = os.path.join(self.logd, f"check.{tag}.log")
            dinfo = getattr(self, "_delta_info", {}).get(export)
            if self.svc.warm_check and dinfo is not None:
                root, dnames, dtag, dthr, mods = dinfo
                wd = self.svc.warm_daemons[self.pset_name]
                t = time.time()
                resp = self.svc.warm_query(wd["state"], {"op": "check_delta", "delta": export, "config": cfgp, "timeout": 180.0})
                tier = 1
                reason_lo = str(resp.get("reason", "")).lower()
                if (resp.get("verdict") == "REJECTED"
                        and any(tok in reason_lo for tok in ("not found", "unknown constant", "missing constant", "unknown declaration"))
                        and wd.get("manifest") and os.path.isfile(wd["manifest"])):
                    r2 = self.svc.delta_export(self, root, dnames, dtag + ".t2", exclude=wd["manifest"], threads=dthr)
                    if r2 is not None:
                        out2, _, sz2, _ = r2
                        tier = 2
                        resp = self.svc.warm_query(wd["state"], {"op": "check_delta", "delta": out2, "config": cfgp, "timeout": 180.0})
                        with self.lock:
                            self.res["exports"].append({"tag": dtag + ".t2", "n": len(dnames), "exit": 0, "size": sz2, "delta": True, "tier": 2})
                if resp.get("verdict") == "FALLBACK_REQUIRED":
                    self._force_full_export = True
                    try:
                        full_exp, _ = self.export(root, dnames, dtag + ".cold", dthr)
                    finally:
                        self._force_full_export = False
                    if full_exp:
                        return self.check(full_exp, names, tag + ".cold", threads)
                sec = round(time.time() - t, 3)
                rc = int(resp.get("exit", 2))
                reason = str(resp.get("reason", ""))
                with open(js, "w") as f:
                    json.dump(resp, f, indent=1)
                rec = {"tag": tag, "theorems": list(names), "exit": rc, "s": sec, "reason": reason[:400],
                       "config": cfgp, "config_sha256": bv.sha256_file(cfgp), "warm": True, "tier": tier,
                       "check_wall_s": round(float(resp.get("wall_ms", 0.0)) / 1000.0, 4)}
                with self.lock:
                    self.ncheck += 1
                    self.res["checks"].append(rec)
                self.ev(stage="check", tag=tag, n=len(names), exit=rc, s=sec, warm=True, tier=tier, reason=reason[:160])
                return rc, reason
            t = time.time()
            p = subprocess.run(self.svc.check_argv(export, self.chx, cfgp, threads or self.a.threads, js, logf),
                               capture_output=True, text=True)
            sec = round(time.time() - t, 3)
            reason = ""
            try:
                reason = json.load(open(js)).get("reason", "")
            except (OSError, ValueError):
                pass
            try:
                text = "\n".join(ln for ln in open(logf, errors="replace").read()[-400000:].splitlines()
                                 if re.search(r"error|\(kernel\)|mismatch|Illegal|not match", ln, re.I))
            except OSError:
                text = ""
            rec = {"tag": tag, "theorems": list(names), "exit": p.returncode, "s": sec, "reason": reason[:400],
                   "config": cfgp, "config_sha256": bv.sha256_file(cfgp)}
            try:
                rec["check_wall_s"] = json.load(open(js)).get("wall_s")
            except (OSError, ValueError):
                pass
            with self.lock:
                self.ncheck += 1
                self.res["checks"].append(rec)
            self.ev(stage="check", tag=tag, n=len(names), exit=p.returncode, s=sec, reason=reason[:160])
            return p.returncode, reason + "\n" + text
    return FastBatch


class ForkServer:
    """the untrusted compile worker fork/fvfork (built from fork/FvFork.lean + fork/shim.c with the OFFICIAL 4.33.1
    toolchain, linked against its libleanshared): loads the official header snapshot ONCE, then elaborates every attempt
    in a fork()ed child (Landlock: the child writes only its own output dir) with the body of Lean.Elab.runFrontend.
    Runs inside bwrap exactly like batchverify's lean (no network, read-only /, home hidden, env cleared); the state dir is
    masked and only STATE/fork (the children's private dirs) is writable - the batch dirs are not visible at all;
    each child is confined further by setsid + Landlock + seccomp (fork/shim.c)."""

    def __init__(self, svc, binary, snap):
        self.svc, self.binary, self.snap = svc, binary, snap
        self.lock = threading.Lock()
        self.waiters = {}
        self.n = 0
        self.ready = threading.Event()
        self.dead = False
        ws_pk, tc = svc.ws_pk, svc.tc
        lp = ":".join(os.path.join(ws_pk, d, ".lake", "build", "lib", "lean") for d in sorted(os.listdir(ws_pk)))
        # the whole state dir is masked (socket, batches, warm state, logs); only STATE/fork (the
        # children's private dirs) is bound back writable, plus the snapshot dir and the binary file read-only (each
        # child reads only its own source and writes only its own private dir: fork/shim.c setsid + Landlock + seccomp)
        self.legacy = False
        # only the binary FILE is bound (never its directory: a sibling file there, or the
        # state dir itself, would become visible), and it is not readable by the children (they never exec or read it)
        ro = [os.path.dirname(snap), binary]
        argv = svc.bv.sandbox(tc, ws_pk, rw=[svc.forkd], ro=ro, chdir="/", mask=[svc.state],
                              env={"LEAN_PATH": lp, "FVFORK_READ": ":".join([tc, ws_pk, os.path.dirname(snap)])}) + [binary, snap]
        self.p = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=open(
            os.path.join(svc.state, "fvfork.err"), "ab"), env={}, text=True, bufsize=1)
        threading.Thread(target=self.reader, daemon=True).start()

    def reader(self):
        for ln in self.p.stdout:
            w = ln.split()
            if w[:1] == ["READY"]:
                if "sandbox=2" not in w:
                    # a binary built before the child sandbox (Landlock read/exec allowlist, seccomp: no
                    # process creation / signals or limits on others / setpgid, own session) is never used: no fork server
                    self.legacy = True
                    try:
                        self.p.kill()
                    except OSError:
                        pass
                    break
                self.ready.set()
            elif w[:1] == ["DONE"] and len(w) == 3:
                with self.lock:
                    ev = self.waiters.get(w[1])
                if ev:
                    ev[1] = int(w[2])
                    ev[0].set()
        self.dead = True
        self.ready.set()
        with self.lock:
            for ev in self.waiters.values():
                ev[0].set()

    def main_pid(self):
        """pid of the fvfork process itself (inside the sandbox: argv = [binary, snap])"""
        if getattr(self, "_main", None):
            return self._main
        g = self.svc.guard
        for p in g.tree(self.p.pid):
            cl = (g._read(f"/proc/{p}/cmdline") or b"").split(b"\0")
            if len(cl) >= 2 and cl[0].decode(errors="replace") == self.binary and cl[1].decode(errors="replace") == self.snap:
                self._main = p
                return p
        return None

    def find_child(self, outdir, wait_s, done=None):
        """the forked child serving OUTDIR: its stdout is OUTDIR/log (fork/shim.c fv_child_setup); None if not found (also
        at once when its DONE line has arrived: a child that finished before it was seen needs no watching)"""
        main, g = self.main_pid(), self.svc.guard
        if not main:
            return None
        target = os.path.join(outdir, "log")
        end = time.time() + wait_s
        while time.time() < end and not (done is not None and done.is_set()):
            for c in g.children(main):
                try:
                    if os.readlink(f"/proc/{c}/fd/1") == target:
                        return c
                except OSError:
                    pass
            if self.dead:
                return None
            time.sleep(0.005)
        return None

    def compile(self, src, outdir, mod, timeout, limits=None):
        """-> exit status of the child (0 ok, 1 elaboration errors); ("timeout"|"limit", detail) when the child's process
        tree was KILLED (a timed-out child must not keep running, and the attempt must not be compiled a second
        time); or None (server unusable / crash / child not found at a timeout: the caller falls back to the official lean)"""
        if self.dead or not self.ready.is_set():
            return None
        with self.lock:
            self.n += 1
            rid = f"r{self.n}"
            ev = [threading.Event(), None]
            self.waiters[rid] = ev
        try:
            self.p.stdin.write(f"{rid}\t{src}\t{outdir}\t{mod}\n")
            self.p.stdin.flush()
        except OSError:
            self.dead = True
            return None
        g = self.svc.guard
        child = self.find_child(outdir, 5.0, ev[0])
        w = None
        if child and limits is not None:
            # the child shares the parent's heap copy-on-write: subtract the parent's anonymous memory
            base = (g.proc_mem(self.main_pid(), "anon") or (0, 0))[0] if limits.mem_metric == "anon" else 0
            w = g.Watch(child, limits, mem_baseline=base,
                        disk=[(outdir, limits.disk)] if (limits.disk or limits.disk_files) else ())
            w.start()
        ok = ev[0].wait(timeout)
        if w is not None:
            w.stop()
        try:
            if w is not None and w.violation:
                ev[0].wait(10)                      # its DONE line (killed)
                return ("limit", w.detail)
            if not ok:
                if not child:
                    return None
                ww = g.Watch(child, g.Limits())
                ww.kill_tree()
                ev[0].wait(10)
                return ("timeout", f"{timeout} s")
            return ev[1]
        finally:
            with self.lock:
                self.waiters.pop(rid, None)

    def stop(self):
        try:
            self.p.stdin.close()
            self.p.wait(10)
        except Exception:
            self.p.kill()


class Item:
    __slots__ = ("id", "pset", "theorem", "source", "t_submit", "t_start", "done", "result", "cancelled", "client")

    def __init__(self, iid, pset, theorem, source, client=""):
        self.id, self.pset, self.theorem, self.source = iid, pset, theorem, source
        self.client = client
        self.t_submit, self.t_start = time.time(), None
        self.cancelled = False
        self.done = threading.Event()
        self.result = None


# ----------------------------------------------------------------------------------------------------------- service
class Service:
    def __init__(self, a):
        self.a = a
        self.t0 = time.time()
        self.state = os.path.realpath(a.state)
        os.makedirs(self.state, exist_ok=True)
        os.chmod(self.state, 0o700)
        self.fv = os.path.realpath(a.fv)
        self.bv = load_batchverify(self.fv)
        self.FastBatch = make_fastbatch(self.bv)
        self.FastBatch.svc = self
        self.guard = load_guard(self.fv)            # tools/guard (process-tree helpers; limits only with --limits)
        # which code this process runs: Python keeps the code it imported at start, so a file replaced later (a fix
        # published while the service runs) is NOT in use until a restart. 'stats' reports the sha256 of the files loaded
        # at start and lists those that differ on disk now ("stale": restart the service to use them).
        self.code_files = {"fvserve": os.path.realpath(__file__), "batchverify": os.path.realpath(self.bv.__file__),
                           "fvguard": os.path.realpath(self.guard.__file__)}
        if getattr(a, "fork_server", None):
            self.code_files["fvfork"] = os.path.realpath(a.fork_server)
        self.code = {k: file_sha_or_none(p) for k, p in self.code_files.items()}
        self.limits = self.guard.Limits.parse(a.limits) if getattr(a, "limits", None) else None
        self.tc = os.path.realpath(a.toolchain)
        if not a.packages:
            raise SystemExit("fvserve: no trusted package workspace: pass --packages DIR or set FV_PACKAGES")
        self.ws = os.path.realpath(a.packages)
        self.ws_pk = os.path.join(self.ws, ".lake", "packages")
        self.lock = threading.Lock()
        self.cv = threading.Condition(self.lock)
        self.pending = collections.deque()
        self.inflight = 0
        self.served = {}             # --fair: client -> counter of its last attempt taken into a batch
        self.nserved = 0
        self.started = {}            # dispatch key -> start time of the batches in flight (--slow-after)
        self.nlaunch = 0
        self.nbatch = 0
        self.nitem = 0
        self.stop_flag = False
        self.stats = collections.Counter()
        self.logf = open(os.path.join(self.state, "service.jsonl"), "a")
        if a.svc_check:     # trusted service variant: check-sound.sh + --integrity-cache (pins verified once, then stamps)
            self.check_script = os.path.join(self.fv, "check", "sound", "check-sound-svc.sh")
            self.icache = os.path.join(self.state, "icache")
            os.makedirs(self.icache, exist_ok=True)
            os.chmod(self.icache, 0o700)
            self.check_extra = ["--integrity-cache", self.icache] + list(a.check_arg or [])
        else:
            self.check_script = os.path.realpath(a.check_script or os.path.join(self.fv, "check", "sound", "check-sound.sh"))
            self.icache = None
            self.check_extra = list(a.check_arg or [])
        self.lean_version = lean_version(self.tc)
        # on a release where the speed-ups were not A/B-validated (e.g. 4.36.0) every compile failure under the
        # header snapshot / fork server is re-compiled by plain lean before it can become REJECTED
        self.confirm_failures = "errors" if self.lean_version.startswith(SPEEDUP_VALIDATED) else "all"
        self.pins = resolve_pins(self.fv, getattr(a, "pins", None))
        if self.pins:
            if getattr(a, "warm_check", False):
                raise SystemExit("fvserve: --warm-check uses the 4.36 warm legs; it cannot be combined with --pins")
            self.check_extra = self.check_extra + ["--pins", self.pins]
        self.fast_export = not a.no_fast_export
        exd = a.export_dir or ("/dev/shm" if os.path.isdir("/dev/shm") else self.state)
        clean_stale_export_dirs(exd)
        # private (0700); the pid in the name lets a later service remove it if this one dies without cleaning up
        self.export_dir = tempfile.mkdtemp(prefix=f"fvserve-exports.p{os.getpid()}.", dir=exd)
        self.bdir = os.path.join(self.state, "batches")
        os.makedirs(self.bdir, exist_ok=True)
        os.chmod(self.bdir, 0o700)   # this service's own dir: a mode damaged earlier is reset at start
        # batch numbers continue after the batch dirs a previous run kept (--keep): no name collision
        self.nbatch = max([int(e[1:]) for e in os.listdir(self.bdir) if re.fullmatch(r"b[0-9]{6,12}", e)] + [0])
        # the fork server's ONLY writable directory: each child gets a private dir here holding a copy
        # of its own source and its outputs; the batch dirs (other tenants, history) are not visible to the fork server
        self.forkd = os.path.join(self.state, "fork")
        # the previous run's STATE/fork (its children's private dirs: untrusted content, any depth, any
        # modes) is renamed aside atomically and removed in the background by depth-safe tools: start-up never fails on it
        old_fork = []
        if os.path.lexists(self.forkd):
            aside = os.path.join(self.state, f"fork.old.{os.getpid()}.{time.time_ns()}")
            os.rename(self.forkd, aside)
        for e in os.listdir(self.state):
            if e.startswith("fork.old."):
                old_fork.append(os.path.join(self.state, e))
        if old_fork:
            threading.Thread(target=lambda: [self.bv.rm_tree(x) for x in old_fork], daemon=True,
                             name="fork-dir-cleanup").start()
        os.makedirs(self.forkd, mode=0o700)
        self.psets = {}
        self.timing = {}
        self.fork = None
        self.fork_snap = None
        self.fork_restarting = False
        self.fork_last_restart = 0.0
        self.finished = collections.deque()
        self.warm_check = bool(getattr(a, "warm_check", False))
        if self.warm_check:   # warm mode is EXPERIMENTAL and not available (single-attempt ownership gap)
            raise SystemExit("fvserve: --warm-check is not available in this release; run without it")
        self.warm_daemons = {}
        self.warm_bins = os.path.realpath(a.warm_bins) if getattr(a, "warm_bins", None) else "/scratch/fastverify-next/warm/v1"
        self.warm_src = os.path.realpath(a.warm_src) if getattr(a, "warm_src", None) else os.path.join(self.fv, "check", "warm")

    def log(self, **k):
        k["t"] = round(time.time() - self.t0, 3)
        with self.lock:
            self.logf.write(json.dumps(k) + "\n")
            self.logf.flush()

    # ------------------------------------------------------------------ start-up (the fixed costs, paid once)
    def startup(self):
        t = time.time()
        for spec in self.a.pset:
            name, rest = spec.split("=", 1)
            pdir, sha = rest.rsplit(":", 1)
            if not NAME_RE.fullmatch(name) or not re.fullmatch(r"[0-9a-f]{64}", sha):   # fullmatch
                raise SystemExit(f"fvserve: bad --pset {spec!r} (NAME=PSETDIR:SHA256)")
            d = os.path.join(self.state, "psets", name)
            os.makedirs(d, exist_ok=True)
            # private copy of the official challenge export (nobody else writes it during the service's life)
            tmp = os.path.join(d, ".challenge.export.tmp")
            shutil.copyfile(os.path.join(pdir, "challenge.export"), tmp)
            os.chmod(tmp, 0o400)
            os.replace(tmp, os.path.join(d, "challenge.export"))
            shutil.copyfile(os.path.join(pdir, "comparator.json"), os.path.join(d, "comparator.json"))
            got = sha256_file(os.path.join(d, "challenge.export"))
            if got != sha:
                raise SystemExit(f"fvserve: challenge export of {name} has sha256 {got}, pinned {sha}: refuse")
            cfg = json.load(open(os.path.join(d, "comparator.json"), encoding="utf-8"))
            raw_ax = cfg.get("permitted_axioms")
            # compared as Lean names (xvcheck.parse_lean_name, the judges' String.toName mirror): `«propext»`
            # is propext; the set is not widened
            xvn = load_xvcheck(self.fv).parse_lean_name
            s1 = {xvn(n) for n in ("propext", "Quot.sound", "Classical.choice")}
            if not isinstance(raw_ax, list) or any(not isinstance(x, str) or xvn(x) not in s1 for x in raw_ax):
                raise SystemExit(f"fvserve: comparator.json of {name} has permitted_axioms outside GOAL S1(3): refuse")
            # A04's cross-version gate (veto only), as bin/fastverify applies it in sound mode: a problem set whose official
            # challenge export comes from a release the 4.36 check is not verified for gives no verdict; one that fails a
            # rule of its release's own comparator rejects every attempt
            xv = os.path.join(self.fv, "check", "xversion", "xvcheck.py")
            if not os.path.isfile(xv):
                raise SystemExit(f"fvserve: missing cross-version gate {xv}: refuse")
            xp = subprocess.run(["/usr/bin/python3", "-I", xv, os.path.join(d, "challenge.export"),
                                 os.path.join(d, "comparator.json")], capture_output=True, text=True)
            xrc = xp.returncode
            if xrc not in (0, 1):
                raise SystemExit(f"fvserve: cross-version gate gives no verdict for {name} (rc {xrc}): "
                                 + (xp.stdout + xp.stderr)[-300:] + " - refuse")
            self.psets[name] = {"dir": d, "sha": sha, "theorems": set(cfg.get("theorem_names") or []), "xversion_rc": xrc}
        self.timing["psets_s"] = round(time.time() - t, 3)
        # --toolchain verified against its pinned manifest exactly like bin/fastverify does (lib/toolchain.py
        # verify), and --packages must exist - once, after the cheap problem-set checks above (pins, S1(3), the cross-version
        # gate: their refusals stay specific; r2, review M2) and before anything is compiled; else no service (exit 2)
        t = time.time()
        _, self.timing["toolchain_verified"] = self.bv.verify_toolchain(self.fv, self.a.toolchain, self.a.packages)
        self.timing["toolchain_verify_s"] = round(time.time() - t, 3)
        self.timing["profile"] = getattr(self.a, "profile", None)
        # trusted check preflight (pins + self-test); with an integrity-cache variant this also fills the cache
        t = time.time()
        p = subprocess.run(self.check_argv_preflight(), capture_output=True, text=True)
        self.timing["check_preflight_s"] = round(time.time() - t, 3)
        if p.returncode != 0:
            raise SystemExit("fvserve: trusted check preflight failed: " + (p.stdout + p.stderr)[-600:])
        # exporter: verify the native exporter + closure guard once (untrusted in sound mode: availability only)
        t = time.time()
        comp = json.load(open(os.path.join(self.fv, "export", "components.json")))
        nat = native_for_toolchain(comp, self.lean_version)   # export.sh's select_native: the native exporter of THIS release
        self.native = nat["path"]
        self.timing["native_exporter"] = os.path.basename(self.native)
        self.timing["lean"] = self.lean_version[:80]
        self.timing["confirm_failures"] = self.confirm_failures
        self.timing["check_pins"] = os.path.basename(self.pins) if self.pins else "pins.env"
        self.closure = comp["closure_check"]["path"]
        ok = (os.access(self.native, os.X_OK) and sha256_file(self.native) == nat["sha256"]
              and os.access(self.closure, os.X_OK) and sha256_file(self.closure) == comp["closure_check"]["sha256"])
        if ok:
            p = subprocess.run([os.path.join(self.fv, "export", "export.sh"), "--preflight", self.tc],
                               capture_output=True, text=True)
            ok = p.returncode == 0
        if not ok:
            self.fast_export = False
        self.timing["export_preflight_s"] = round(time.time() - t, 3)
        self.timing["fast_export"] = self.fast_export
        # warm-up: one attempt through the whole path (makes the header snapshot, warms the page cache)
        t = time.time()
        if self.a.warmup:
            name, thm, path = self.a.warmup.split(":", 2)
            it = Item("warmup", name, thm, open(path).read())
            self.run_batch([it])
            self.timing["warmup_verdict"] = it.result.get("verdict")
        else:
            self.run_batch([], snapshot_only=True)
        self.timing["warmup_s"] = round(time.time() - t, 3)
        if self.a.fork_server:
            t = time.time()
            snaps = [os.path.join(r, "hdr.snap") for r, _, fs in os.walk(os.path.join(self.state, "snap")) if "hdr.snap" in fs]
            bdir_ = os.path.dirname(os.path.realpath(self.a.fork_server))
            ro_roots = ["/usr", "/lib", "/lib32", "/lib64", "/libx32", "/bin", "/sbin", "/etc", "/sys", "/proc", "/dev",
                        self.tc, self.ws_pk]
            if snaps and any(self.state == r or self.state.startswith(r.rstrip("/") + "/") for r in ro_roots):
                # a state dir below a tree the children may read (system dirs, the toolchain,
                # the packages) or below /dev (a state dir in /dev/shm) is never combined with the fork server
                self.log(event="fork-server-refused", why="the state dir " + self.state + " lies below a directory the fork "
                         "children may read (or /dev): use a state dir elsewhere for --fork-server")
                snaps = []
            if snaps and (bdir_ == self.state or bdir_.startswith(self.state + "/")):
                # a binary inside the state dir (writable by the service, next to every batch) is not used
                self.log(event="fork-server-refused", why="the fvfork binary lies inside the state dir " + self.state
                         + ": build it elsewhere (fork/build.sh TC OUTDIR)")
                snaps = []
            if snaps and not fork_matches_toolchain(os.path.realpath(self.a.fork_server), self.a.toolchain, self.tc):
                self.log(event="fork-server-skipped", why="the fvfork binary is linked against another toolchain's "
                         "libleanshared (rebuild it with fork/build.sh " + self.tc + ")")
                snaps = []
            if snaps:
                self.fork_snap = snaps[0]
                self.fork = ForkServer(self, os.path.realpath(self.a.fork_server), snaps[0])
                self.fork.ready.wait(120)
                if self.fork.dead or not self.fork.ready.is_set():
                    if getattr(self.fork, "legacy", False):
                        self.log(event="fork-server-refused", why="the fvfork binary predates the fork-child sandbox (no "
                                 "'sandbox=2' in its READY line): rebuild it with fork/build.sh")
                    else:
                        self.log(event="fork-server-failed")
                    self.fork = None
            self.timing["fork_server_s"] = round(time.time() - t, 3)
            self.timing["fork_server"] = self.fork is not None
        if self.warm_check:
            t_w = time.time()
            fvcheckd_py = os.path.join(self.warm_src, "fvcheckd.py")
            extractor = os.path.join(self.warm_bins, "warm-delta-extract")
            for pname, pinfo in self.psets.items():
                wstate = os.path.join(self.state, "warm", pname)
                shutil.rmtree(wstate, ignore_errors=True)
                os.makedirs(os.path.dirname(wstate), exist_ok=True)
                chal_p = os.path.join(pinfo["dir"], "challenge.export")
                cfg_p = os.path.join(pinfo["dir"], "comparator.json")
                base_p = os.path.realpath(self.a.warm_base) if getattr(self.a, "warm_base", None) else chal_p
                manifest_p = os.path.join(self.state, "warm", f"{pname}.base_consts.txt")
                if os.path.isfile(extractor) and not os.path.isfile(manifest_p):
                    subprocess.run([extractor, "manifest", base_p, manifest_p],
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
                wlog = open(wstate + ".log", "w")
                wthr = max(4, min(32, self.a.threads))
                wproc = subprocess.Popen([
                    "/usr/bin/python3", "-I", fvcheckd_py, "serve",
                    "--state", wstate, "--challenge", chal_p, "--challenge-sha256", pinfo["sha"],
                    "--config", cfg_p, "--allow-theorem-subset",
                    "--base", base_p, "--threads", str(wthr), "--bins-dir", self.warm_bins,
                    "--pkgroot", self.fv,
                ], stdout=wlog, stderr=subprocess.STDOUT)
                wsock = os.path.join(wstate, "sock")
                for _ in range(3600):
                    if os.path.exists(wsock):
                        break
                    if wproc.poll() is not None:
                        wlog.close()
                        raise SystemExit(f"fvserve: fvcheckd for {pname} died:\n" + open(wstate + ".log").read()[-800:])
                    time.sleep(0.1)
                else:
                    wproc.kill()
                    wlog.close()
                    raise SystemExit(f"fvserve: fvcheckd for {pname} timed out")
                self.warm_daemons[pname] = {"state": wstate, "proc": wproc, "log": wlog,
                                            "base": base_p, "manifest": manifest_p if os.path.isfile(manifest_p) else None}
            self.timing["warm_daemons_s"] = round(time.time() - t_w, 3)
            self.timing["warm_check"] = True
        self.timing["startup_s"] = round(time.time() - self.t0, 3)
        self.log(event="startup", **self.timing)

    def warm_query(self, wstate, req, timeout_s=240.0):
        sock_path = os.path.join(wstate, "sock")
        deadline = time.time() + min(10.0, timeout_s)
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(timeout_s)
        while True:
            try:
                s.connect(sock_path)
                break
            except (BlockingIOError, ConnectionRefusedError):
                if time.time() >= deadline:
                    s.close()
                    raise
                time.sleep(0.01)
        try:
            s.sendall((json.dumps(req) + "\n").encode("utf-8"))
            chunks = []
            while True:
                b = s.recv(65536)
                if not b:
                    break
                chunks.append(b)
                if b"\n" in b:
                    break
            return json.loads(b"".join(chunks).decode("utf-8"))
        finally:
            s.close()

    def delta_export(self, batch, root, names, tag, exclude=None, threads=None):
        """Untrusted delta native exporter: Tier 1 (LEAN4EXPORT_DELTA_ONLY=1) or Tier 2 (LEAN4EXPORT_SNAP=1 LEAN4EXPORT_EXCLUDE)."""
        delta_bin = os.path.join(self.warm_bins, "lean4export-delta")
        if not os.access(delta_bin, os.X_OK):
            return None
        mods = root.split() if root else ["Attempt." + n for n in names]
        out = os.path.join(self.export_dir, f"dx-{os.getpid()}-{batch.bid}-{tag}.ndjson")
        mod_file = out + ".mods"
        with open(mod_file, "w") as mf:
            mf.write("\n".join(mods) + "\n")
        errp = out + ".err"
        thr = max(1, min(threads or batch.a.threads, 16)) if exclude else 1
        extra_binds = ["--ro-bind", mod_file, mod_file, "--ro-bind", delta_bin, delta_bin]
        mode_env = ["--setenv", "LEAN4EXPORT_DELTA_ONLY", "1"]
        filt_ex = None
        if exclude:
            prev_t1 = None
            for k_out, info in getattr(batch, "_delta_info", {}).items():
                if info[2] == tag[:-3] and os.path.isfile(k_out):
                    prev_t1 = k_out
                    break
            filt_ex = out + ".ex"
            dirty_nms = set()
            if prev_t1:
                nmap = {0: ""}
                with open(prev_t1, "r", encoding="utf-8", errors="replace") as tf:
                    for ln in tf:
                        ln = ln.strip()
                        if not ln:
                            continue
                        try:
                            o = json.loads(ln)
                        except Exception:
                            continue
                        if "in" in o:
                            if "str" in o:
                                p = nmap.get(o["str"]["pre"], "")
                                nmap[o["in"]] = (p + "." + o["str"]["str"]) if p else o["str"]["str"]
                            elif "num" in o:
                                p = nmap.get(o["num"]["pre"], "")
                                nmap[o["in"]] = (p + "." + str(o["num"]["i"])) if p else str(o["num"]["i"])
                        elif "inductive" in o:
                            for g in ("types", "ctors", "recs"):
                                for it in o["inductive"].get(g, ()):
                                    dirty_nms.add(nmap.get(it["name"], ""))
                        else:
                            for kk in ("axiom", "def", "thm", "opaque", "quot"):
                                if kk in o:
                                    dirty_nms.add(nmap.get(o[kk]["name"], ""))
            with open(exclude, "r", encoding="utf-8") as fin, open(filt_ex, "w", encoding="utf-8") as fout:
                for ln in fin:
                    s = ln.rstrip("\r\n")
                    if s and s not in dirty_nms:
                        fout.write(s + "\n")
            extra_binds += ["--ro-bind", filt_ex, filt_ex]
            mode_env = ["--setenv", "LEAN4EXPORT_SNAP", "1", "--setenv", "LEAN4EXPORT_EXCLUDE", filt_ex]
        # no separate /run/user mask: `--tmpfs /run` below masks all of /run, and
        # bwrap cannot create /run/user on hosts without it (the delta export then always failed there)
        sbx = ["/usr/bin/bwrap", "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root",
               "--tmpfs", "/tmp", "--dir", "/tmp/home", "--tmpfs", "/run", "--tmpfs", "/var", "--dev", "/dev", "--proc",
               "/proc", "--clearenv", "--ro-bind", self.tc, self.tc, "--ro-bind", batch.proj, batch.proj,
               "--ro-bind", self.ws_pk, self.ws_pk, *extra_binds,
               "--setenv", "PATH", f"{self.tc}/bin:/usr/bin:/bin", "--setenv", "HOME", "/tmp/home", "--setenv", "LANG",
               "C.UTF-8", "--setenv", "LEAN_PATH", batch.lp, "--setenv", "LEAN_ABORT_ON_PANIC", "1",
               *mode_env, "--setenv", "LEAN4EXPORT_THREADS", str(thr),
               "--unshare-all", "--die-with-parent", "--new-session", "--chdir", batch.proj, "--",
               delta_bin, "@" + mod_file]
        try:
            with open(out, "wb") as fo, open(errp, "wb") as fe:
                os.chmod(out, 0o600)
                p = subprocess.run(sbx, stdout=fo, stderr=fe, env={}, timeout=120)
            log = open(errp, errors="replace").read()
            if p.returncode != 0 or os.path.getsize(out) == 0:
                raise OSError(f"delta exit {p.returncode}: {log[:200]}")
            sz = os.path.getsize(out)
            for x in (errp, mod_file, filt_ex):
                if x:
                    try:
                        os.unlink(x)
                    except OSError:
                        pass
            return out, log, sz, mods
        except Exception as e:
            for x in (out, errp, mod_file, filt_ex):
                if x:
                    try:
                        os.unlink(x)
                    except OSError:
                        pass
            self.log(event="delta-export-fallback", batch=batch.bid, tag=tag, why=str(e)[:200])
            return None

    def maybe_restart_fork(self):
        """the fork server died (an OOM kill inside a memory-capped host, a crash): without a restart every later attempt would
        pay the full import of the official lean. Restart it in the background (at most one restart
        per 10 s); compiles use the official lean meanwhile. Untrusted (availability only)."""
        with self.lock:
            if (self.fork_restarting or self.stop_flag or not self.a.fork_server or not self.fork_snap or self.fork is None
                    or not self.fork.dead or time.time() - self.fork_last_restart < 10):
                return
            self.fork_restarting, self.fork_last_restart = True, time.time()

        def go():
            t = time.time()
            ok, fk = False, None
            try:
                old = self.fork
                try:
                    old.stop()
                except Exception:          # noqa: BLE001 - it is dead already
                    pass
                fk = ForkServer(self, os.path.realpath(self.a.fork_server), self.fork_snap)
                fk.ready.wait(120)
                ok = fk.ready.is_set() and not fk.dead
                if ok:
                    self.fork = fk
                else:
                    fk.stop()
                with self.lock:
                    self.stats["fork_restarts" if ok else "fork_restart_failed"] += 1
                self.log(event="fork-restart", ok=ok, s=round(time.time() - t, 3))
            finally:
                with self.lock:
                    self.fork_restarting = False
            if ok:
                # bwrap --die-with-parent = PR_SET_PDEATHSIG, which fires when the parent THREAD exits: this thread started
                # the worker's bwrap, so it must live as long as the worker (measured: returning here killed the new worker
                # ~2 s after READY)
                fk.p.wait()
        threading.Thread(target=go, daemon=True, name="fork-server-keeper").start()

    def check_argv_preflight(self):
        return [self.check_script, "--preflight"] + (["--integrity-cache", self.icache] if self.icache else []) + \
            (["--pins", self.pins] if self.pins else [])

    def check_argv(self, export, chx, cfgp, threads, js, logf):
        argv = [self.check_script, export, chx, cfgp, "--threads", str(threads), "--json", js, "--log", logf] + \
            self.check_extra
        try:
            if "--challenge-sha256)" in open(self.check_script, encoding="utf-8", errors="replace").read():
                argv += ["--challenge-sha256", sha256_file(chx), "--comparator-sha256", sha256_file(cfgp)]
        except OSError:
            pass
        return argv

    # ------------------------------------------------------------------ untrusted fast export (export.sh's native path)
    def native_export(self, batch, root, names, tag, threads):
        """the native exporter + closure guard exactly as export/export.sh runs them (same sandbox, environment, early
        return, guard), without export.sh's per-run preflight (done once at start). Returns (path, log, size) or None
        (then export.sh decides)."""
        tf = os.path.join(batch.out, f"targets.{tag}.txt")
        targets = batch.export_targets(names)
        with open(tf, "w") as f:
            f.write("\n".join(targets) + "\n")
        mods = root.split() if root else ["Attempt." + n for n in names]
        out = os.path.join(self.export_dir, f"fx-{os.getpid()}-{batch.bid}-{tag}.export")
        thr = max(1, min(threads or batch.a.threads, 128))
        # the exporter reads UNTRUSTED .olean files: S4 masks (every non-system top-level dir, the
        # state dir), then only the toolchain, this batch's project dir, the packages and the exporter binary are bound
        # a state dir below /dev or /proc is never visible anyway (--dev / --proc replace them): not
        # masked (a mask there could not be remounted read-only)
        st_mask = [] if (self.state + "/").startswith(("/dev/", "/proc/")) else [self.state]
        sbx = ["/usr/bin/bwrap", "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", 
               "--tmpfs", "/tmp", "--dir", "/tmp/home", "--tmpfs", "/run", "--tmpfs", "/var"] + self.bv.toplevel_masks() + \
            [y for x in st_mask for y in ("--tmpfs", x)] + [
               "--dev", "/dev", "--proc",
               "/proc", "--clearenv", "--ro-bind", self.tc, self.tc, "--ro-bind", batch.proj, batch.proj,
               "--ro-bind", self.ws_pk, self.ws_pk, "--ro-bind", self.native, self.native] + self.bv.toplevel_remount_ro(
               st_mask) + [
               "--setenv", "PATH", f"{self.tc}/bin:/usr/bin:/bin", "--setenv", "HOME", "/tmp/home", "--setenv", "LANG",
               "C.UTF-8", "--setenv", "LEAN_PATH", batch.lp, "--setenv", "LEAN_ABORT_ON_PANIC", "1",
               "--setenv", "LEAN4EXPORT_VERBOSE", "1", "--setenv", "LEAN4EXPORT_THREADS", str(thr),
               "--unshare-all", "--die-with-parent", "--new-session", "--chdir", batch.proj, "--",
               self.native, *mods, "--", *targets]
        errp = out + ".err"
        try:
            with open(out, "wb") as fo, open(errp, "wb") as fe:
                os.chmod(out, 0o600)
                t0 = time.time()
                pr = subprocess.Popen(sbx, stdout=fo, stderr=fe, env={})
                rc = None
                while True:
                    rc = pr.poll()
                    if rc is not None:
                        break
                    with open(errp, "rb") as g:   # export.sh's early return: 'done: names' = output complete
                        if b"s thread] done: names " in g.read():
                            pr.kill()
                            pr.wait()
                            rc = 0
                            break
                    time.sleep(0.01)
            log = open(errp, errors="replace").read()
            if rc != 0 or os.path.getsize(out) == 0:
                raise OSError(f"native exit {rc}")
            tn = round(time.time() - t0, 3)
            t1 = time.time()
            tg = out + ".tg"
            with open(tg, "w") as f:
                f.write("\n".join(targets) + "\n")
            p = subprocess.run([self.closure, out, tg, str(thr)], capture_output=True, text=True,
                               env={"PATH": "/usr/bin:/bin"})
            os.unlink(tg)
            if p.returncode != 0:
                raise OSError("closure guard: " + (p.stdout + p.stderr)[:300])
            os.unlink(errp)
            return out, log, os.path.getsize(out), tn, round(time.time() - t1, 3)
        except OSError as e:
            for x in (out, errp, out + ".tg"):
                try:
                    os.unlink(x)
                except OSError:
                    pass
            self.log(event="fast-export-fallback", batch=batch.bid, tag=tag, why=str(e)[:300])
            return None

    # ------------------------------------------------------------------ one batch = one batchverify run
    def batch_args(self, pset, attempts, out, nthreads):
        ps = self.psets[pset]
        return argparse.Namespace(
            pset=ps["dir"], attempts=attempts, out=out, challenge_sha256=ps["sha"], threads=nthreads, jobs=nthreads,
            packages=self.ws, toolchain=self.tc, fv=self.fv, export_dir=self.export_dir,
            skip_kernel_tc=self.a.skip_kernel_tc, snapshot_cache=os.path.join(self.state, "snap"),
            snapshot_header=self.a.snapshot_header, root_module=False, confirm_failures=self.confirm_failures,
            attempt_timeout=self.a.attempt_timeout, par=self.a.par, split=self.a.split, limits=self.limits)

    def run_batch(self, items, snapshot_only=False):
        with self.lock:
            self.nbatch += 1
            bid = self.nbatch
        t = time.time()
        bdir = os.path.join(self.bdir, f"b{bid:06d}")
        att = os.path.join(bdir, "attempts")
        pset = items[0].pset if items else next(iter(self.psets))
        with self.lock:     # adaptive: an idle service gives a batch all threads, a busy one shares them
            nth = max(2, self.a.threads // max(1, self.busy()[0])) if items else self.a.threads
        try:
            # creating the batch is inside the try: a failure (e.g. a damaged mode on the
            # batch dir) answers this batch's attempts NO-VERDICT instead of killing the batch thread (clients hung); a
            # batch dir whose mode lost the owner's rwx is repaired once (it is this service's own directory)
            try:
                os.makedirs(att)
            except PermissionError:
                os.chmod(self.bdir, 0o700)
                self.log(event="batch-dir-repaired", path=self.bdir)
                os.makedirs(att)
            for it in items:
                with open(os.path.join(att, it.theorem + ".lean"), "w") as f:
                    f.write(it.source)
            b = self.FastBatch(self.batch_args(pset, att, os.path.join(bdir, "out"), nth))
            b.bid = bid
            b.pset_name = pset
            if snapshot_only:
                b.make_snapshot()
                return
            for it in items:
                it.t_start = t
            byname = {it.theorem: it for it in items}
            b.early_cb = lambda bb, early: [self.answer(byname[n], bid, len(items), t, bb.res, None, bdir, early=True)
                                            for n in early if n in byname]
            b.run()
            res = b.res
            err = None
        except BaseException as e:          # a crash is never a verdict
            res, err = None, f"{type(e).__name__}: {e}"
        for it in items:
            if not it.done.is_set():
                self.answer(it, bid, len(items), t, res, err, bdir)
        try:
            self.prune(bdir)
        except Exception as e:   # noqa: BLE001 - pruning is housekeeping: never a dead batch thread
            self.log(event="prune-failed", batch=bid, why=str(e)[:200])

    def answer(self, it, bid, n, t, res, err, bdir, early=False):
        """build the JSON answer of one attempt from the batch result and release the waiting client (once)"""
        if it.done.is_set():
            return
        if True:
            r = {"id": it.id, "pset": it.pset, "theorem": it.theorem, "batch": bid, "batch_size": n,
                 "queue_s": round(it.t_start - it.t_submit, 3), "batch_s": round(time.time() - t, 3)}
            if early:
                r["early"] = True     # final compile verdict, answered before the batch's export + check
            if res is None:
                r.update(verdict="NO-VERDICT", why="service error: " + (err or "?")[:300])
            else:
                a = res["attempts"].get(it.theorem, {})
                r.update(verdict=a.get("verdict", "NO-VERDICT"), why=a.get("why", ""), build_exit=a.get("build_exit"),
                         build_s=a.get("build_s"))
                if a.get("confirmed_plain"):   # a compile failure under the snapshot / fork server, re-compiled by plain lean
                    r["confirmed_plain"] = True
                logp = os.path.join(bdir, "out", "log", "Attempt." + it.theorem + ".build.log")
                try:
                    r["compiler_output"] = open(logp, errors="replace").read()[:8000]
                except OSError:
                    r["compiler_output"] = ""
                r["exports"] = [{k: e.get(k) for k in ("tag", "n", "exit", "s", "size", "fast", "fast_fallback", "native_s", "guard_s")
                                 if k in e} for e in res.get("exports", [])]
                r["checks"] = [{"tag": c.get("tag"), "n": len(c.get("theorems", [])), "exit": c.get("exit"), "s": c.get("s"),
                                "check_wall_s": c.get("check_wall_s")} for c in res.get("checks", [])]
                r["snapshot_s"] = res.get("build", {}).get("snapshot_s")
            r["total_s"] = round(time.time() - it.t_submit, 3)
            it.result = r
            with self.lock:
                self.stats[r["verdict"]] += 1
                if early:
                    self.stats["early_answers"] += 1
                if r.get("confirmed_plain"):      # how often the speed-ups' failures were re-compiled, and how often
                    self.stats["confirm_plain"] += 1          # plain lean then COMPILED the attempt (a 'flip': the speed-up
                    if r.get("build_exit") == 0:              # would have caused a wrong REJECTED without the confirm)
                        self.stats["confirm_flips"] += 1
            self.log(event="verdict", **{k: v for k, v in r.items() if k != "compiler_output"})
            it.done.set()

    def prune(self, bdir):
        """keep the directories of the last --keep FINISHED batches (a batch still in flight is never removed: removing by
        name order deleted a long batch's directory while it ran -> NO-VERDICT for its attempts, found in a 48-way stream)"""
        with self.lock:
            self.finished.append(bdir)
            old = [self.finished.popleft() for _ in range(max(0, len(self.finished) - self.a.keep))]
        for d in old:
            self.bv.rm_tree(d)   # depth-safe, never raises

    # ------------------------------------------------------------------ queue + adaptive batching
    def submit(self, pset, theorem, source, client=""):
        with self.lock:
            self.nitem += 1
            it = Item(f"a{self.nitem:07d}", pset, theorem, source, client)
            self.pending.append(it)
            self.cv.notify_all()
        return it

    def cancel(self, it):
        """the client of a QUEUED attempt went away (timeout / disconnect): drop it before any work is spent on
        it. An attempt already in a batch is not touched (the batch shares one export + check). -> True if dropped."""
        with self.lock:
            if it.done.is_set() or it.t_start is not None:
                return False
            try:
                self.pending.remove(it)
            except ValueError:
                return False
            it.cancelled = True
            self.stats["cancelled"] += 1
        it.result = {"id": it.id, "pset": it.pset, "theorem": it.theorem, "verdict": "NO-VERDICT",
                     "why": "client disconnected before the attempt started", "total_s": round(time.time() - it.t_submit, 3)}
        it.done.set()
        self.log(event="cancelled", id=it.id, theorem=it.theorem)
        return True

    SUSPECT = re.compile(r"\bsorry\b|\bsorryAx\b|^\s*(private\s+|protected\s+)?axiom\b|\bnative_decide\b|\bimplemented_by\b|"
                         r"\bextern\b|debug\.skipKernelTC|\baddDecl\b|\bunsafe\b|run_cmd|run_tac|#eval", re.M)

    def suspect(self, it):
        """UNTRUSTED scheduling hint only: an attempt whose text mentions sorry / axiom / native_decide / unsafe / addDecl /
        run_cmd ... is likely to make a set check reject (one culprit costs an isolation round for every honest attempt
        of the batch), so it is checked alone. Never changes a verdict: every attempt is still judged by the trusted check."""
        return bool(self.SUSPECT.search(it.source))

    def take_batch(self):
        """the oldest pending attempt + further pending attempts of the same problem set with DIFFERENT theorems
        (batchverify: at most one attempt per theorem per batch), up to --max-batch, in arrival order; suspect attempts
        (see suspect) go alone. With --fair: per-client round robin instead of arrival order (take_batch_fair)."""
        if self.a.fair:
            return self.take_batch_fair()
        first = self.pending.popleft()
        batch, seen, keep = [first], {first.theorem}, collections.deque()
        if self.a.isolate_suspects and self.suspect(first):
            return batch
        while self.pending and len(batch) < self.a.max_batch:
            it = self.pending.popleft()
            if it.pset == first.pset and it.theorem not in seen and not (self.a.isolate_suspects and self.suspect(it)):
                batch.append(it)
                seen.add(it.theorem)
            else:
                keep.append(it)
        keep.extend(self.pending)
        self.pending = keep
        return batch

    def take_batch_fair(self):
        """(untrusted scheduling only) one client's burst (best-of-N, a misbehaving agent) must not make every other
        client wait behind it. The batch starts with the oldest attempt of the client served least recently and is filled
        round robin over the clients in that order (each time the client's oldest eligible attempt: same problem set,
        theorem not yet in the batch, not a suspect), up to --max-batch. Same batching rules as take_batch; only the order
        in which attempts are taken changes."""
        order = []                                   # clients with pending attempts, least recently served first
        byc = collections.OrderedDict()
        for it in self.pending:
            byc.setdefault(it.client, []).append(it)
        order = sorted(byc, key=lambda c: (self.served.get(c, 0), byc[c][0].t_submit))
        first = byc[order[0]][0]
        batch, seen = [first], {first.theorem}
        self.nserved += 1
        self.served[first.client] = self.nserved
        if not (self.a.isolate_suspects and self.suspect(first)):
            progress = True
            idx = {c: 0 for c in order}
            idx[first.client] = 1
            while len(batch) < self.a.max_batch and progress:
                progress = False
                for c in order:
                    lst = byc[c]
                    while idx[c] < len(lst):
                        it = lst[idx[c]]
                        idx[c] += 1
                        if it.pset == first.pset and it.theorem not in seen and not (self.a.isolate_suspects and self.suspect(it)):
                            batch.append(it)
                            seen.add(it.theorem)
                            self.nserved += 1
                            self.served[c] = self.nserved
                            progress = True
                            break
                    if len(batch) >= self.a.max_batch:
                        break
        taken = set(id(x) for x in batch)
        self.pending = collections.deque(x for x in self.pending if id(x) not in taken)
        if len(self.served) > 65536:              # forget clients that have nothing waiting
            waiting = set(x.client for x in self.pending)
            self.served = {c: n for c, n in self.served.items() if c in waiting}
        return batch

    def busy(self):
        """batches that count against --max-inflight. With --slow-after S (untrusted scheduling only), a batch that
        has run longer than S seconds moves to the slow lane and stops counting, so a few runaway attempts (each holds a
        batch until its timeout) cannot block every other agent's attempts; at most --max-slow batches are slow at once."""
        if not self.a.slow_after:
            return self.inflight, 0
        now = time.time()
        slow = sum(1 for t in self.started.values() if now - t > self.a.slow_after)
        return self.inflight - slow, slow

    def may_dispatch(self):
        fast, slow = self.busy()
        return fast < self.a.max_inflight and self.inflight < self.a.max_inflight + (self.a.max_slow if self.a.slow_after else 0)

    def dispatcher(self):
        while True:
            err = None
            with self.cv:
                while not self.stop_flag and (not self.pending or not self.may_dispatch()):
                    self.cv.wait(0.5 if self.a.slow_after else None)   # batches age without a notify
                if self.stop_flag:
                    return
                if self.a.linger > 0 and self.inflight == 0:
                    self.cv.wait(self.a.linger)
                    if self.stop_flag:
                        return
                    if not self.pending or not self.may_dispatch():   # the lingering attempts may have been cancelled
                        continue
                try:
                    batch = self.take_batch()
                except Exception as e:      # noqa: BLE001 - never let the only dispatcher thread die (defense in depth)
                    err = repr(e)[:300]
                    self.cv.wait(1.0)          # a persistent error must not spin (at most one log line per second)
                else:
                    now = time.time()
                    for it in batch:
                        it.t_start = now          # under the lock: cancel() leaves a dispatched attempt alone
                    self.inflight += 1
                    self.nlaunch += 1
                    key = self.nlaunch
                    self.started[key] = now
            if err is not None:                # log() takes self.lock (= the cv's lock, not reentrant): only outside it
                self.log(event="dispatch-error", error=err)
                continue
            threading.Thread(target=self._run, args=(batch, key), daemon=True).start()

    def _run(self, batch, key=None):
        try:
            self.run_batch(batch)
        finally:
            with self.cv:
                self.inflight -= 1
                self.started.pop(key, None)
                self.cv.notify_all()

    def bad_request(self, req, client=""):
        pset, thm, src = req.get("pset"), req.get("theorem"), req.get("source")
        if self.a.max_pending_per_client and client:   # one client cannot fill the queue for everybody
            with self.lock:
                mine = sum(1 for it in self.pending if it.client == client)
            if mine >= self.a.max_pending_per_client:
                with self.lock:
                    self.stats["client_queue_full"] += 1
                return f"queue full for this client ({mine} attempts waiting, --max-pending-per-client {self.a.max_pending_per_client}): retry later"
        if self.a.max_pending and len(self.pending) >= self.a.max_pending:   # a flood of requests waits nowhere
            with self.lock:
                self.stats["queue_full"] += 1
            return f"queue full ({len(self.pending)} attempts waiting, --max-pending {self.a.max_pending}): retry later"
        if pset not in self.psets:
            return "unknown problem set"
        if self.psets[pset].get("xversion_rc") == 1:
            return "REJECTED by the cross-version gate (a rule of the challenge release's own comparator fails)"
        if not isinstance(thm, str) or not NAME_RE.fullmatch(thm):   # no trailing line feed
            return "bad theorem name"
        if not isinstance(src, str) or len(src.encode("utf-8", "replace")) > MAX_SOURCE:
            return "source missing or too large"
        return None


class Handler(socketserver.StreamRequestHandler):
    def handle(self):
        svc = self.server.svc
        timer = None
        if svc.a.request_timeout:      # a client that never finishes its request line does not hold a thread forever
            self.connection.settimeout(svc.a.request_timeout)      # a silent client: per recv()
            # a TOTAL deadline for the request line: a client trickling a byte now and then never trips the
            # per-recv() timeout; at the deadline the connection is shut down, the read returns, the client is dropped
            conn = self.connection

            def cut():
                try:
                    conn.shutdown(socket.SHUT_RDWR)
                except OSError:
                    pass
            timer = threading.Timer(svc.a.request_timeout, cut)
            timer.daemon = True
            timer.start()
        try:
            line = self.rfile.readline(MAX_SOURCE * 2 + 4096)
            if timer is not None:
                timer.cancel()
            req = json.loads(line.decode("utf-8"))
        except (ValueError, UnicodeDecodeError):
            if timer is not None and not line.endswith(b"\n"):
                return                 # cut at the deadline: nothing to answer
            self.reply({"error": "bad request"})
            return
        except OSError:                # socket.timeout included
            return
        if not isinstance(req, dict):
            self.reply({"error": "bad request"})
            return
        self.connection.settimeout(None)
        op = req.get("op", "verify")
        if op == "verify":
            ckey = self.client_key(req)
            why = svc.bad_request(req, ckey)
            if why:
                # a theorem name the service cannot resolve (fvserve takes atomic names) was never
                # judged: NO-VERDICT, never REJECTED; only the cross-version gate's own rule is a rejection here
                self.reply({"verdict": "REJECTED" if why.startswith("REJECTED") else "NO-VERDICT",
                            "why": why})
                return
            it = svc.submit(req["pset"], req["theorem"], req["source"], ckey)
            while not it.done.wait(0.5):
                if self.client_gone() and svc.cancel(it):
                    return
            self.reply(it.result)
        elif op == "stats":
            with svc.lock:
                rep = {"uptime_s": round(time.time() - svc.t0, 1), "pending": len(svc.pending),
                       "inflight": svc.inflight, "slow": svc.busy()[1], "batches": svc.nbatch, "items": svc.nitem,
                       "verdicts": dict(svc.stats), "startup": svc.timing, "psets": sorted(svc.psets)}
            rep["code"] = {k: (v or "")[:16] for k, v in svc.code.items()}
            rep["stale"] = sorted(k for k, p in svc.code_files.items() if file_sha_or_none(p) != svc.code[k])
            self.reply(rep)
        elif op == "stop":
            self.reply({"stopping": True})
            threading.Thread(target=self.server.shutdown, daemon=True).start()
        else:
            self.reply({"error": "unknown op"})

    def client_key(self, req):
        """--fair: who sent this request - the request's "client" field (a front-end such as the HTTP API serving many
        agents through one connection pool should set it) or else the connecting process (SO_PEERCRED pid)"""
        c = req.get("client")
        if isinstance(c, str) and 0 < len(c) <= 128:
            return "c:" + c
        try:
            import struct
            pid, _, _ = struct.unpack("3i", self.connection.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))
            return f"p:{pid}"
        except (OSError, struct.error):
            return ""

    def client_gone(self):
        """the client closed its end (EOF readable without data) - one request per connection, nothing else is sent"""
        import select
        try:
            r, _, _ = select.select([self.connection], [], [], 0)
            if not r:
                return False
            return self.connection.recv(1, socket.MSG_PEEK) == b""
        except OSError:
            return True

    def reply(self, obj):
        try:
            self.wfile.write((json.dumps(obj) + "\n").encode())
        except OSError:
            pass


class Server(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True
    allow_reuse_address = True
    # socketserver's default listen backlog is 5; a client whose socket has a timeout (fvapi, MCP, fvclient
    # with --timeout) gets EAGAIN from connect() as soon as more than 5 connections wait to be accepted (measured: 33 of
    # 64 concurrent clients failed; 96 + 13 of 480 attempts from 24 concurrent clients)
    request_queue_size = 1024


def serve(a):
    svc = Service(a)
    svc.startup()
    sock = os.path.join(svc.state, "sock")
    try:
        os.unlink(sock)
    except OSError:
        pass
    srv = Server(sock, Handler)
    os.chmod(sock, 0o600)
    srv.svc = svc
    threading.Thread(target=svc.dispatcher, daemon=True).start()
    print(json.dumps({"event": "ready", "sock": sock, **svc.timing,
                      "code": {k: (v or "")[:16] for k, v in svc.code.items()}}), flush=True)
    signal.signal(signal.SIGTERM, lambda *_: threading.Thread(target=srv.shutdown, daemon=True).start())
    try:
        srv.serve_forever(poll_interval=0.2)
    finally:
        with svc.cv:
            svc.stop_flag = True
            svc.cv.notify_all()
        shutil.rmtree(svc.export_dir, ignore_errors=True)
        if svc.fork:
            svc.fork.stop()
        for wd in svc.warm_daemons.values():
            try:
                svc.warm_query(wd["state"], {"op": "stop"}, 10.0)
                wd["proc"].wait(timeout=10)
            except Exception:
                wd["proc"].kill()
            try:
                wd["log"].close()
            except Exception:
                pass
        try:
            os.unlink(sock)
        except OSError:
            pass


# ----------------------------------------------------------------------------------------------------------- client
def request(state, obj, timeout=None):
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:   # closed on a timeout too: the service then drops a
        s.settimeout(timeout)                                       # still-queued attempt
        end = time.time() + (timeout if timeout else 3600)
        while True:            # a full listen backlog gives EAGAIN on a socket with a timeout: retry until the deadline
            try:
                s.connect(os.path.join(state, "sock"))
                break
            except BlockingIOError:
                if time.time() >= end:
                    raise socket.timeout("connect: service backlog full until the deadline")
                time.sleep(0.02)
        if timeout:                    # one deadline for connect + request + answer
            s.settimeout(max(0.001, end - time.time()))
        s.sendall((json.dumps(obj) + "\n").encode())
        buf = b""
        while not buf.endswith(b"\n"):
            c = s.recv(1 << 16)
            if not c:
                break
            buf += c
    return json.loads(buf.decode())


# measured configurations: `serve --profile NAME` inserts these flags at the
# position of --profile, so anything given after it overrides them (argparse keeps the last value)
LIMITS_RECOMMENDED = "mem=2G,nproc=512,procs=64,threads=256,out=16M,disk=64M,fsize=64M,cpu=120"   # 1,908 real attempts: 0 ended
PROFILES = {
    # a service shared by many agents: per-attempt limits, slow lane, fair scheduling, queue cap, request deadline
    "shared": ["--svc-check", "--limits", LIMITS_RECOMMENDED, "--attempt-timeout", "120", "--slow-after", "10",
               "--max-slow", "8", "--fair", "--max-pending", "512", "--request-timeout", "10"],
    # a laptop / 8-16 GB machine: the same, one batch in flight (~1.7 GB + 3.1 GB per batch), a smaller queue
    "laptop": ["--svc-check", "--limits", LIMITS_RECOMMENDED, "--attempt-timeout", "120", "--max-inflight", "1",
               "--slow-after", "10", "--max-slow", "1", "--fair", "--max-pending", "64", "--request-timeout", "10"],
}


def expand_profile(argv):
    """['serve', ..., '--profile', 'shared', ...] -> the profile's flags inserted at that position (also '--profile=shared')"""
    out, i = [], 0
    while i < len(argv):
        x = argv[i]
        name = x.split("=", 1)[1] if x.startswith("--profile=") else (argv[i + 1] if x == "--profile" and i + 1 < len(argv) else None)
        if name is not None:
            if name not in PROFILES:
                raise SystemExit(f"fvserve: unknown --profile {name} (known: {', '.join(sorted(PROFILES))})")
            out += PROFILES[name]
            i += 1 if x.startswith("--profile=") else 2
            continue
        out.append(x)
        i += 1
    return out


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


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("serve")
    s.add_argument("--state", required=True)
    s.add_argument("--pset", action="append", required=True, help="NAME=PSETDIR:SHA256 (official challenge export pin)")
    s.add_argument("--profile", choices=sorted(PROFILES), default=None,
                   help="measured flag sets (expanded where --profile stands; later flags override): shared = "
                        + " ".join(PROFILES["shared"]) + "; laptop = " + " ".join(PROFILES["laptop"]))
    s.add_argument("--threads", type=int, default=os.cpu_count())
    s.add_argument("--max-inflight", type=int, default=4, help="batches in flight at once")
    s.add_argument("--max-batch", type=int, default=64, help="attempts per batch (distinct theorems)")
    s.add_argument("--no-isolate-suspects", dest="isolate_suspects", action="store_false",
                   help="do not check attempts that mention sorry/axiom/native_decide/... alone")
    s.add_argument("--linger", type=float, default=0.0, help="seconds an idle service waits to collect a batch")
    s.add_argument("--packages", default=default_packages(),
                   help="trusted Lake workspace with .lake/packages (default: $FV_PACKAGES, else <repository root>/verify/challenge if present)")
    s.add_argument("--toolchain", default=default_toolchain(),
                   help="official Lean 4.33.1 toolchain (default: the registered one in config/components.json)")
    s.add_argument("--fv", default=os.path.join(HERE, "..", ".."))
    s.add_argument("--export-dir", default=None, help="parent of the private export dir (default /dev/shm)")
    s.add_argument("--check-script", default=None, help="trusted check (default check/sound/check-sound.sh)")
    s.add_argument("--check-arg", action="append", default=[], help="extra argument of the trusted check")
    s.add_argument("--pins", default=None,
                   help="pins file of the trusted check, e.g. check/sound/pins-437.env = the judge built from Lean "
                        "4.37.0-rc1: passed to check-sound(-svc).sh --pins at the preflight and every check; must be a "
                        "pins*.env in this package's check/sound/ (as bin/fastverify --pins). Default: the 4.36 pins.env")
    s.add_argument("--svc-check", action="store_true",
                   help="trusted check = check/sound/check-sound-svc.sh --integrity-cache STATE/icache (pins + 4.36 tree "
                        "verified fully at start, then compared by stamp)")
    s.add_argument("--warm-check", action="store_true",
                   help="opt-in persistent warm delta verification (lean4export-delta + fvcheckd; automatic Tier-2 & cold fallback)")
    s.add_argument("--warm-base", default=None, help="base export for --warm-check (default: each pset's challenge.export; e.g. mathlib.export)")
    s.add_argument("--warm-bins", default="/scratch/fastverify-next/warm/v1", help="dir containing ccmp-warm, pleanchecker-warm, gruszka-warm, lean4export-delta (default: the pinned install prefix /scratch/fastverify-next/warm/v1)")
    s.add_argument("--warm-src", default=None, help="dir containing fvcheckd.py (default: FV/check/warm)")
    s.add_argument("--warmup", default=None, help="NAME:THEOREM:FILE verified once at start")
    s.add_argument("--keep", type=int, default=16, help="batch directories kept for inspection")
    s.add_argument("--no-fast-export", action="store_true")
    s.add_argument("--snapshot-header", default="import Mathlib")
    s.add_argument("--fork-server", default=None,
                   help="path of the fvfork binary (fork/build.sh): attempts with the snapshot header are elaborated in "
                        "forked children of one process that loaded the header snapshot once (untrusted; fallback: lean)")
    s.add_argument("--skip-kernel-tc", action="store_true")
    s.add_argument("--attempt-timeout", type=float, default=600)
    s.add_argument("--limits", default=None,
                   help="per-attempt resource limits of every compile, also of fork-server children, e.g. 'mem=8G,nproc=512,"
                        "procs=64,cpu=900,fsize=1G,out=64M,disk=2G' (tools/guard; default off): a limit hit -> NO-VERDICT")
    s.add_argument("--slow-after", type=float, default=0,
                   help="a batch running longer than this many seconds stops counting against --max-inflight (slow lane; "
                        "0 = off): runaway attempts cannot block everyone else's")
    s.add_argument("--max-slow", type=int, default=4, help="batches allowed in the slow lane at once (with --slow-after)")
    s.add_argument("--fair", action="store_true",
                   help="per-client round-robin batching (client = the request's \"client\" field or the connecting process) "
                        "instead of arrival order: one client's burst does not delay the others")
    s.add_argument("--max-pending-per-client", type=int, default=0,
                   help="answer NO-VERDICT 'queue full for this client' when this client already has this many attempts waiting "
                        "(client as for --fair; 0 = unlimited)")
    s.add_argument("--max-pending", type=int, default=0,
                   help="answer NO-VERDICT 'queue full' at once when this many attempts already wait (0 = unlimited)")
    s.add_argument("--request-timeout", type=float, default=0,
                   help="seconds a client may take to send its request line (0 = no limit)")
    s.add_argument("--par", type=int, default=8)
    s.add_argument("--split", type=int, default=4)
    c = sub.add_parser("submit")
    c.add_argument("--state", required=True)
    c.add_argument("--pset", required=True)
    c.add_argument("--theorem", required=True)
    c.add_argument("--timeout", type=float, default=None)
    c.add_argument("file")
    for n in ("stats", "stop"):
        x = sub.add_parser(n)
        x.add_argument("--state", required=True)
    argv = sys.argv[1:]
    profile = None
    for k, x in enumerate(argv):
        if x.startswith("--profile="):
            profile = x.split("=", 1)[1]
        elif x == "--profile" and k + 1 < len(argv):
            profile = argv[k + 1]
    a = ap.parse_args(expand_profile(argv) if argv[:1] == ["serve"] else argv)
    if a.cmd == "serve":
        a.profile = profile
        serve(a)
    elif a.cmd == "submit":
        r = request(a.state, {"op": "verify", "pset": a.pset, "theorem": a.theorem, "source": open(a.file).read()},
                    a.timeout)
        print(json.dumps(r))
        sys.exit({"ACCEPTED": 0, "REJECTED": 1}.get(r.get("verdict"), 2))
    else:
        print(json.dumps(request(a.state, {"op": a.cmd}, 30)))


if __name__ == "__main__":
    reset_child_signals()
    main()

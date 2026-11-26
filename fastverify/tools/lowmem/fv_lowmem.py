#!/usr/bin/python3 -I
"""
fastverify/tools/lowmem/fv_lowmem.py — End-to-end low-memory sound verifier CLI.

Supports BOTH:
  1. Export-in mode (`--from-export SOL.export`):
     Copies SOL.export into a private 0700 OUT directory (reflink where available) and runs
     `check/lowmem/check-sound-lowmem.sh --private-inputs` (sequential 3-leg sound check with
     2-pass mmap CSR + selective Expr `ccmp-lowmem` -> `pleanchecker` -> `gruszka`).
  2. Sources-in mode (`PROJECT CHALLENGE OUT`):
     Detects host/cgroup memory budget, builds the challenge officially if `challenge.export` is absent,
     builds the project in a clean bwrap sandbox (capping parallel `lean` jobs to fit the memory budget
     without OOM-thrashing), exports via `export/export-lowmem.sh` (`lean4export-lowmem`
     `LEAN4EXPORT_LOWMEM=1`, falling back to official `E0`), and judges via
     `check/lowmem/check-sound-lowmem.sh --private-inputs`.

Exit codes (identical to `bin/fastverify --preset sound`):
  0 = ACCEPTED (all 3 trusted legs accepted + challenge sha256 matched)
  1 = REJECTED (the build failed officially, or the trusted check rejected; a failed EXPORT is never
      REJECTED: exit 2 ERROR)
  2 = ERROR / DECLINED (no verdict: OOM, timeout, pin mismatch, tampered challenge)
"""
import os
import sys


# the caller's environment never reaches a stage: like bin/fastverify (`env -i PATH=/usr/bin:/bin
# LANG=C.UTF-8 /usr/bin/python3 -I`, finding 016) this script re-executes itself in exactly that environment before anything
# else runs, and every child gets an explicit fixed env (child_env). Passing os.environ to build/official-build.sh would let
# BASH_ENV make a shell function replace the verified lake, and PATH make a fake `tr` move where the challenge .oleans are read from
# (ACCEPTED, trust sound, for a challenge stating 0 = 1). Only builtin modules are imported above this point.
def _clean_env():
    return (set(os.environ) <= {"PATH", "LANG"} and os.environ.get("PATH") == "/usr/bin:/bin"
            and os.environ.get("LANG") == "C.UTF-8" and sys.flags.isolated == 1)


if __name__ == "__main__":
    for _fd in (0, 1, 2):   # a closed standard fd is reopened on /dev/null: no later file (OUT's
        try:                # result.json, a stage's pipe) can land on fd 0-2, and sys.stderr is never None below
            os.fstat(_fd)
        except OSError:
            os.open(os.devnull, os.O_RDWR)
    if not _clean_env():
        if sys.argv[1:2] == ["--clean-env-reexec"]:
            try:
                sys.stderr.write("fv_lowmem: environment not clean after the env -i re-exec (refused)\n")
            except (AttributeError, OSError, ValueError):
                pass
            os._exit(2)
        os.execv("/usr/bin/env", ["/usr/bin/env", "-i", "PATH=/usr/bin:/bin", "LANG=C.UTF-8", "/usr/bin/python3", "-I",
                                  os.path.realpath(__file__), "--clean-env-reexec"] + sys.argv[1:])
    if sys.argv[1:2] == ["--clean-env-reexec"]:
        del sys.argv[1]
    # signal dispositions survive env -i / exec: a caller could start this run with SIGCHLD ignored
    # (every child then reads as exit 0: a failing toolchain verify "passed", and the run hung). As in bin/fastverify,
    # only what breaks correctness is reset: SIGCHLD -> default and the inherited signal mask
    # cleared; SIGTERM -> default so that _main() installs its handler (a SIGTERM always ends the run as ERROR). SIGHUP and
    # SIGINT keep their inherited disposition: an ignored one (nohup, a background job) stays ignored, so a nohup run
    # survives its terminal; otherwise _main() handles them like SIGTERM. SIGPIPE stays ignored in
    # Python (a closed stdout is a BrokenPipeError); subprocess restores SIG_DFL in every stage (restore_signals)
    import signal as _signal
    for _s in (_signal.SIGCHLD, _signal.SIGTERM):
        _signal.signal(_s, _signal.SIG_DFL)
    _signal.pthread_sigmask(_signal.SIG_SETMASK, set())
    _signal.signal(_signal.SIGPIPE, _signal.SIG_IGN)
    # the umask survives env -i / exec: a caller's 0777 / 0277 made OUT unusable (the error
    # handler then crashed: exit 1 = REJECTED). Everything this run creates is private to the caller anyway
    os.umask(0o077)

import argparse
import hashlib
import json
import re
import shutil
import signal
import stat
import subprocess
import time

HERE = os.path.dirname(os.path.realpath(__file__))
FV = os.path.dirname(os.path.dirname(HERE))
PRIMITIVES = [
    "Nat", "Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd",
    "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
    "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
]
HOST_ERROR_RE = (
    r"No space left on device|Cannot allocate memory|Resource temporarily unavailable|"
    r"failed to create thread|Too many open files|mmap.*failed|out of memory|std::bad_alloc|"
    r"Stale file handle|failed to read file '"
)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def detect_budget():
    cpus = len(os.sched_getaffinity(0))
    mem_mb = None
    try:
        for ln in open("/proc/self/cgroup"):
            p = ln.strip().split(":", 2)
            if len(p) == 3 and p[0] == "0":
                d = "/sys/fs/cgroup" + p[2]
                while d.startswith("/sys/fs/cgroup"):
                    mp = os.path.join(d, "memory.max")
                    if os.path.exists(mp):
                        v = open(mp).read().strip()
                        if v and v != "max":
                            mb = int(v) // (1024 * 1024)
                            mem_mb = mb if mem_mb is None else min(mem_mb, mb)
                    if d == "/sys/fs/cgroup":
                        break
                    d = os.path.dirname(d)
    except Exception:
        pass
    avail_mb = None
    try:
        for ln in open("/proc/meminfo"):
            if ln.startswith("MemAvailable:"):
                avail_mb = int(ln.split()[1]) // 1024
                break
    except Exception:
        pass
    eff_mb = min(x for x in (mem_mb, avail_mb) if x is not None) if (mem_mb or avail_mb) else 16384
    return cpus, mem_mb, eff_mb


def parse_last_json(txt):
    for ln in reversed(txt.splitlines()):
        ln = ln.strip()
        if ln.startswith("{") and ln.endswith("}"):
            try:
                return json.loads(ln)
            except Exception:
                pass
    return None


def copy_clean_project(src, dst):
    src_real = os.path.realpath(src)
    for root, dirs, files in os.walk(src_real):
        if os.path.realpath(root) == src_real and ".lake" in dirs:
            dirs.remove(".lake")
        for n in dirs + files:
            st = os.lstat(os.path.join(root, n))
            if not (stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode) or stat.S_ISLNK(st.st_mode)):
                raise RuntimeError(f"special file in project: {os.path.join(root, n)}")
    shutil.copytree(
        src_real,
        dst,
        symlinks=True,
        ignore=lambda d, names: [".lake"] if os.path.realpath(d) == src_real else [],
    )
    for root, dirs, files in os.walk(dst):
        for n in dirs + files:
            p = os.path.join(root, n)
            if os.path.islink(p):
                t = os.path.realpath(p)
                if not (t == dst or t.startswith(dst + os.sep)):
                    raise RuntimeError(f"symlink escapes project: {os.path.relpath(p, dst)}")


def resolve_toolchain(tc_str, comps):
    """the toolchain and official exporter of a release, resolved exactly as bin/fastverify
    and tools/subcontract/common.py do: only a toolchain REGISTERED in config/components.json (lean_toolchains),
    its whole tree verified against its pinned manifest (lib/toolchain.py verify), and its official exporter
    (official_lean4export) present with the pinned sha256. Anything else raises RuntimeError: no unverified
    ~/.elan/toolchains/<id> fallback and no hard-coded env/tools lean4export path. Returns
    (prefix, exporter)."""
    tcs = comps.get("lean_toolchains") or {}
    lt = tcs.get(tc_str) if isinstance(tc_str, str) else None
    prefix = (lt or {}).get("prefix")
    if not lt or not prefix or not os.path.isdir(prefix):
        raise RuntimeError(f"toolchain {tc_str!r} is not a registered official toolchain (config/components.json "
                           "lean_toolchains; register it with tools/addrelease.py)")
    if not os.path.isabs(prefix) or os.path.realpath(prefix) != os.path.normpath(prefix) or prefix != os.path.normpath(prefix):
        # the registered prefix itself: absolute, no symlinked component, no trailing slash
        raise RuntimeError(f"toolchain {tc_str}: registered prefix {prefix!r} is not a canonical path (refused)")
    try:   # a host failure here is no verdict (RuntimeError -> exit 2 ERROR), never a traceback
        r = run_stage(["/usr/bin/python3", "-I", os.path.join(FV, "lib", "toolchain.py"), "verify", prefix, tc_str],
                           capture_output=True, text=True, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}, timeout=900)
    except (OSError, subprocess.SubprocessError) as e:
        raise RuntimeError(f"toolchain {tc_str}: lib/toolchain.py verify could not run: {e}")
    if r.returncode != 0:
        raise RuntimeError(f"toolchain {tc_str} at {prefix} does not verify against its pinned manifest (lib/toolchain.py "
                           f"verify): {(r.stderr or r.stdout).strip()[-300:]}")
    e = lt.get("official_lean4export") or {}
    off_exp, want = e.get("path"), e.get("sha256")
    if not off_exp or not want or not os.path.isfile(off_exp):
        raise RuntimeError(f"no registered official exporter for {tc_str} (config/components.json official_lean4export)")
    if not os.path.isabs(off_exp) or os.path.realpath(off_exp) != os.path.normpath(off_exp) or off_exp != os.path.normpath(off_exp):
        raise RuntimeError(f"official exporter path {off_exp!r} for {tc_str} is not a canonical path (refused)")
    try:
        have = sha256_file(off_exp)
    except OSError as e:
        raise RuntimeError(f"official exporter {off_exp} unreadable: {e}")
    if have != want:
        raise RuntimeError(f"official exporter {off_exp} sha256 {have} differs from its pin {want} (config/components.json)")
    return prefix, off_exp, want


def private_exporter(off_exp, want, out):
    """a private copy of the official exporter in OUT (0700), hashed AFTER copying: the copy is
    what runs (bound at the exporter's own path inside the sandbox, so $ORIGIN/../lib still resolves into the verified
    toolchain), so swapping the registered file after the check (or swap-and-restore) changes nothing"""
    d = os.path.join(out, ".exporter")
    os.makedirs(d, mode=0o700, exist_ok=True)
    cp = os.path.join(d, want[:16] + "-" + os.path.basename(off_exp))   # one copy per pinned exporter, reused
    try:
        if not os.path.exists(cp):
            shutil.copyfile(off_exp, cp)
            os.chmod(cp, 0o500)
        have = sha256_file(cp)
    except OSError as e:
        raise RuntimeError(f"official exporter {off_exp}: private copy failed: {e}")
    if have != want:
        raise RuntimeError(f"official exporter copy sha256 {have} differs from its pin {want}")
    return cp


def resolve_lowmem_pins(given_pins, chal_tc):
    """Boundary B4: --pins must name a pins*.env file directly inside check/lowmem/ (no caller paths or symlink escape)."""
    import glob
    lm_dir = os.path.realpath(os.path.join(FV, "check", "lowmem"))
    chk_script = os.path.join(lm_dir, "check-sound-lowmem.sh")
    try:
        has_pins_flag = "--pins" in open(chk_script, encoding="utf-8", errors="replace").read()
    except OSError:
        has_pins_flag = False
    if given_pins:
        if given_pins in ("436", "default"):
            return None
        if given_pins == "437":
            given_pins = os.path.join(lm_dir, "pins-437.env")
        p = os.path.realpath(given_pins if os.path.isabs(given_pins) else os.path.join(FV, given_pins))
        if os.path.dirname(p) != lm_dir or not os.path.basename(p).startswith("pins") or not p.endswith(".env") or not os.path.isfile(p):
            raise RuntimeError(f"--pins {given_pins}: must name a pins*.env file in {lm_dir}")
        if os.path.realpath(os.path.join(lm_dir, "pins.env")) == p:
            return None
        if not has_pins_flag:
            raise RuntimeError("check-sound-lowmem.sh does not support --pins yet")
        return p
    if chal_tc and has_pins_flag:
        for f in sorted(glob.glob(os.path.join(lm_dir, "pins-*.env"))):
            try:
                tv = [ln.split("=", 1)[1].strip() for ln in open(f, encoding="utf-8") if ln.startswith("TC_VERSION=")]
            except OSError:
                continue
            if tv and tv[0] == chal_tc:
                p = os.path.realpath(f)
                if p != os.path.realpath(os.path.join(lm_dir, "pins.env")):
                    return p
    return None


def run_official_export_bwrap(tc_prefix, off_exp, proj_dir, lean_path, module, targets, binds, out_export, log_path,
                              exp_copy=None):
    cmd = [
        "/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session",
        "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run", "--tmpfs", "/tmp",
        "--dev", "/dev", "--proc", "/proc",
        "--ro-bind", tc_prefix, tc_prefix,
        "--ro-bind", proj_dir, proj_dir,
        "--ro-bind", exp_copy or off_exp, off_exp,   # the hashed private copy, at the exporter's path
    ]
    for b in binds:   # each dependency checkout (src, in the packages workspace) bound
        # read-only AT its place in the work copy (dst), exactly as lib/fastverify.py sandbox_argv and export-lowmem.sh do;
        # (binding the EMPTY dst onto itself gave an unknown module prefix for every dependency: false REJECTED)
        src = b[0]
        dst = b[1] if len(b) > 1 and b[1] else src
        if not os.path.isdir(src):
            with open(log_path, "ab") as lf:
                lf.write(f"fv_lowmem: dependency checkout {src} missing\n".encode())
            return 2
        if dst != src:
            if not os.path.normpath(dst).startswith(proj_dir.rstrip("/") + "/"):
                with open(log_path, "ab") as lf:
                    lf.write(f"fv_lowmem: dependency mount point {dst} outside the work copy {proj_dir}\n".encode())
                return 2
            os.makedirs(dst, exist_ok=True)
        cmd += ["--ro-bind", src, dst]
    cmd += [
        "--chdir", proj_dir,
        "--setenv", "HOME", "/tmp",
        "--setenv", "TMPDIR", "/tmp",
        "--setenv", "LANG", "C.UTF-8",
        "--setenv", "PATH", f"{tc_prefix}/bin:/usr/bin:/bin",
        "--setenv", "LEAN_PATH", lean_path,
        "--setenv", "LEAN_ABORT_ON_PANIC", "1",
        "--", off_exp, module, "--",
    ] + list(targets)
    with open(out_export, "wb") as outf, open(log_path, "wb") as lf:
        p = run_stage(cmd, stdout=outf, stderr=subprocess.PIPE, env={})
        lf.write(p.stderr)
    rc = p.returncode if p.returncode >= 0 else 128 - p.returncode
    if rc != 0:
        if rc in (137, 143) or re.search(HOST_ERROR_RE, p.stderr.decode("utf-8", "replace")):
            return 2
        return 1
    return 0


RSH = None   # --require-sorried-holes, recorded in EVERY result.json
_STAGES = []     # the running stage processes (each the leader of its own process group)
EXPORTERS = []   # {"source", "sha256"} of the official exporter copies used: recorded, the copies deleted


def run_stage(cmd, capture_output=False, text=False, env=None, timeout=None, stdout=None, stderr=None):
    """subprocess.run in a NEW process group, tracked, so that SIGTERM can kill the whole stage tree"""
    if capture_output:
        stdout = stderr = subprocess.PIPE
    p = subprocess.Popen(cmd, stdout=stdout, stderr=stderr, text=text, env=env, start_new_session=True)
    _STAGES.append(p)
    try:
        try:
            o, e = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except OSError:
                pass
            p.communicate()
            raise
    finally:
        _STAGES.remove(p)
    return subprocess.CompletedProcess(cmd, p.returncode, o, e)


_XV = []
S1_NAMES = ("propext", "Quot.sound", "Classical.choice")


def lean_name(x):
    """(as in bin/fastverify) the canonical Lean name (component tuple) of a config
    string: check/xversion/xvcheck.py parse_lean_name, loaded once by path = the exact `String.toName` mirror the judges
    (q02_canon) and the official comparator use. `«propext»` and `propext` are the same name; `«Quot.sound»` is the
    ONE-component name «Quot.sound» (not Quot.sound); () for a non-string or a string that is no name"""
    if not _XV:
        import importlib.util
        xp = os.path.join(FV, "check", "xversion", "xvcheck.py")
        spec = importlib.util.spec_from_file_location("fv_lowmem_xvcheck", xp)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"{xp} missing: Lean names cannot be read")
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        _XV.append(m)
    return _XV[0].parse_lean_name(x) if isinstance(x, str) else ()


def lean_names(xs):
    """the canonical names of a config list (a non-list has none)"""
    return {lean_name(x) for x in xs} if isinstance(xs, list) else set()


def integrity_cache_dir():
    """bin/fastverify's integrity record directory (lib/fastverify.py integrity_cache_dir):
    /tmp/fastverify-icache-UID/<sha256(host, package root)[:16]>, both levels 0700 and ours, else None (full verification)"""
    import socket
    uid = os.getuid()
    top = f"/tmp/fastverify-icache-{uid}"
    sub = os.path.join(top, hashlib.sha256(f"{socket.gethostname()}\0{os.path.realpath(FV)}".encode()).hexdigest()[:16])
    for d in (top, sub):
        try:
            os.mkdir(d, 0o700)
        except FileExistsError:
            pass
        except OSError:
            return None
        try:
            st_d = os.lstat(d)
        except OSError:
            return None
        if not stat.S_ISDIR(st_d.st_mode) or st_d.st_uid != uid or (st_d.st_mode & 0o077):
            return None
    return sub


def write_result(out, res):
    """every result.json: require_sorried_holes, the official exporters used (source + sha256); the private
    exporter copies are deleted (they were ~221 MB per run for 4.33.1)"""
    if RSH is not None:
        res.setdefault("require_sorried_holes", RSH)
    if EXPORTERS:
        res["official_exporters"] = list(EXPORTERS)
    shutil.rmtree(os.path.join(out, ".exporter"), ignore_errors=True)
    # a result that cannot be recorded is no verdict (ResultWriteError -> exit 2);
    # written to a temp file and renamed: result.json is complete or absent (a file-size limit left just "{")
    tmp_r = os.path.join(out, ".result.json.tmp.%d" % os.getpid())
    try:
        with open(tmp_r, "w") as f:
            json.dump(res, f, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_r, os.path.join(out, "result.json"))
    except OSError as e:
        try:
            os.unlink(tmp_r)
        except OSError:
            pass
        raise ResultWriteError(f"cannot write {out}/result.json: {e}")
    try:   # a closed / broken stdout only loses the copy on stdout
        print(json.dumps(res), flush=True)
    except (BrokenPipeError, OSError, ValueError, AttributeError):
        try:
            os.dup2(os.open(os.devnull, os.O_WRONLY), 1)
        except OSError:
            pass


class ResultWriteError(Exception):
    """result.json could not be written: no verdict"""


def child_env(out):
    """the fixed environment of every stage (as lib/fastverify.py child_env)"""
    h, t = os.path.join(out, ".home"), os.path.join(out, ".tmp")
    os.makedirs(h, mode=0o700, exist_ok=True)
    os.makedirs(t, mode=0o700, exist_ok=True)
    return {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "HOME": h, "TMPDIR": t}


def emit_err(out, reason, stage_sec=None):
    res = {"verdict": "ERROR", "exit": 2, "trust": "none", "reason": reason}
    if stage_sec is not None:
        res["stage_seconds"] = stage_sec
    write_result(out, res)
    return 2


OUT_DIR = None


def main():
    """any uncaught exception is no verdict: exit 2 ERROR with result.json (never a traceback with
    exit 1 = REJECTED)"""
    try:
        rc = _main()
    except SystemExit:
        raise
    except BaseException as e:  # noqa: BLE001
        if OUT_DIR and os.path.isdir(OUT_DIR) and not isinstance(e, ResultWriteError):
            try:   # the handler itself can fail (unwritable OUT): still exit 2
                return emit_err(OUT_DIR, f"internal error (no verdict): {e!r}"[:400])
            except BaseException:  # noqa: BLE001
                pass
        _stderr(f"fv_lowmem: internal error (no verdict): {e!r}")
        return 2
    return rc if rc in (0, 1, 2) else 2


def _stderr(msg):
    try:
        print(msg, file=sys.stderr, flush=True)
    except (AttributeError, OSError, ValueError):
        pass


def _main():
    global OUT_DIR, RSH
    ap = argparse.ArgumentParser(description="Low-memory sound Lean 4 verification", allow_abbrev=False)
    ap.add_argument("project", help="Project directory (or '-' with --from-export)")
    ap.add_argument("challenge", help="Challenge directory (comparator.json + challenge.export or challenge sources)")
    ap.add_argument("out", help="Fresh output directory (must not exist or must be empty)")
    ap.add_argument("--from-export", dest="export_in", help="Verify an existing .export file directly")
    ap.add_argument("--challenge-sha256", help="Expected SHA-256 of challenge.export (64 hex chars)")
    ap.add_argument("--comparator-sha256", help="Expected SHA-256 of comparator.json (64 hex chars)")
    ap.add_argument("--pins", help="Judge pins file inside check/lowmem/ (e.g. check/lowmem/pins-437.env or 437)")
    ap.add_argument("--packages", help="Workspace with .lake/packages")
    ap.add_argument("--threads", type=int, default=0, help="Max threads (0 = auto from CPU/memory budget)")
    ap.add_argument("--mem-budget-mb", type=int, default=0, help="Explicit memory budget in MiB")
    ap.add_argument("--integrity-cache", nargs="?", const="auto",
                    help="use the pin integrity record cache: always bin/fastverify's private per-user, "
                         "per-package directory /tmp/fastverify-icache-UID/<hash>; a DIR given here is not used")
    ap.add_argument("--timeout", type=int, default=0, help="Check timeout in seconds")
    ap.add_argument("--require-sorried-holes", action="store_true",
                    help="(as bin/fastverify) the trusted judge refuses (DECLINED) a challenge whose definition holes "
                         "are not sorried, for every Lean release (default off = the official 4.36 semantics before 4.37; "
                         "4.37 challenges always get the rule); recorded in result.json")
    a = ap.parse_args()

    t0 = time.time()
    if a.challenge_sha256 is not None and not re.fullmatch(r"[0-9a-f]{64}", a.challenge_sha256):
        print("fv_lowmem: --challenge-sha256 must be 64 lowercase hex digits", file=sys.stderr)
        return 2
    if a.comparator_sha256 is not None and not re.fullmatch(r"[0-9a-f]{64}", a.comparator_sha256):
        print("fv_lowmem: --comparator-sha256 must be 64 lowercase hex digits", file=sys.stderr)
        return 2
    # OUT normalized first ('sym_out/.' and 'sym_out/' are 'sym_out'), no '..' component, and
    # neither OUT itself nor a directory on its way is a symlink (checking only the raw string let 'sym_out/.'
    # write through the link)
    if not a.out or "\x00" in a.out or ".." in a.out.split("/"):
        print(f"fv_lowmem: OUT {a.out!r}: empty or with a '..' component (refused)", file=sys.stderr)
        return 2
    out_p = os.path.abspath(a.out)
    if os.path.islink(out_p):   # OUT itself is never a symlink (dangling or not)
        print(f"fv_lowmem: OUT {a.out} is a symlink (refused)", file=sys.stderr)
        return 2
    if os.path.realpath(os.path.dirname(out_p)) != os.path.dirname(out_p):
        print(f"fv_lowmem: OUT {a.out}: a directory on its path is a symlink (refused; give the resolved path)", file=sys.stderr)
        return 2
    out_real = out_p   # as bin/fastverify: OUT is disjoint from PROJECT
    for d, what in ((a.project, "PROJECT"), (a.challenge, "CHALLENGE")):   # and CHALLENGE (not equal, inside, or containing)
        if what == "PROJECT" and d in ("", "-"):   # only the project has the '-' placeholder
            continue
        d = os.path.realpath(d)
        if out_real == d or out_real.startswith(d.rstrip("/") + "/") or d.startswith(out_real.rstrip("/") + "/"):
            print(f"fv_lowmem: OUT {out_real} must not be inside {what} {d} (or contain it)", file=sys.stderr)
            return 2
    if os.path.lexists(out_p):   # an existing OUT: a directory of ours, checked empty BEFORE its
        # mode is touched (a non-empty directory is refused unchanged), then made 0700 through an O_NOFOLLOW fd and checked
        # empty once more (nobody else can add entries afterwards)
        try:
            ofd = os.open(out_p, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        except OSError as e:
            print(f"fv_lowmem: OUT {a.out} exists and is not a directory ({e.strerror}; refused)", file=sys.stderr)
            return 2
        try:
            if os.fstat(ofd).st_uid != os.getuid():
                print(f"fv_lowmem: OUT {a.out} is not owned by the caller (refused)", file=sys.stderr)
                return 2
            if os.listdir(ofd):
                print(f"fv_lowmem: OUT {a.out} exists and is non-empty", file=sys.stderr)
                return 2
            os.fchmod(ofd, 0o700)
            if os.listdir(ofd):
                print(f"fv_lowmem: OUT {a.out} changed while it was checked (refused)", file=sys.stderr)
                return 2
        finally:
            os.close(ofd)
    else:
        os.makedirs(os.path.dirname(out_p), mode=0o700, exist_ok=True)
        os.mkdir(out_p, 0o700)
        os.chmod(out_p, 0o700)
    out = out_p
    OUT_DIR = out
    RSH = bool(a.require_sorried_holes)
    # wherever the challenge pin is required - a GIVEN challenge export -
    # the comparator pin is required too, before anything runs; it is checked on the private copy of comparator.json below
    # and recorded in result.json
    # "a given challenge export" is decided ONCE, here (testing it twice let an export that
    # appeared in between take the given-export path without the comparator pin); --challenge-sha256 given also needs the
    # comparator pin (it pins the official export either way)
    given_export = os.path.isfile(os.path.join(a.challenge, "challenge.export"))
    if (given_export or a.challenge_sha256) and not a.comparator_sha256:
        return emit_err(out, "sound mode: a given challenge export needs --comparator-sha256 HEX (the sha256 of the official "
                        "comparator.json) as well as --challenge-sha256 HEX")

    def _on_signal(signum, _frame):   # no verdict: kill the running stage tree, ERROR result.json
        for p in list(_STAGES):
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except OSError:
                pass
        try:
            emit_err(out, f"interrupted by signal {signum} (no verdict; the running stage was killed)")
        finally:
            os._exit(2)
    for sg in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        if signal.getsignal(sg) is not signal.SIG_IGN:   # as bin/fastverify: keep nohup's / the shell's ignores
            signal.signal(sg, _on_signal)
    cenv = child_env(out)   # every stage: this fixed env, never the caller's
    used_tc = []            # toolchains used here: re-verified before the result is emitted
    exp_copies = []         # (path, pin) of the private exporter copies: re-hashed before the result is emitted

    def end_check():
        """Before EVERY verdict, as bin/fastverify's verify_components_end:
        the toolchains used and the exporter copies are verified again; a change during the run is no verdict -> reason"""
        for tc_s, tc_p in used_tc:
            try:
                p2, _, _ = resolve_toolchain(tc_s, comps)
                if p2 != tc_p:
                    raise RuntimeError(f"toolchain {tc_s} registration changed during the run")
            except RuntimeError as e:
                return f"toolchain changed during the run (no verdict): {e}"
        for ec, pin in exp_copies:
            try:
                if sha256_file(ec) != pin:
                    return f"exporter copy {ec} changed during the run (no verdict)"
            except OSError as e:
                return f"exporter copy {ec} unreadable at the end of the run: {e}"
        return None
    chk_script = os.path.join(FV, "check", "lowmem", "check-sound-lowmem.sh")
    if a.require_sorried_holes:   # checked before any build: the judge must implement the switch
        try:
            knows_rsh = "--require-sorried-holes)" in open(chk_script, encoding="utf-8", errors="replace").read()
        except OSError:
            knows_rsh = False
        if not knows_rsh:
            return emit_err(out, f"--require-sorried-holes: the judge {chk_script} does not implement the switch")
    stage_sec = {}

    if not os.path.isdir(a.challenge):
        return emit_err(out, f"challenge directory missing: {a.challenge}")
    orig_cfg = os.path.join(a.challenge, "comparator.json")
    if not os.path.isfile(orig_cfg):
        return emit_err(out, "missing comparator.json in challenge directory")
    cfg_path = os.path.join(out, "comparator.json")
    shutil.copyfile(os.path.realpath(orig_cfg), cfg_path)
    os.chmod(cfg_path, 0o444)
    cfg_sha = sha256_file(cfg_path)
    cfg_sf = orig_cfg + ".sha256"
    if os.path.isfile(cfg_sf):
        want_cfg = open(cfg_sf).read().split()[0].lower()
        if want_cfg != cfg_sha:
            return emit_err(out, f"comparator.json sha256 mismatch vs .sha256 ({cfg_sha} != {want_cfg})")
    if a.comparator_sha256 and cfg_sha != a.comparator_sha256.lower():
        return emit_err(out, f"comparator.json sha256 mismatch ({cfg_sha} != {a.comparator_sha256})")
    try:
        cc = json.load(open(cfg_path, encoding="utf-8"))
    except Exception as e:
        return emit_err(out, f"invalid comparator.json: {e}")
    for k in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
        if k not in cc:
            return emit_err(out, f"comparator.json missing '{k}'")
    if lean_name("sorryAx") in lean_names(cc.get("permitted_axioms")):   # as a Lean name: «sorryAx» too
        return emit_err(out, "comparator.json permits sorryAx (refused)")
    # the S1(3) gate BEFORE any build, as bin/fastverify: a config outside S1(3)
    # is no verdict even when the project then fails to build (not REJECTED with trust sound-lowmem)
    if not isinstance(cc.get("permitted_axioms"), list) or any(
            not isinstance(x, str) or lean_name(x) not in {lean_name(n) for n in S1_NAMES} for x in cc["permitted_axioms"]):
        return emit_err(out, f"comparator config {cfg_path}: permitted_axioms {cc.get('permitted_axioms')!r} outside GOAL S1(3)")
    chal_tc = None
    ctc_probe = os.path.join(a.challenge, "lean-toolchain")
    if os.path.isfile(ctc_probe):
        chal_tc = open(ctc_probe, encoding="utf-8").read().strip()
    try:
        lm_pins = resolve_lowmem_pins(a.pins, chal_tc)
    except Exception as e:
        return emit_err(out, str(e))

    # 4.36 Lake compareIt builtinTargets: `legalAxioms.contains ``Quot.sound` on the PARSED names
    builtin = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] \
        if lean_name("Quot.sound") in lean_names(cc["permitted_axioms"]) else []
    targets = builtin + list(cc["theorem_names"]) + list(cc["permitted_axioms"]) + PRIMITIVES + list(cc.get("definition_names") or [])

    cpus, cg_mb, eff_mb = detect_budget()
    budget_mb = a.mem_budget_mb if a.mem_budget_mb > 0 else (cg_mb or 0)
    plan_mb = a.mem_budget_mb if a.mem_budget_mb > 0 else eff_mb
    thr = a.threads if a.threads > 0 else cpus
    build_thr = max(1, min(thr, max(1, (plan_mb - 2048) // 2048)))

    comps = json.load(open(os.path.join(FV, "config", "components.json")))
    ws = os.path.realpath(a.packages) if a.packages else (
        os.path.realpath(a.challenge) if os.path.isdir(os.path.join(a.challenge, ".lake", "packages")) else "/nonexistent"
    )

    # Prepare challenge.export (given or officially built B0 + E0, matching lib/fastverify.py:prepare_challenge_export)
    chal_exp = os.path.join(a.challenge, "challenge.export")
    if given_export:   # the decision made above, not a second look
        # GOAL S1(1): a GIVEN challenge export must be THE official one: the caller's own pin is required,
        # exactly as bin/fastverify --preset sound (lib/fastverify.py) - its own hash (or a .sha256 file next to it) has no
        # independent provenance; without challenge.export the challenge is built and exported officially (B0 + E0)
        if not a.challenge_sha256:
            return emit_err(out, "sound mode: a given challenge export needs --challenge-sha256 HEX (the sha256 of the "
                            "official challenge export, GOAL S1(1)); without challenge.export the challenge is built and "
                            "exported officially (B0 + E0) instead")
        chal_exp = os.path.realpath(chal_exp)
        chal_sha = sha256_file(chal_exp)
        sf = chal_exp + ".sha256"
        if os.path.isfile(sf):
            want = open(sf).read().split()[0].lower()
            if want != chal_sha:
                return emit_err(out, f"challenge.export sha256 mismatch vs .sha256 ({chal_sha} != {want})")
    else:
        ctc_file = os.path.join(a.challenge, "lean-toolchain")
        if not os.path.isfile(ctc_file):
            return emit_err(out, "challenge.export missing and challenge has no lean-toolchain")
        ctc_str = open(ctc_file, encoding="utf-8").read().strip()
        try:   # registered + verified toolchain, pinned official exporter; refused otherwise
            ctc_prefix, c_off_exp, c_exp_pin = resolve_toolchain(ctc_str, comps)
            c_exp_copy = private_exporter(c_off_exp, c_exp_pin, out)   # the hashed copy is what runs
        except RuntimeError as e:
            return emit_err(out, f"cannot use the official toolchain/exporter for {ctc_str}: {e}")
        used_tc.append((ctc_str, ctc_prefix))
        exp_copies.append((c_exp_copy, c_exp_pin))
        EXPORTERS.append({"source": c_off_exp, "sha256": c_exp_pin, "used_for": "challenge"})
        tc_prep = time.time()
        cwork = os.path.join(out, "work_challenge")
        try:
            copy_clean_project(a.challenge, cwork)
        except Exception as e:
            return emit_err(out, f"challenge copy failed: {e}")
        clp_file = os.path.join(out, "challenge.lean_path")
        cbp = run_stage([
            os.path.join(FV, "build", "official-build.sh"), cwork, ws, ctc_prefix,
            "--threads", str(build_thr), "--lean-path-out", clp_file,
            "--log", os.path.join(out, "log-challenge-build")
        ], capture_output=True, text=True, env=cenv)
        if cbp.returncode != 0:
            shutil.rmtree(cwork, ignore_errors=True)
            return emit_err(out, f"clean challenge failed official build (exit {cbp.returncode})")
        mr = run_stage(["/usr/bin/python3", "-I", os.path.join(FV, "lib", "manifest.py"), cwork, ws],
                            capture_output=True, text=True, env=cenv)
        if mr.returncode != 0:
            shutil.rmtree(cwork, ignore_errors=True)
            return emit_err(out, f"challenge manifest dependencies failed: {mr.stderr.strip()}")
        cbinds = [tuple(ln.split("\t")) for ln in mr.stdout.splitlines() if ln]
        chal_exp = os.path.join(out, "challenge.export")
        erc = run_official_export_bwrap(
            ctc_prefix, c_off_exp, cwork, open(clp_file).read().strip(),
            cc["challenge_module"], targets, cbinds, chal_exp, os.path.join(out, "challenge_export.log"), exp_copy=c_exp_copy
        )
        shutil.rmtree(cwork, ignore_errors=True)
        if erc != 0 or not os.path.isfile(chal_exp):
            return emit_err(out, f"clean challenge failed official export (exit {erc})")
        os.chmod(chal_exp, 0o444)
        chal_sha = sha256_file(chal_exp)
        stage_sec["prepare_challenge"] = round(time.time() - tc_prep, 3)

    if a.challenge_sha256 and chal_sha != a.challenge_sha256.lower():
        return emit_err(out, f"challenge.export sha256 mismatch ({chal_sha} != {a.challenge_sha256})", stage_sec)

    sol_exp = os.path.join(out, "solution.export")

    if a.export_in:
        if not os.path.isfile(a.export_in):
            return emit_err(out, f"missing export {a.export_in}", stage_sec)
        tc = time.time()
        cp = run_stage(["/bin/cp", "--reflink=auto", "--", os.path.realpath(a.export_in), sol_exp], capture_output=True, text=True, env=cenv)
        if cp.returncode != 0:
            return emit_err(out, f"cannot copy export into OUT: {cp.stderr.strip()[:200]}", stage_sec)
        os.chmod(sol_exp, 0o444)
        stage_sec["copy_export"] = round(time.time() - tc, 3)
    else:
        if not os.path.isdir(a.project):
            return emit_err(out, f"project directory missing: {a.project}", stage_sec)
        ptc_file = os.path.join(a.project, "lean-toolchain")
        if not os.path.isfile(ptc_file):
            return emit_err(out, f"project {a.project} has no lean-toolchain", stage_sec)
        tc_str = open(ptc_file, encoding="utf-8").read().strip()
        ctc_file = os.path.join(a.challenge, "lean-toolchain")
        if os.path.isfile(ctc_file):
            ctc_str = open(ctc_file, encoding="utf-8").read().strip()
            if tc_str != ctc_str:
                return emit_err(out, f"project toolchain {tc_str} != challenge toolchain {ctc_str}", stage_sec)
        try:   # registered + verified toolchain; its pinned official exporter, as a private
            # copy, is THE fallback of the project export (export-lowmem.sh's own fallback reads export/components-lowmem.json,
            # which has no 4.36 / addrelease entries: it ended every honest 4.36 project in ERROR)
            tc_prefix, p_off_exp, p_exp_pin = resolve_toolchain(tc_str, comps)
            p_exp_copy = private_exporter(p_off_exp, p_exp_pin, out)
        except RuntimeError as e:
            return emit_err(out, f"cannot use the toolchain {tc_str}: {e}", stage_sec)
        used_tc.append((tc_str, tc_prefix))
        exp_copies.append((p_exp_copy, p_exp_pin))
        EXPORTERS.append({"source": p_off_exp, "sha256": p_exp_pin, "used_for": "project (E0 fallback)"})

        wproj = os.path.join(out, "work_proj")
        try:
            copy_clean_project(a.project, wproj)
        except Exception as e:
            return emit_err(out, f"project copy failed: {e}", stage_sec)

        mr = run_stage(["/usr/bin/python3", "-I", os.path.join(FV, "lib", "manifest.py"), wproj, ws],
                            capture_output=True, text=True, env=cenv)
        if mr.returncode != 0:
            shutil.rmtree(wproj, ignore_errors=True)
            return emit_err(out, f"project dependencies cannot be resolved: {mr.stderr.strip()}", stage_sec)
        binds_tsv = os.path.join(out, "binds.tsv")
        open(binds_tsv, "w").write(mr.stdout)

        lp_file = os.path.join(out, "lean_path.txt")
        tb = time.time()
        # Use B1 (parallel exact build with official binaries, zero 65 GB zygote) first, falling back to B0 official-build.sh
        brc = 2
        bp = run_stage([
            os.path.join(FV, "build", "build.sh"), wproj, ws, tc_prefix,
            "--threads", str(build_thr),
            "--lean-path-out", lp_file, "--log", os.path.join(out, "log-build")
        ], capture_output=True, text=True, env=cenv)
        brc = bp.returncode
        if brc not in (0, 1):
            shutil.rmtree(wproj, ignore_errors=True)
            copy_clean_project(a.project, wproj)
            bp = run_stage([
                os.path.join(FV, "build", "official-build.sh"), wproj, ws, tc_prefix,
                "--threads", str(build_thr), "--lean-path-out", lp_file,
                "--log", os.path.join(out, "log-build-official"),
                "--json", os.path.join(out, "build_official.json")
            ], capture_output=True, text=True, env=cenv)
            brc = bp.returncode
        stage_sec["build"] = round(time.time() - tb, 3)
        if brc != 0:
            shutil.rmtree(wproj, ignore_errors=True)
            v = "REJECTED" if brc == 1 else "ERROR"
            ex = 1 if brc == 1 else 2
            if ex == 1:   # no REJECTED before the end-of-run re-verification
                why_end = end_check()
                if why_end:
                    return emit_err(out, why_end, stage_sec)
            res = {"verdict": v, "exit": ex, "trust": "sound-lowmem" if ex == 1 else "none",
                   "reason": f"build exited {brc}", "stage_seconds": stage_sec,
                   "challenge_sha256": chal_sha, "comparator_sha256": cfg_sha,
                   "require_sorried_holes": RSH}
            write_result(out, res)
            return ex

        tf = os.path.join(out, "targets.txt")
        open(tf, "w").write("\n".join(targets) + "\n")
        lp = open(lp_file).read().strip()
        te = time.time()
        exp_thr = max(1, min(thr, 32))
        ep = run_stage([
            os.path.join(FV, "export", "export-lowmem.sh"),
            "--lean-path", lp, "--module", cc["solution_module"],
            "--targets-nl", tf, "--toolchain", tc_prefix, "--project", wproj,
            "--binds", binds_tsv, "--out", sol_exp, "--threads", str(exp_thr),
            "--json", os.path.join(out, "export.json")
        ], capture_output=True, text=True, env=cenv)
        erc, ewhy = ep.returncode, f"export-lowmem exited {ep.returncode}"
        if erc == 2:   # the low-memory native exporter declined: the VERIFIED official exporter (E0) exports instead
            try:
                os.unlink(sol_exp)
            except OSError:
                pass
            pbinds = [tuple(ln.split("\t")) for ln in open(binds_tsv).read().splitlines() if ln]
            erc = run_official_export_bwrap(tc_prefix, p_off_exp, wproj, lp, cc["solution_module"], targets, pbinds, sol_exp,
                                            os.path.join(out, "export_official.log"), exp_copy=p_exp_copy)
            ewhy = f"official export (E0, verified exporter copy) exited {erc}"
        stage_sec["export"] = round(time.time() - te, 3)
        shutil.rmtree(wproj, ignore_errors=True)
        if erc != 0 or not os.path.isfile(sol_exp):   # a failed export is no verdict: ERROR, never
            # REJECTED (otherwise the E0 fallback's exit 1 would become REJECTED, trust sound-lowmem, for valid proofs)
            return emit_err(out, ewhy, stage_sec)
        os.chmod(sol_exp, 0o444)

    # Cross-version & S1(3) comparator axiom gate before running low-memory judge
    raw_ax = cc.get("permitted_axioms")
    if not isinstance(raw_ax, list):
        return emit_err(out, f"comparator config {cfg_path}: missing list permitted_axioms", stage_sec)
    # compared as LEAN names, as bin/fastverify and the judges: `«propext»` IS propext (the official
    # comparator and the judge accept it, so refusing it as outside S1 would be wrong). The set is never widened: only a
    # string whose canonical name is propext, Quot.sound or Classical.choice passes; a non-string, a non-name, `propext.x`
    # and `«Quot.sound»` (one component) stay outside
    s1 = {lean_name(n) for n in S1_NAMES}
    bad_ax = [x for x in raw_ax if not isinstance(x, str) or lean_name(x) not in s1]
    if bad_ax:
        return emit_err(out, f"comparator config {cfg_path}: permitted_axioms {bad_ax} outside GOAL S1(3)", stage_sec)
    xv_py = os.path.join(FV, "check", "xversion", "xvcheck.py")
    if not os.path.isfile(xv_py):
        return emit_err(out, "check/xversion/xvcheck.py missing", stage_sec)
    xv_json = os.path.join(out, "xversion.json")
    txv = time.time()
    xvp = run_stage(["/usr/bin/python3", "-I", xv_py, os.path.realpath(chal_exp), os.path.realpath(cfg_path),
                          "--json", xv_json], capture_output=True, text=True, env=cenv)
    stage_sec["xversion"] = round(time.time() - txv, 3)
    if xvp.returncode != 0:
        try:
            xvj = json.load(open(xv_json, encoding="utf-8")) if os.path.isfile(xv_json) else {}
        except (OSError, ValueError):
            xvj = {}
        xvr = str(xvj.get("reason") or f"cross-version gate exit {xvp.returncode}")
        if xvp.returncode == 1 and xvj.get("verdict") == "REJECTED":
            why_end = end_check()
            if why_end:
                return emit_err(out, why_end, stage_sec)
            res = {"verdict": "REJECTED", "exit": 1, "trust": "sound", "reason": xvr,
                   "challenge_sha256": chal_sha, "comparator_sha256": cfg_sha,
                   "wall_s": round(time.time() - t0, 3), "stage_seconds": stage_sec, "xversion": xvj,
                   "require_sorried_holes": RSH}
            write_result(out, res)
            return 1
        return emit_err(out, f"cross-version gate: {xvr}", stage_sec)

    # Trusted sequential low-memory sound check
    tchk = time.time()
    chk_json = os.path.join(out, "check.json")
    chk_cmd = [
        chk_script, sol_exp, os.path.realpath(chal_exp), os.path.realpath(cfg_path),
        "--threads", str(thr), "--workdir", out, "--private-inputs",
        "--json", chk_json, "--log", os.path.join(out, "check.log")
    ]
    try:
        if "--challenge-sha256)" in open(chk_script, encoding="utf-8", errors="replace").read():
            chk_cmd += ["--challenge-sha256", chal_sha, "--comparator-sha256", cfg_sha]
    except OSError:
        pass
    if budget_mb > 0:
        chk_cmd += ["--mem-budget-mb", str(budget_mb)]
    if a.integrity_cache:   # never the caller's directory (as bin/fastverify)
        icd = integrity_cache_dir()
        if icd:
            chk_cmd += ["--integrity-cache", icd]
    if lm_pins:
        chk_cmd += ["--pins", lm_pins]
    if a.timeout > 0:
        chk_cmd += ["--timeout", str(a.timeout)]
    if a.require_sorried_holes:   # the judge's support is checked at the start
        chk_cmd.append("--require-sorried-holes")
    cp = run_stage(chk_cmd, capture_output=True, text=True, env=cenv)
    stage_sec["check"] = round(time.time() - tchk, 3)

    cj = None
    if os.path.isfile(chk_json):
        try:
            cj = json.load(open(chk_json))
        except Exception:
            pass
    if cj is None:
        cj = parse_last_json(cp.stdout) or {}

    rc = cp.returncode
    verdict = cj.get("verdict", "DECLINED")
    # as bin/fastverify's verify_components_end: the toolchains used and the exporter copies are
    # verified again before any result; a change during the run is no verdict
    tend = time.time()
    why_end = end_check()
    if why_end:
        return emit_err(out, why_end, stage_sec)
    stage_sec["verify_components_end"] = round(time.time() - tend, 3)
    if rc == 0 and verdict == "ACCEPTED":
        out_rc, out_v, trust = 0, "ACCEPTED", "sound"
    elif rc == 1 and verdict == "REJECTED":
        out_rc, out_v, trust = 1, "REJECTED", "none"
    else:
        out_rc, out_v, trust = 2, "DECLINED", "none"

    res = {
        "verdict": out_v,
        "exit": out_rc,
        "trust": trust,
        "reason": cj.get("reason", f"check rc={rc}"),
        "challenge_sha256": chal_sha,
        "comparator_sha256": cfg_sha,
        "wall_s": round(time.time() - t0, 3),
        "stage_seconds": stage_sec,
        "budget": {"detected_cpus": cpus, "cgroup_mem_mb": cg_mb, "applied_mem_budget_mb": budget_mb},
        "require_sorried_holes": bool(a.require_sorried_holes),
        "check": cj,
    }
    write_result(out, res)
    return out_rc


if __name__ == "__main__":
    try:   # nothing escapes as exit 1 (= REJECTED): only main()'s own 0 / 1 / 2
        _rc = main()
    except SystemExit:   # argparse: --help / a usage error is no verdict (0 = ACCEPTED here)
        _rc = 2
    except BaseException:  # noqa: BLE001
        _rc = 2
    for _st in (sys.stdout, sys.stderr):   # a failing final flush (file-size limit, closed pipe) cannot change
        try:                               # the exit status (Python would exit 120)
            _st.flush()
        except BaseException:  # noqa: BLE001
            pass
    os._exit(_rc)

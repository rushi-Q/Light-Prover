#!/usr/bin/python3 -I
"""fvcheckd.py — Persistent Multi-Query Warm Sound Check Supervisor.

Supervises three sandboxed (bwrap --unshare-all, no network, private anonymous stdin/stdout pipes)
warm legs preloaded with a pinned official challenge export C and a from-scratch kernel-verified
base export B:
  1. ccmp-warm         (official Lean 4.36 compareAt on challenge-slice + exact incremental checkAxioms)
  2. pleanchecker-warm (official Lean 4.36 kernel PChk.replayPar on immutable verified baseEnv / clean envD)
  3. gruszka-warm      (independent Rust second kernel, veto-only, CoW fork() per query)

Soundness invariants (docs/concepts/soundness.md):
  - Challenge export C is verified against --challenge-sha256 at startup and copied to mode-0700 private dir W.
  - Base export B is copied to W and VERIFIED FROM SCRATCH by BOTH pleanchecker-warm and gruszka-warm before ready.
  - Pins + official Lean 4.36 toolchain tree are fully verified at startup and stamp-checked on every query
    (identical to the check-sound-svc.sh stamp invariant).
  - Startup self-test verifies good -> ACCEPTED and bad -> REJECTED through all 3 legs before listening.
  - Per query: delta & config are copied into a fresh private mode-0700 dir W/q-<nonce>, stamped before & after,
    dispatched concurrently over anonymous pipes (zero FIFO injection surface), and judged by structured
    JSON responses (no log scraping, so export content cannot inject verdict lines).
  - ACCEPTED iff ALL THREE legs return status=="ok" for this exact nonce, ccmp-warm and pleanchecker-warm report
    identical (delta_consts, overridden, dirty, eff), gruszka-warm reports identical delta_consts, input stamps
    and pin stamps are unchanged.
  - Conditional mode (--conditional-mode, aligned with the zero-new-TCB axiom-rewrite +
    frontier-challenge C' construction): NEVER returns ACCEPTED (exit 0); returns CONDITIONAL (exit 3)
    with trust="sound-conditional" when the pinned frontier challenge C' and all 3 warm legs accept S'.
  - Any fallback response from any leg returns status="FALLBACK_REQUIRED" (or invokes cold check-sound.sh if
    full_fallback is provided), NEVER ACCEPTED on the delta path.

Usage:
  fvcheckd.py serve --state DIR --challenge C --challenge-sha256 HEX --base B [--base-layer1 L1]
                    [--threads N] [--bins-dir DIR] [--tc36 DIR] [--pkgroot DIR] [--allow-no-selftest]
  fvcheckd.py check-delta --state DIR --delta FILE --config FILE [--full-fallback FILE] [--frontier [ALLOW_FILE]]
  fvcheckd.py check-full  --state DIR --export FILE --config FILE
  fvcheckd.py stats|stop  --state DIR
"""
import argparse, concurrent.futures as cf, hashlib, json, os, secrets, shutil, signal, socket, socketserver
import stat, subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.realpath(__file__))
_CAND_PKGROOT = os.path.realpath(os.path.join(HERE, "..", ".."))
DEFAULT_PKGROOT = _CAND_PKGROOT   # the package this file belongs to (check/warm/ -> fastverify/)


def sha256_file(p: str) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def file_stamp(p: str):
    st = os.lstat(p)
    if not stat.S_ISREG(st.st_mode):
        raise ValueError(f"not a regular file: {p}")
    return (st.st_dev, st.st_ino, st.st_mode, st.st_size, st.st_mtime_ns, st.st_ctime_ns, st.st_nlink)


def dir_tree_stamp(root: str) -> str:
    """Fast stat-only metadata stamp over a toolchain tree (matches check-sound-svc.sh)."""
    h = hashlib.sha256()
    for dp, dns, fns in os.walk(root):
        dns.sort()
        fns.sort()
        for nm in fns:
            p = os.path.join(dp, nm)
            st = os.lstat(p)
            h.update(f"{p}|{st.st_dev}|{st.st_ino}|{st.st_mode}|{st.st_size}|{st.st_mtime_ns}|{st.st_ctime_ns}|{st.st_nlink}\n".encode())
    return h.hexdigest()


def resolve_pins_path(raw_pins) -> str:
    """Resolve & confine --pins to regular non-symlink pins*.env inside check/warm/ (B4 boundary)."""
    allowed_dir = os.path.realpath(HERE)
    if not raw_pins:
        p = os.path.join(allowed_dir, "pins.env")
        if not os.path.isfile(p) or os.path.islink(p):
            raise RuntimeError(f"missing or symlinked default pins.env: {p}")
        return p
    if os.path.islink(raw_pins):
        raise RuntimeError(f"pins path must not be a symlink: {raw_pins}")
    p = os.path.realpath(raw_pins)
    bn = os.path.basename(p)
    if os.path.dirname(p) != allowed_dir or not (bn.startswith("pins") and bn.endswith(".env")):
        raise RuntimeError(f"--pins must be a pins*.env inside {allowed_dir}: got {raw_pins}")
    if not os.path.isfile(p):
        raise RuntimeError(f"missing pins file: {p}")
    return p


def load_pins_env(pins_path: str):
    """Parse pinned trusted binary SHA-256 digests, default paths, and toolchain metadata from pins*.env."""
    if not os.path.isfile(pins_path):
        raise RuntimeError(f"missing pins file: {pins_path}")
    pins = {}
    paths = {}
    meta = {
        "TC_VERSION": "leanprover/lean4:v4.36.0",
        "TC_LABEL": "4.36",
        "CHECK_SOUND_PINS": "",
    }
    with open(pins_path, "r", encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            parts = s.split()
            if len(parts) >= 3 and parts[0] == "PIN":
                if parts[1] in pins:
                    raise RuntimeError(f"duplicate PIN for {parts[1]} in {pins_path}")
                pins[parts[1]] = parts[2].lower()
                if len(parts) >= 4:
                    paths[parts[1]] = parts[3]
            elif "=" in s and not s.startswith("UNTRUSTED "):
                k, v = s.split("=", 1)
                k = k.strip()
                if k in meta:
                    meta[k] = v.strip()
    for req_key in ("ccmp_warm", "pleanchecker_warm", "gruszka_warm"):
        h = pins.get(req_key, "")
        if len(h) != 64 or any(c not in "0123456789abcdef" for c in h):
            raise RuntimeError(f"invalid or missing PIN for {req_key} in {pins_path}")
    return pins, paths, meta


def resolve_toolchain_dir(pkgroot: str, tc_version: str, tc_override) -> str:
    """Resolve official toolchain directory from --tc36/--tc override, config/components.json, or ~/.elan."""
    if tc_override:
        return os.path.realpath(tc_override)
    comp_p = os.path.join(pkgroot, "config", "components.json")
    if os.path.isfile(comp_p):
        try:
            comp = json.load(open(comp_p, "r", encoding="utf-8"))
            ent = (comp.get("lean_toolchains") or {}).get(tc_version)
            if isinstance(ent, dict) and ent.get("prefix") and os.path.isdir(ent["prefix"]):
                return os.path.realpath(ent["prefix"])
        except Exception:
            pass
    elan_name = tc_version.replace("/", "--").replace(":", "---")
    return os.path.realpath(os.path.expanduser(os.path.join("~/.elan/toolchains", elan_name)))


def copy_regular_file_safe(src: str, dst: str, max_bytes: int = 0) -> None:
    """Copy a regular file without following the final symlink or blocking on a FIFO."""
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    fd = os.open(src, flags)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise ValueError(f"not a regular file: {src}")
        if max_bytes and st.st_size > max_bytes:
            raise ValueError(f"file too large ({st.st_size} > {max_bytes}): {src}")
        # Clear O_NONBLOCK after verifying S_ISREG
        total = 0
        with os.fdopen(fd, "rb", closefd=False) as rf, open(dst, "wb") as wf:
            while True:
                buf = rf.read(1 << 20)
                if not buf:
                    break
                total += len(buf)
                if max_bytes and total > max_bytes:
                    raise ValueError(f"file grew past {max_bytes} during read: {src}")
                wf.write(buf)
    finally:
        os.close(fd)


def load_strict_json_config(src: str) -> dict:
    def no_dups(pairs):
        ks = [k for k, _ in pairs]
        if len(ks) != len(set(ks)):
            raise ValueError("duplicate key in config")
        return dict(pairs)
    def bad_const(x):
        raise ValueError(f"non-standard JSON constant {x}")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    fd = os.open(src, flags)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise ValueError(f"config is not a regular file: {src}")
        if st.st_size > 16 * 1024 * 1024:
            raise ValueError(f"config too large: {st.st_size}")
        with os.fdopen(fd, "rb", closefd=False) as rf:
            raw = rf.read(16 * 1024 * 1024 + 1).decode("utf-8", errors="strict")
    finally:
        os.close(fd)
    obj = json.loads(raw, object_pairs_hook=no_dups, parse_constant=bad_const)
    if not isinstance(obj, dict):
        raise ValueError("config is not a JSON object")
    if obj.get("enable_nanoda") is True and isinstance(obj.get("external_kernels"), dict) and obj["external_kernels"]:
        raise ValueError("enable_nanoda together with external_kernels")
    return obj


def _is_letter_like(c):
    v = ord(c)
    return (
        (0x3B1 <= v <= 0x3C9 and v != 0x3BB)
        or (0x391 <= v <= 0x3A9 and v != 0x3A0 and v != 0x3A3)
        or (0x3CA <= v <= 0x3FB)
        or (0x1F00 <= v <= 0x1FFE)
        or (0x2100 <= v <= 0x214F)
        or (0x1D49C <= v <= 0x1D59F)
        or (0x00C0 <= v <= 0x00FF and v != 0x00D7 and v != 0x00F7)
        or (0x0100 <= v <= 0x017F)
    )

def _is_subscript_alnum(c):
    v = ord(c)
    return (0x2080 <= v <= 0x2089) or (0x2090 <= v <= 0x209C) or (0x1D62 <= v <= 0x1D6A) or v == 0x2C7C

def _is_id_first(c):
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or c == "_" or _is_letter_like(c)

def _is_id_rest(c):
    return (
        ("a" <= c <= "z")
        or ("A" <= c <= "Z")
        or ("0" <= c <= "9")
        or c in ("_", "'", "!", "?")
        or _is_letter_like(c)
        or _is_subscript_alnum(c)
    )

def parse_lean_name(s):
    """Exact mirror of Lean 4 `String.toName` (`Init/Meta/Defs.lean:splitNameLitAux` + `Substring.Raw.toName`).
    Returns a canonical component tuple: `()` for `Name.anonymous`, `(("s", str) | ("n", int), ...)` otherwise."""
    n = len(s)
    if n == 0:
        return ()
    i = 0
    comps = []
    while True:
        if i >= n:
            return ()
        c = s[i]
        if c == "«":
            j = s.find("»", i + 1)
            if j < 0:
                return ()
            comps.append(("s", s[i + 1 : j]))
            i = j + 1
        elif _is_id_first(c):
            j = i + 1
            while j < n and _is_id_rest(s[j]):
                j += 1
            comps.append(("s", s[i:j]))
            i = j
        elif "0" <= c <= "9":
            j = i + 1
            while j < n and ("0" <= s[j] <= "9"):
                j += 1
            comps.append(("n", int(s[i:j])))
            i = j
        else:
            return ()
        if i == n:
            return tuple(comps)
        if s[i] == ".":
            i += 1
        else:
            return ()


def q02_config_check(c, axs):
    """The judge-side config checks (see check/sound/check-sound.sh's config step)."""
    def q02_canon(x):
        t = parse_lean_name(x) if isinstance(x, str) else ()
        if not t:
            raise ValueError("config: name %r is not a Lean name" % (x,))
        return t
    Q02_S1 = set(q02_canon(n) for n in ("propext", "Quot.sound", "Classical.choice"))
    Q02_PRIMS = set(q02_canon(n) for n in ("Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq",
        "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List",
        "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam", "Quot",
        "Quot.mk", "Quot.lift", "Quot.ind",   # the comparator's primitiveTargets + builtinTargets
        "Nat.zero", "Nat.succ", "List.cons", "List.nil", "Bool", "Bool.true", "Bool.false", "Eq", "Eq.refl", "dontcare",
        "Lean.reduceBool", "Lean.reduceNat"))   # + kernel-implicit names (their closure: xversion/xvcheck.py)
    q02_ax = list(axs)
    if not isinstance(q02_ax, list) or not all(isinstance(x, str) for x in q02_ax):
        raise ValueError("permitted_axioms is not a list of names")
    q02_allow = []
    q02_extra = sorted(set(x for x in q02_ax if q02_canon(x) not in Q02_S1))
    if set(q02_canon(x) for x in q02_extra) != set(q02_canon(x) for x in q02_allow):
        if q02_extra:
            raise ValueError("permitted_axioms %s outside GOAL S1(3) (propext, Quot.sound, Classical.choice)%s" % (
                q02_extra, "" if not q02_allow else "; --extra-axioms lists %s" % sorted(q02_allow)))
        raise ValueError("--extra-axioms lists %s but the config permits no axiom outside GOAL S1(3)" % sorted(q02_allow))
    q02_dn = c.get("definition_names")
    q02_dn = [] if q02_dn is None else q02_dn
    q02_tn = c.get("theorem_names")
    q02_tn = [] if q02_tn is None else q02_tn
    if not isinstance(q02_dn, list) or not all(isinstance(x, str) for x in q02_dn):
        raise ValueError("definition_names is not a list of names")
    if not isinstance(q02_tn, list) or not all(isinstance(x, str) for x in q02_tn):
        raise ValueError("theorem_names is not a list of names")
    q02_bad = sorted(x for x in q02_dn if q02_canon(x) in (Q02_PRIMS | set(map(q02_canon, q02_tn)) | set(map(q02_canon, q02_ax))))
    if q02_bad:
        raise ValueError("definition_names %s overlap the kernel primitives / quotient builtins / theorem_names / permitted_axioms" % q02_bad)


def validate_comparator_config(obj: dict, forbid_sorry: bool = True) -> dict:
    """Validate comparator config structure and normalize lists (fail closed on malformed/sorryAx)."""
    if not isinstance(obj, dict):
        raise ValueError("config is not a JSON object")
    thms = obj.get("theorem_names")
    axs = obj.get("permitted_axioms")
    defs = obj.get("definition_names")
    if not isinstance(thms, list) or not isinstance(axs, list):
        raise ValueError("config missing list theorem_names or permitted_axioms")
    if defs is None:
        defs = []
    if not isinstance(defs, list):
        raise ValueError("config definition_names must be a list or null")
    for field, lst in (("theorem_names", thms), ("definition_names", defs), ("permitted_axioms", axs)):
        if not all(isinstance(x, str) and x and "\n" not in x and "\r" not in x for x in lst):
            raise ValueError(f"config {field} contains invalid name")
    if forbid_sorry and "sorryAx" in axs:
        raise ValueError("comparator config must not permit sorryAx in sound mode")
    # (S1(3)) an ACCEPTED / CONDITIONAL verdict is about propext, Quot.sound, Classical.choice only (the
    # conditional mode adds sorryAx / the frontier F itself, never through the user's config); definition holes may not be
    # kernel primitives / quotient builtins / targets / axioms. Canonical Lean names (String.toName).
    if forbid_sorry:
        q02_config_check(obj, axs)
    out = dict(obj)
    out["theorem_names"] = list(thms)
    out["definition_names"] = list(defs)
    out["permitted_axioms"] = list(axs)
    return out


def load_and_validate_frontier(frontier_path: str, official_cfg: dict) -> list:
    """Load & validate open-lemma frontier list F (matches check/frontier/check-frontier.sh:243-253)."""
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    fd = os.open(frontier_path, flags)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise ValueError(f"frontier file is not a regular file: {frontier_path}")
        if st.st_size > 1024 * 1024:
            raise ValueError(f"frontier file too large: {st.st_size}")
        with os.fdopen(fd, "rb", closefd=False) as rf:
            raw = rf.read(1024 * 1024 + 1).decode("utf-8", errors="strict")
    finally:
        os.close(fd)
    s = raw.strip()
    if s.startswith("["):
        F = json.loads(s)
        if not isinstance(F, list):
            raise ValueError("frontier JSON must be a list of strings")
    else:
        F = [ln.strip() for ln in raw.splitlines() if ln.strip() and not ln.strip().startswith("#")]
    if not F:
        raise ValueError("frontier list F must be non-empty in --conditional-mode")
    if not all(isinstance(x, str) and x and "\n" not in x and "\r" not in x for x in F):
        raise ValueError("frontier list contains malformed name")
    if len(set(F)) != len(F):
        raise ValueError("frontier list contains duplicate names")
    T = set(official_cfg["theorem_names"])
    D = set(official_cfg.get("definition_names") or [])
    A = set(official_cfg["permitted_axioms"])
    bad = sorted(set(F) & (T | D | A | {"sorryAx"}))
    if bad:
        raise ValueError(f"frontier contains forbidden target/def/axiom/sorryAx: {bad}")
    trust = sorted(
        n for n in F
        if n in ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")
        or "._native.native_decide.ax_" in n
        or n.startswith("_native.native_decide.ax_")
    )
    if trust:
        raise ValueError(f"frontier contains compiler/native_decide trust axiom: {trust}")
    # the same checks on CANONICAL names (guillemet spellings are the same Name)
    q02_F = [parse_lean_name(n) for n in F]
    if not all(q02_F):
        raise ValueError("frontier list contains a name that is not a Lean name")
    if len(set(q02_F)) != len(q02_F):
        raise ValueError("frontier list contains duplicate names (canonical)")
    q02_forb = set(parse_lean_name(n) for n in list(T) + list(D) + list(A) +
                   ["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"])
    q02_badF = sorted(n for n, tt in zip(F, q02_F) if tt in q02_forb or any(
        tt[i] == ("s", "_native") and tt[i + 1] == ("s", "native_decide") and tt[i + 2][0] == "s"
        and tt[i + 2][1].startswith("ax_") for i in range(len(tt) - 2)))
    if q02_badF:
        raise ValueError(f"frontier contains forbidden target/def/axiom/sorryAx/trust axiom (canonical): {q02_badF}")
    return sorted(F)


class SandboxedLeg:
    """One persistent warm leg inside bwrap --unshare-all, communicating over private anonymous pipes.
    Auto-respawns cleanly on a keeper thread if a prior query crashes, panics, times out, or desyncs
    the leg (an availability measure; it does not affect soundness)."""
    def __init__(self, name: str, bin_path: str, args: list, tc36: str, work_dir: str,
                 queries_dir: str, threads: int, stack_kb: int = 917376, extra_env: dict = None):
        self.name = name
        self.bin_path = os.path.realpath(bin_path)
        self.lock = threading.Lock()
        self.ready_info = None
        self.broken = False
        self._stopping = False
        self.proc = None
        self.bwrap_cmd = [
            "/usr/bin/env", "-i",
            "/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session",
            "--ro-bind", "/", "/",
            "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run", "--tmpfs", "/tmp",
            "--dev", "/dev", "--proc", "/proc",
            "--ro-bind", tc36, tc36,
            "--ro-bind", work_dir, work_dir,
            "--ro-bind", queries_dir, queries_dir,
            "--ro-bind", self.bin_path, self.bin_path,
            "--chdir", work_dir,
            "--setenv", "HOME", "/tmp",
            "--setenv", "TMPDIR", "/tmp",
            "--setenv", "LANG", "C.UTF-8",
            "--setenv", "LEAN_ABORT_ON_PANIC", "1",
            "--setenv", "LEAN_NUM_THREADS", str(threads),
            "--setenv", "LEAN_STACK_SIZE_KB", str(stack_kb),
            "--setenv", "PATH", f"{tc36}/bin:/usr/bin:/bin",
            *[x for k, v in (extra_env or {}).items() for x in ("--setenv", str(k), str(v))],
            "--", self.bin_path, *args,
        ]
        self._spawn()

    def _spawn(self):
        """Spawn bwrap on a dedicated keeper thread so PR_SET_PDEATHSIG (--die-with-parent) stays
        bound to a live thread for the leg's lifetime (even across respawns)."""
        started = threading.Event()
        holder = [None, None]
        def _keeper():
            try:
                p = subprocess.Popen(
                    self.bwrap_cmd,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    bufsize=1,
                )
                holder[0] = p
            except Exception as e:
                holder[1] = e
                started.set()
                return
            started.set()
            try:
                p.wait()
            except Exception:
                pass
        kt = threading.Thread(target=_keeper, daemon=True, name=f"leg-{self.name}")
        kt.start()
        started.wait()
        if holder[1] is not None:
            raise holder[1]
        self.proc = holder[0]
        self.broken = False

    def _kill_broken(self):
        self.broken = True
        p = self.proc
        if p is not None:
            try:
                if p.poll() is None:
                    p.kill()
                p.wait(timeout=2)
            except Exception:
                pass

    def _ensure_alive(self):
        if self._stopping:
            raise RuntimeError(f"leg {self.name} stopping")
        if self.broken or self.proc is None or self.proc.poll() is not None:
            self._kill_broken()
            self._spawn()
            self.wait_ready()

    def wait_ready(self):
        line = self.proc.stdout.readline()
        if not line:
            err = self.proc.stderr.read() if self.proc.stderr else ""
            rc = self.proc.poll()
            self._kill_broken()
            raise RuntimeError(f"leg {self.name} exited during startup (rc={rc}): {err.strip()[:500]}")
        try:
            info = json.loads(line)
        except Exception as e:
            self._kill_broken()
            raise RuntimeError(f"leg {self.name} emitted non-JSON startup line: {line!r} ({e})")
        if not info.get("ready"):
            self._kill_broken()
            raise RuntimeError(f"leg {self.name} failed base verification: {info}")
        self.ready_info = info
        self.broken = False
        return info

    def query(self, cmd_line: str, timeout_s: float = 300.0, expected_nonce: str = None) -> dict:
        with self.lock:
            try:
                self._ensure_alive()
            except Exception as e:
                return {"leg": self.name, "status": "decline", "msg": f"leg {self.name} respawn failed: {e}"}
            try:
                self.proc.stdin.write(cmd_line + "\n")
                self.proc.stdin.flush()
            except OSError as e:
                self._kill_broken()
                return {"leg": self.name, "status": "error", "msg": f"write to {self.name} failed: {e}"}
            # Wait for 1-line JSON response with timeout
            res_holder = [None]
            p_cur = self.proc
            def _read():
                try:
                    res_holder[0] = p_cur.stdout.readline()
                except Exception:
                    res_holder[0] = ""
            t = threading.Thread(target=_read, daemon=True)
            t.start()
            t.join(timeout_s)
            if t.is_alive():
                self._kill_broken()
                return {"leg": self.name, "status": "decline", "msg": f"leg {self.name} timed out after {timeout_s}s"}
            line = res_holder[0]
            if not line:
                rc = self.proc.poll()
                self._kill_broken()
                return {"leg": self.name, "status": "decline", "msg": f"leg {self.name} closed pipe (rc={rc})"}
            try:
                obj = json.loads(line)
            except Exception as e:
                self._kill_broken()
                return {"leg": self.name, "status": "error", "msg": f"leg {self.name} non-JSON response: {line!r} ({e})"}
            if expected_nonce is not None and obj.get("nonce") != expected_nonce:
                self._kill_broken()
                return {"leg": self.name, "status": "decline", "msg": f"leg {self.name} nonce mismatch (desync)"}
            return obj

    def stop(self):
        with self.lock:
            self._stopping = True
            if self.proc is not None and self.proc.poll() is None:
                try:
                    self.proc.stdin.write("QUIT\n")
                    self.proc.stdin.flush()
                    self.proc.wait(timeout=3)
                except Exception:
                    self.proc.kill()
                    self.proc.wait()


class WarmCheckDaemon:
    def __init__(self, args):
        self.args = args
        self.state_dir = os.path.realpath(args.state)
        os.makedirs(self.state_dir, mode=0o700, exist_ok=True)
        os.chmod(self.state_dir, 0o700)
        self.work_dir = os.path.join(self.state_dir, "priv")
        self.queries_dir = os.path.join(self.state_dir, "queries")
        shutil.rmtree(self.work_dir, ignore_errors=True)
        shutil.rmtree(self.queries_dir, ignore_errors=True)
        os.makedirs(self.work_dir, mode=0o755, exist_ok=True)
        os.makedirs(self.queries_dir, mode=0o755, exist_ok=True)

        self.pkgroot = os.path.realpath(args.pkgroot)
        # 1. Resolve & load confined pins*.env (default: check/warm/pins.env, Lean 4.36)
        self.pins_path = resolve_pins_path(getattr(args, "pins", None))
        self.pins_sha = sha256_file(self.pins_path)
        self.pins_stamp = file_stamp(self.pins_path)
        pins, pin_paths, pin_meta = load_pins_env(self.pins_path)
        self.tc_version = pin_meta["TC_VERSION"]
        self.tc_label = pin_meta["TC_LABEL"]
        self.check_sound_pins = pin_meta["CHECK_SOUND_PINS"]

        self.tc36 = resolve_toolchain_dir(self.pkgroot, self.tc_version, getattr(args, "tc36", None))
        bins_dir_arg = getattr(args, "bins_dir", None)
        def _pick_bin(pin_key: str, fallback_name: str) -> str:
            if bins_dir_arg:
                bd = os.path.realpath(bins_dir_arg)
                pinned_bn = os.path.basename(pin_paths.get(pin_key, "")) if pin_paths.get(pin_key) else ""
                if pinned_bn and os.path.isfile(os.path.join(bd, pinned_bn)):
                    return os.path.join(bd, pinned_bn)
                return os.path.join(bd, fallback_name)
            return pin_paths.get(pin_key) or os.path.join("/scratch/fastverify-next/warm/v1", fallback_name)

        self.ccmp_bin = _pick_bin("ccmp_warm", "ccmp-warm")
        self.plc_bin = _pick_bin("pleanchecker_warm", "pleanchecker-warm")
        self.gz_bin = _pick_bin("gruszka_warm", "gruszka-warm")

        # 2. Verify official Lean toolchain tree once + record stat stamp (fail closed!)
        t0 = time.time()
        tc_script = os.path.join(self.pkgroot, "lib", "toolchain.py")
        if not os.path.isfile(tc_script):
            raise RuntimeError(f"missing official toolchain verifier: {tc_script}")
        r = subprocess.run(["/usr/bin/python3", "-I", tc_script, "verify", self.tc36, self.tc_version],
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            raise RuntimeError(f"official {self.tc_label} toolchain verify failed: {r.stderr.strip()}")
        self.tc36_stamp = dir_tree_stamp(self.tc36)
        self.tc36_lib = os.path.join(self.tc36, "lib", "lean", "libleanshared.so")
        self.tc36_lib_stamp = file_stamp(self.tc36_lib)

        # 3. Enforce pins*.env SHA-256 digests + stat stamps on all 3 trusted binaries (fail closed!)
        self.bin_sha = {}
        self.bin_stamps = {}
        for name, pin_key, bp in [
            ("ccmp-warm", "ccmp_warm", self.ccmp_bin),
            ("pleanchecker-warm", "pleanchecker_warm", self.plc_bin),
            ("gruszka-warm", "gruszka_warm", self.gz_bin),
        ]:
            if not os.path.isfile(bp):
                raise RuntimeError(f"missing warm binary: {bp}")
            got_sha = sha256_file(bp)
            if got_sha != pins[pin_key]:
                raise RuntimeError(f"pinned binary {name} sha256 mismatch: got {got_sha}, expected {pins[pin_key]} ({bp})")
            self.bin_sha[name] = got_sha
            self.bin_stamps[name] = file_stamp(bp)

        # 3. Copy & verify pinned challenge export, comparator config, and base export into private work_dir (0400)
        chal_src = os.path.realpath(args.challenge)
        chal_got = sha256_file(chal_src)
        if chal_got != args.challenge_sha256:
            raise RuntimeError(f"challenge sha256 mismatch: got {chal_got}, pinned {args.challenge_sha256}")
        self.chal_path = os.path.join(self.work_dir, "challenge.export")
        copy_regular_file_safe(chal_src, self.chal_path)
        os.chmod(self.chal_path, 0o400)
        if sha256_file(self.chal_path) != args.challenge_sha256:
            raise RuntimeError("challenge changed during copy")
        self.chal_sha = args.challenge_sha256
        self.chal_stamp = file_stamp(self.chal_path)

        cfg_src = os.path.realpath(args.config)
        if getattr(args, "config_sha256", None):
            cfg_got = sha256_file(cfg_src)
            if cfg_got != args.config_sha256:
                raise RuntimeError(f"config sha256 mismatch: got {cfg_got}, pinned {args.config_sha256}")
        official_cfg = validate_comparator_config(load_strict_json_config(cfg_src), forbid_sorry=True)

        self.hide_src = ""
        self.hide_path = None
        self.hide_sha = ""
        self.hide_stamp = None
        if getattr(args, "hide", None):
            h_in = args.hide
            try:
                hst = os.stat(h_in)  # follows symlinks like stat -L
            except OSError as e:
                raise RuntimeError(f"--hide: cannot stat '{h_in}': {e}")
            if not stat.S_ISREG(hst.st_mode) or hst.st_size > 16777216:
                raise RuntimeError(f"--hide: not a regular file <= 16 MiB: '{h_in}'")
            h_real = os.path.realpath(h_in)
            self.hide_src = h_in
            self.hide_path = os.path.join(self.work_dir, "hide")
            copy_regular_file_safe(h_real, self.hide_path)
            os.chmod(self.hide_path, 0o400)
            self.hide_sha = sha256_file(self.hide_path)
            self.hide_stamp = file_stamp(self.hide_path)

        self.conditional_mode = bool(getattr(args, "conditional_mode", False))
        self.allow_theorem_subset = bool(getattr(args, "allow_theorem_subset", False))
        self.official_chal_path = None
        self.official_chal_sha = None
        self.official_chal_stamp = None
        self.frontier = []

        if self.conditional_mode:
            if self.allow_theorem_subset:
                raise RuntimeError("--allow-theorem-subset is forbidden with --conditional-mode")
            if not getattr(args, "official_challenge", None) or not getattr(args, "official_challenge_sha256", None):
                raise RuntimeError("--conditional-mode requires --official-challenge and --official-challenge-sha256")
            if not getattr(args, "frontier", None):
                raise RuntimeError("--conditional-mode requires --frontier FILE")
            off_src = os.path.realpath(args.official_challenge)
            if sha256_file(off_src) != args.official_challenge_sha256:
                raise RuntimeError("official challenge sha256 mismatch")
            self.official_chal_path = os.path.join(self.work_dir, "official_challenge.export")
            copy_regular_file_safe(off_src, self.official_chal_path)
            os.chmod(self.official_chal_path, 0o400)
            if sha256_file(self.official_chal_path) != args.official_challenge_sha256:
                raise RuntimeError("official challenge changed during copy")
            self.official_chal_sha = args.official_challenge_sha256
            self.official_chal_stamp = file_stamp(self.official_chal_path)

            self.frontier = load_and_validate_frontier(os.path.realpath(args.frontier), official_cfg)
            # Build Check A config from official config (+ sorryAx iff present in official C) and run unchanged check-sound.sh!
            csorry = b'"pre":0,"str":"sorryAx"}' in open(self.official_chal_path, "rb").read()
            cfgA = dict(official_cfg)
            cfgA["permitted_axioms"] = list(official_cfg["permitted_axioms"]) + (["sorryAx"] if csorry else [])
            cfgA_path = os.path.join(self.work_dir, "checkA_comparator.json")
            with open(cfgA_path, "w", encoding="utf-8") as f:
                json.dump(cfgA, f, ensure_ascii=False)
            os.chmod(cfgA_path, 0o400)
            check_sound_sh = os.path.join(self.pkgroot, "check", "sound", "check-sound.sh")
            if not os.path.isfile(check_sound_sh):
                raise RuntimeError(f"missing check-sound.sh for conditional Check A: {check_sound_sh}")
            checkA_json = os.path.join(self.work_dir, "checkA_result.json")
            ca_cmd = [
                check_sound_sh, self.chal_path, self.official_chal_path, cfgA_path,
                "--threads", str(args.threads), "--private-inputs", "--json", checkA_json,
                "--workdir", self.work_dir,
            ]
            if self.check_sound_pins:
                cs_bn = self.check_sound_pins
                if "/" in cs_bn or ".." in cs_bn or not (cs_bn.startswith("pins") and cs_bn.endswith(".env")):
                    raise RuntimeError(f"invalid CHECK_SOUND_PINS in {self.pins_path}: {cs_bn}")
                cs_pins_p = os.path.join(self.pkgroot, "check", "sound", cs_bn)
                if os.path.islink(cs_pins_p) or not os.path.isfile(cs_pins_p):
                    raise RuntimeError(f"missing or symlinked check-sound pins: {cs_pins_p}")
                ca_cmd += ["--pins", cs_pins_p]
            if self.hide_path and "--hide" in open(check_sound_sh, "r", encoding="utf-8", errors="replace").read():
                ca_cmd += ["--hide", self.hide_path]
            # Check A legitimately permits sorryAx beyond GOAL S1(3); a sound check that holds configs to S1(3)
            # needs it listed with --extra-axioms (exactly the extras of cfgA)
            if csorry and "--extra-axioms)" in open(check_sound_sh, "r", encoding="utf-8", errors="replace").read():
                xa_path = os.path.join(self.work_dir, "checkA_extra_axioms.txt")
                with open(xa_path, "w", encoding="utf-8") as f:
                    f.write("sorryAx\n")
                os.chmod(xa_path, 0o400)
                ca_cmd += ["--extra-axioms", xa_path]
            ca_proc = subprocess.run(ca_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            ca_verdict = None
            if os.path.isfile(checkA_json):
                try:
                    ca_verdict = json.load(open(checkA_json, encoding="utf-8")).get("verdict")
                except Exception:
                    ca_verdict = None
            if ca_proc.returncode != 0 or ca_verdict != "ACCEPTED":
                raise RuntimeError(
                    f"conditional Check A (C' vs official C) failed (rc={ca_proc.returncode}, verdict={ca_verdict}): "
                    f"{(ca_proc.stdout + ca_proc.stderr)[-400:]}"
                )
            pinned_cfg = dict(official_cfg)
            pinned_cfg["permitted_axioms"] = list(official_cfg["permitted_axioms"]) + list(self.frontier)
        else:
            pinned_cfg = official_cfg

        self.pinned_cfg = pinned_cfg
        self.cfg_path = os.path.join(self.work_dir, "comparator.json")
        with open(self.cfg_path, "w", encoding="utf-8") as f:
            json.dump(self.pinned_cfg, f, ensure_ascii=False)
        os.chmod(self.cfg_path, 0o400)
        self.cfg_sha = sha256_file(self.cfg_path)
        # the cross-version gate on the PRIVATE copies (official challenge C and the
        # pinned config) before the daemon serves anything: anything but rc 0 + OK refuses to start (fail closed)
        xv_chal = self.official_chal_path if getattr(self, "official_chal_path", None) else self.chal_path
        xv_py = os.path.join(self.pkgroot, "check", "xversion", "xvcheck.py")
        if not os.path.isfile(xv_py):
            raise RuntimeError("xversion gate: check/xversion/xvcheck.py missing")
        xv_json = os.path.join(self.work_dir, "xversion.json")
        xp = subprocess.run(["/usr/bin/python3", "-I", xv_py, xv_chal, self.cfg_path, "--releases",
                             os.path.join(self.pkgroot, "check", "xversion", "releases.json"), "--json", xv_json]
                            + (["--require-sorried-holes"] if getattr(args, "require_sorried_holes", False) else []),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            xvj = json.load(open(xv_json, encoding="utf-8"))
        except Exception:
            xvj = {}
        if not (xp.returncode == 0 and xvj.get("verdict") == "OK"):
            raise RuntimeError(f"xversion gate refused the challenge (rc={xp.returncode}, verdict={xvj.get('verdict')}): "
                               f"{str(xvj.get('reason', ''))[:300]}")
        self.cfg_stamp = file_stamp(self.cfg_path)

        base_src = os.path.realpath(args.base)
        self.base_path = os.path.join(self.work_dir, "base.export")
        copy_regular_file_safe(base_src, self.base_path)
        os.chmod(self.base_path, 0o400)
        self.base_sha = sha256_file(self.base_path)
        self.base_stamp = file_stamp(self.base_path)

        self.layer1_path = None
        if args.base_layer1:
            l1_src = os.path.realpath(args.base_layer1)
            self.layer1_path = os.path.join(self.work_dir, "layer1.export")
            copy_regular_file_safe(l1_src, self.layer1_path)
            os.chmod(self.layer1_path, 0o400)

        # 4. Launch all 3 sandboxed legs on MAIN THREAD (so bwrap --die-with-parent tracks main thread,
        # not an ephemeral ThreadPoolExecutor worker thread!), then await ready concurrently.
        nt = args.threads
        plc_args = ["--base", self.base_path, f"-j{nt}"]
        if self.layer1_path:
            plc_args += ["--base-layer1", self.layer1_path]
        ccmp_args = ["--challenge", self.chal_path, "--base", self.base_path, f"-j{nt}"]
        gz_args = ["--warm-base", self.base_path, str(nt)]

        self.ccmp = SandboxedLeg("ccmp", self.ccmp_bin, ccmp_args, self.tc36, self.work_dir, self.queries_dir, nt)
        plc_env = {"PCHK_HIDE_FILE": self.hide_path} if self.hide_path else None
        self.plc = SandboxedLeg("lean4", self.plc_bin, plc_args, self.tc36, self.work_dir, self.queries_dir, nt, extra_env=plc_env)
        self.gz = SandboxedLeg("gruszka", self.gz_bin, gz_args, self.tc36, self.work_dir, self.queries_dir, nt)
        with cf.ThreadPoolExecutor(max_workers=3) as ex:
            fc = ex.submit(self.ccmp.wait_ready)
            fp = ex.submit(self.plc.wait_ready)
            fg = ex.submit(self.gz.wait_ready)
            fc.result()
            fp.result()
            fg.result()
        # 5. Mandatory startup self-test: verify good -> ok AND bad -> reject on ALL THREE binaries!
        # Uses /scratch/fastverify-next/selftest when present, else synthesizes a minimal
        # self-contained NDJSON challenge/good/bad-axiom fixture in work_dir (never silently skipped).
        st_root = "/scratch/fastverify-next/selftest"
        if not getattr(args, "skip_selftest", False):
            if os.path.isdir(st_root):
                st_chal = os.path.join(st_root, "challenge.export")
                st_good = os.path.join(st_root, "good.export")
                st_bad = os.path.join(st_root, "bad.export")
                st_cfg = os.path.join(st_root, "comparator.json")
            else:
                st_chal = os.path.join(self.work_dir, "selftest_chal.export")
                st_good = os.path.join(self.work_dir, "selftest_good.export")
                st_bad = os.path.join(self.work_dir, "selftest_bad.export")
                st_cfg = os.path.join(self.work_dir, "selftest_cfg.json")
                _hdr = '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.36.0"}}}\n'
                _names = (
                    '{"in":1,"str":{"pre":0,"str":"fvST"}}\n'
                    '{"in":2,"str":{"pre":0,"str":"fvBadAx"}}\n'
                    '{"in":3,"str":{"pre":0,"str":"p"}}\n'
                    '{"ie":0,"sort":0}\n'
                    '{"ie":1,"bvar":0}\n'
                    '{"ie":2,"forallE":{"binderInfo":"default","body":1,"name":3,"type":0}}\n'
                    '{"ie":3,"forallE":{"binderInfo":"default","body":2,"name":3,"type":0}}\n'
                    '{"ie":4,"lam":{"binderInfo":"default","body":1,"name":3,"type":0}}\n'
                    '{"ie":5,"lam":{"binderInfo":"default","body":4,"name":3,"type":0}}\n'
                    '{"ie":6,"const":{"name":2,"us":[]}}\n'
                )
                with open(st_chal, "w", encoding="utf-8") as f:
                    f.write(_hdr + _names + '{"axiom":{"levelParams":[],"name":2,"type":3}}\n{"thm":{"all":[1],"levelParams":[],"name":1,"type":3,"value":6}}\n')
                with open(st_good, "w", encoding="utf-8") as f:
                    f.write(_hdr + _names + '{"thm":{"all":[1],"levelParams":[],"name":1,"type":3,"value":5}}\n')
                with open(st_bad, "w", encoding="utf-8") as f:
                    f.write(_hdr + _names + '{"axiom":{"levelParams":[],"name":2,"type":3}}\n{"thm":{"all":[1],"levelParams":[],"name":1,"type":3,"value":6}}\n')
                with open(st_cfg, "w", encoding="utf-8") as f:
                    json.dump({"theorem_names": ["fvST"], "definition_names": [], "permitted_axioms": []}, f)
            # Write tiny kernel-invalid export (`def fvSelfTestBad : Prop := Type 0`) into work_dir
            st_kbad = os.path.join(self.work_dir, "selftest_kbad.export")
            with open(st_kbad, "w", encoding="utf-8") as f:
                f.write(
                    '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.36.0"}}}\n'
                    '{"in":1,"str":{"pre":0,"str":"fvSelfTestBad"}}\n'
                    '{"ie":0,"sort":0}\n'
                    '{"il":1,"succ":0}\n'
                    '{"ie":1,"sort":1}\n'
                    '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":1}}\n'
                )
            # 5a. Kernel legs (running live instances): good -> ok, kbad -> reject
            for leg_name, leg_obj in [("lean4", self.plc), ("gruszka", self.gz)]:
                rg = leg_obj.query(f"CHECK_FULL\tstg\t{st_good}", 60.0)
                if rg.get("status") != "ok":
                    raise RuntimeError(f"startup self-test good failed on {leg_name}: {rg}")
                rb = leg_obj.query(f"CHECK_FULL\tstkb\t{st_kbad}", 60.0)
                if rb.get("status") != "reject":
                    raise RuntimeError(f"startup self-test kernel-bad NOT rejected on {leg_name}: {rb}")
            # 5b. ccmp-warm binary: one-shot sandboxed verification on selftest challenge (good -> ok, bad -> reject)
            st_ccmp = SandboxedLeg("ccmp-selftest", self.ccmp_bin,
                                   ["--challenge", st_chal, "--base", st_chal, "-j1"],
                                   self.tc36, self.work_dir, self.queries_dir, 1)
            st_ccmp.wait_ready()
            try:
                rcg = st_ccmp.query(f"CHECK_FULL\tstg\t{st_good}\t{st_cfg}", 60.0)
                if rcg.get("status") != "ok":
                    raise RuntimeError(f"startup self-test good failed on ccmp-warm: {rcg}")
                rcb = st_ccmp.query(f"CHECK_FULL\tstb\t{st_bad}\t{st_cfg}", 60.0)
                if rcb.get("status") != "reject":
                    raise RuntimeError(f"startup self-test bad-axiom NOT rejected on ccmp-warm: {rcb}")
            finally:
                st_ccmp.stop()

        self.startup_s = round(time.time() - t0, 3)
        self.stats_lock = threading.Lock()
        self.stats = {
            "started_at": time.time(),
            "startup_s": self.startup_s,
            "queries": 0,
            "accepted": 0,
            "conditional": 0,
            "rejected": 0,
            "declined": 0,
            "fallbacks": 0,
            "errors": 0,
            "pins_file": os.path.basename(self.pins_path),
            "pins_sha256": self.pins_sha,
            "tc_version": self.tc_version,
            "hide": self.hide_src,
            "hide_sha256": self.hide_sha,
            "challenge_sha256": self.chal_sha,
            "config_sha256": self.cfg_sha,
            "base_sha256": self.base_sha,
            "binaries_sha256": self.bin_sha,
            "legs_ready": {
                "ccmp": self.ccmp.ready_info,
                "lean4": self.plc.ready_info,
                "gruszka": self.gz.ready_info,
            },
        }
        self.pool = cf.ThreadPoolExecutor(max_workers=3)
        self.check_lock = threading.Lock()
        self.stop_event = threading.Event()

    def _verify_runtime_stamps(self) -> str:
        """Fast stat check on pinned binaries + private challenge/base copies."""
        for name, bp in [("ccmp-warm", self.ccmp_bin), ("pleanchecker-warm", self.plc_bin), ("gruszka-warm", self.gz_bin)]:
            if file_stamp(bp) != self.bin_stamps[name]:
                if sha256_file(bp) != self.bin_sha[name]:
                    return f"pinned binary {name} changed during service lifetime"
                self.bin_stamps[name] = file_stamp(bp)
        if file_stamp(self.pins_path) != self.pins_stamp:
            if sha256_file(self.pins_path) != self.pins_sha:
                return "pins file modified during service lifetime"
            self.pins_stamp = file_stamp(self.pins_path)
        if file_stamp(self.tc36_lib) != self.tc36_lib_stamp:
            return f"official {self.tc_label} libleanshared.so modified during service lifetime"
        if file_stamp(self.chal_path) != self.chal_stamp:
            return "private challenge copy modified"
        if file_stamp(self.cfg_path) != self.cfg_stamp:
            return "private pinned comparator config modified"
        if self.official_chal_path and file_stamp(self.official_chal_path) != self.official_chal_stamp:
            return "private official challenge copy modified"
        if file_stamp(self.base_path) != self.base_stamp:
            return "private base copy modified"
        if self.hide_path and file_stamp(self.hide_path) != self.hide_stamp:
            return "private hide copy modified"
        return ""

    def handle_check(self, req: dict) -> dict:
        t0 = time.time()
        op = req.get("op")
        try:
            req_tmo = float(req.get("timeout", 300.0))
            if not (req_tmo > 0.0):
                req_tmo = 300.0
        except Exception:
            req_tmo = 300.0
        # Clamp per-query timeout to a safe server floor (a tiny timeout would let a client cause respawn churn)
        timeout_s = max(5.0, min(3600.0, req_tmo))
        nonce = secrets.token_hex(16)
        stamp_err = self._verify_runtime_stamps()
        if stamp_err:
            return self._finish("DECLINED", 2, stamp_err, {}, t0, nonce)

        src_path = req.get("delta") if op == "check_delta" else req.get("export")
        cfg_src = req.get("config")
        if not src_path:
            return self._finish("ERROR", 2, "missing delta/export path", {}, t0, nonce)
        try:
            src_real = os.path.realpath(src_path)
            p_thms = self.pinned_cfg["theorem_names"]
            p_defs = self.pinned_cfg.get("definition_names") or []
            p_axs = self.pinned_cfg["permitted_axioms"]
            effective_cfg = self.pinned_cfg
            if cfg_src:
                cfg_real = os.path.realpath(cfg_src)
                req_obj = validate_comparator_config(load_strict_json_config(cfg_real), forbid_sorry=not self.conditional_mode)
                r_thms = req_obj["theorem_names"]
                r_defs = req_obj.get("definition_names") or []
                r_axs = req_obj["permitted_axioms"]
                if self.allow_theorem_subset:
                    if (not r_thms
                            or not set(r_thms).issubset(set(p_thms))
                            or set(r_defs) != set(p_defs)
                            or not set(r_axs).issubset(set(p_axs))):
                        return self._finish("DECLINED", 2, "query config violates startup-pinned policy", {}, t0, nonce)
                    effective_cfg = dict(self.pinned_cfg)
                    effective_cfg["theorem_names"] = r_thms
                    effective_cfg["definition_names"] = r_defs
                    effective_cfg["permitted_axioms"] = r_axs
                else:
                    if r_thms != p_thms or r_defs != p_defs or r_axs != p_axs:
                        return self._finish("DECLINED", 2, "query config differs from startup-pinned config", {}, t0, nonce)
        except Exception as e:
            return self._finish("DECLINED", 2, f"input/config refused: {e}", {}, t0, nonce)

        # Copy inputs into a fresh private immutable per-query dir (O_NOFOLLOW|O_NONBLOCK)
        qdir = os.path.join(self.queries_dir, f"q-{nonce}")
        os.makedirs(qdir, mode=0o755, exist_ok=False)
        try:
            q_exp = os.path.join(qdir, "input.export")
            q_cfg = os.path.join(qdir, "comparator.json")
            try:
                copy_regular_file_safe(src_real, q_exp)
            except Exception as e:
                return self._finish("DECLINED", 2, f"input refused: {e}", {}, t0, nonce)
            with open(q_cfg, "w", encoding="utf-8") as f:
                json.dump(effective_cfg, f, ensure_ascii=False)
            os.chmod(q_cfg, 0o400)
            st0 = file_stamp(q_exp)
            cfg_st0 = file_stamp(q_cfg)
            exp_sha = sha256_file(q_exp)
            eff_cfg_sha = sha256_file(q_cfg)
            eff_thms = list(effective_cfg["theorem_names"])

            if op == "check_delta":
                c_cmd = f"CHECK_DELTA\t{nonce}\t{q_exp}\t{q_cfg}"
                p_cmd = f"CHECK_DELTA\t{nonce}\t{q_exp}"
                g_cmd = f"CHECK_DELTA\t{nonce}\t{q_exp}"
            elif op == "check_full":
                c_cmd = f"CHECK_FULL\t{nonce}\t{q_exp}\t{q_cfg}"
                p_cmd = f"CHECK_FULL\t{nonce}\t{q_exp}"
                g_cmd = f"CHECK_FULL\t{nonce}\t{q_exp}"
            else:
                return self._finish("ERROR", 2, f"unknown op {op}", {}, t0, nonce)

            # Dispatch concurrently to all 3 warm legs
            with self.check_lock:
                fc = self.pool.submit(self.ccmp.query, c_cmd, timeout_s, nonce)
                fp = self.pool.submit(self.plc.query, p_cmd, timeout_s, nonce)
                fg = self.pool.submit(self.gz.query, g_cmd, timeout_s, nonce)
                rc_c = fc.result()
                rc_p = fp.result()
                rc_g = fg.result()

            # End-of-query stamp verification (inputs + pin integrity)
            if file_stamp(q_exp) != st0 or file_stamp(q_cfg) != cfg_st0:
                return self._finish("DECLINED", 2, "private query input modified during check", {}, t0, nonce)
            stamp_err2 = self._verify_runtime_stamps()
            if stamp_err2:
                return self._finish("DECLINED", 2, stamp_err2, {}, t0, nonce)

            legs = {"ccmp": rc_c, "lean4": rc_p, "gruszka": rc_g}
            # Nonce verification across all 3 legs
            for lname, lres in legs.items():
                if lres.get("nonce") != nonce:
                    return self._finish("DECLINED", 2, f"nonce mismatch from {lname}", legs, t0, nonce, exp_sha)

            sc, sp, sg = rc_c.get("status"), rc_p.get("status"), rc_g.get("status")

            # Fallback requested by any leg -> NEVER accept on delta path!
            if "fallback" in (sc, sp, sg):
                reasons = [f"{k}:{v.get('msg','')}" for k, v in legs.items() if v.get("status") == "fallback"]
                return self._finish("FALLBACK_REQUIRED", 2, "; ".join(reasons), legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)

            # Definite rejection logic (identical priority to check-sound.sh)
            if sc == "reject":
                return self._finish("REJECTED", 1, f"ccmp: {rc_c.get('msg', '')}", legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)
            if sp == "reject":
                return self._finish("REJECTED", 1, f"lean4: {rc_p.get('msg', '')}", legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)
            if sg == "reject":
                return self._finish("REJECTED", 1, f"gruszka: {rc_g.get('msg', '')}", legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)

            # Any decline or error -> no verdict (exit 2)
            if sp != "ok" or sg != "ok":
                return self._finish("DECLINED", 2, f"kernel leg did not accept (lean4={sp}, gruszka={sg})", legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)
            if sc != "ok":
                return self._finish("DECLINED", 2, f"ccmp did not accept (status={sc}: {rc_c.get('msg', '')})", legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)

            # Cross-leg overlay consistency check (ccmp and lean4 share WarmBase and MUST match exactly!)
            for field in ("delta_consts", "overridden", "dirty", "eff"):
                if rc_c.get(field) != rc_p.get(field):
                    return self._finish("DECLINED", 2, f"cross-leg mismatch on {field}: ccmp={rc_c.get(field)} lean4={rc_p.get(field)}", legs, t0, nonce, exp_sha)
            if rc_g.get("delta_consts") != rc_c.get("delta_consts"):
                return self._finish("DECLINED", 2, f"cross-leg delta_consts mismatch: gruszka={rc_g.get('delta_consts')} ccmp={rc_c.get('delta_consts')}", legs, t0, nonce, exp_sha)

            if self.conditional_mode:
                return self._finish("CONDITIONAL", 3, f"conditional modulo pinned frontier challenge C' (ccmp-warm + official Lean {self.tc_label} kernel + gruszka-warm accept S')", legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)
            return self._finish("ACCEPTED", 0, f"statements + axioms match pinned challenge (ccmp-warm); official Lean {self.tc_label} kernel (pleanchecker-warm) and independent kernel gruszka-warm accept", legs, t0, nonce, exp_sha, eff_cfg_sha, eff_thms)
        finally:
            shutil.rmtree(qdir, ignore_errors=True)

    def _finish(self, verdict: str, exit_code: int, reason: str, legs: dict, t0: float,
                nonce: str, exp_sha: str = "", eff_cfg_sha: str = "",
                eff_thms=None) -> dict:
        wall_ms = round((time.time() - t0) * 1000.0, 2)
        with self.stats_lock:
            self.stats["queries"] += 1
            k = {"ACCEPTED": "accepted", "CONDITIONAL": "conditional", "REJECTED": "rejected",
                 "FALLBACK_REQUIRED": "fallbacks", "DECLINED": "declined"}.get(verdict, "errors")
            self.stats[k] += 1
        out = {
            "checker": "checkSoundWarm",
            "verdict": verdict,
            "exit": exit_code,
            "wall_ms": wall_ms,
            "reason": reason,
            "nonce": nonce,
            "input_sha256": exp_sha,
            "challenge_sha256": self.chal_sha,
            "config_sha256": self.cfg_sha,
            "base_sha256": self.base_sha,
            "hide": self.hide_src,
            "hide_sha256": self.hide_sha,
            "legs": legs,
            "trust": "sound" if verdict == "ACCEPTED" else ("sound-conditional" if verdict == "CONDITIONAL" else "none"),
        }
        if self.allow_theorem_subset:
            if eff_cfg_sha:
                out["effective_config_sha256"] = eff_cfg_sha
            if eff_thms is not None:
                out["effective_theorem_names"] = eff_thms
        if self.conditional_mode:
            out["frontier"] = list(self.frontier)
            out["official_challenge_sha256"] = self.official_chal_sha
        return out

    def stop(self):
        self.stop_event.set()
        self.pool.shutdown(wait=False)
        for leg in (self.ccmp, self.plc, self.gz):
            try:
                leg.stop()
            except Exception:
                pass
        shutil.rmtree(self.work_dir, ignore_errors=True)
        shutil.rmtree(self.queries_dir, ignore_errors=True)


def run_serve(args):
    daemon = WarmCheckDaemon(args)
    sock_path = os.path.join(daemon.state_dir, "sock")
    if os.path.exists(sock_path):
        os.unlink(sock_path)

    class Handler(socketserver.StreamRequestHandler):
        def handle(self):
            raw = self.rfile.readline(1 << 20)
            if not raw:
                return
            try:
                req = json.loads(raw.decode("utf-8"))
            except Exception as e:
                resp = {"verdict": "ERROR", "exit": 2, "reason": f"bad JSON: {e}"}
            else:
                op = req.get("op")
                if op == "stats":
                    with daemon.stats_lock:
                        resp = dict(daemon.stats)
                elif op == "stop":
                    resp = {"ok": True, "stopping": True}
                    self.wfile.write((json.dumps(resp) + "\n").encode("utf-8"))
                    self.wfile.flush()
                    threading.Thread(target=lambda: (time.sleep(0.05), server.shutdown()), daemon=True).start()
                    return
                elif op in ("check_delta", "check_full"):
                    resp = daemon.handle_check(req)
                else:
                    resp = {"verdict": "ERROR", "exit": 2, "reason": f"unknown op {op}"}
            self.wfile.write((json.dumps(resp) + "\n").encode("utf-8"))
            self.wfile.flush()

    class ThreadedUnixServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
        daemon_threads = True
        request_queue_size = 1024

    server = ThreadedUnixServer(sock_path, Handler)
    os.chmod(sock_path, 0o600)

    def _sig(_s, _f):
        threading.Thread(target=server.shutdown, daemon=True).start()
    signal.signal(signal.SIGTERM, _sig)
    signal.signal(signal.SIGINT, _sig)

    info = {
        "ready": True,
        "socket": sock_path,
        "pid": os.getpid(),
        "startup_s": daemon.startup_s,
        "pins_file": os.path.basename(daemon.pins_path),
        "pins_sha256": daemon.pins_sha,
        "tc_version": daemon.tc_version,
        "hide": daemon.hide_src,
        "hide_sha256": daemon.hide_sha,
        "challenge_sha256": daemon.chal_sha,
        "config_sha256": daemon.cfg_sha,
        "base_sha256": daemon.base_sha,
        "conditional_mode": daemon.conditional_mode,
        "allow_theorem_subset": daemon.allow_theorem_subset,
        "legs": daemon.stats["legs_ready"],
    }
    with open(os.path.join(daemon.state_dir, "ready.json"), "w") as f:
        json.dump(info, f, indent=2)
    print(json.dumps(info), flush=True)
    try:
        server.serve_forever(poll_interval=0.2)
    finally:
        server.server_close()
        if os.path.exists(sock_path):
            os.unlink(sock_path)
        daemon.stop()


def send_req(state_dir: str, req: dict, timeout_s: float = 360.0) -> dict:
    sock_path = os.path.join(os.path.realpath(state_dir), "sock")
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


def main():
    ap = argparse.ArgumentParser(description="fvcheckd: persistent warm sound verification daemon (D12)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sp = sub.add_parser("serve")
    sp.add_argument("--state", required=True)
    sp.add_argument("--challenge", required=True)
    sp.add_argument("--challenge-sha256", required=True)
    sp.add_argument("--config", required=True, help="pinned comparator.json (copied 0400 at startup; queries cannot weaken permitted_axioms or targets)")
    sp.add_argument("--config-sha256", default=None, help="optional SHA-256 pin for --config")
    sp.add_argument("--base", required=True)
    sp.add_argument("--base-layer1", default=None)
    sp.add_argument("--threads", type=int, default=max(1, min(32, os.cpu_count() or 4)))
    sp.add_argument("--pins", default=None, help="confined pins*.env inside check/warm/ (default: pins.env = Lean 4.36; use check/warm/pins-437.env for Lean 4.37.0-rc1)")
    sp.add_argument("--hide", default=None, help="optional untrusted availability-only hide list (<= 16 MiB regular file) for D23-E r2 encapsulated replay in pleanchecker-warm-437 (PCHK_HIDE_FILE); default off")
    sp.add_argument("--bins-dir", default=None, help="optional override directory for warm binaries (default: paths in pins*.env)")
    sp.add_argument("--tc36", "--tc", dest="tc36", default=None, help="optional override path for official judge toolchain (default: resolved from pins*.env TC_VERSION)")
    sp.add_argument("--pkgroot", default=DEFAULT_PKGROOT)
    sp.add_argument("--allow-theorem-subset", action="store_true", help="allow per-query subsets of startup-pinned theorem_names (for fvserve problem sets; permitted_axioms & definition_names remain strictly pinned)")
    sp.add_argument("--conditional-mode", action="store_true", help="Day 1-99 frontier-challenge mode: runs Check A (C' vs official C) at startup, validates F, NEVER returns ACCEPTED (exit 0); passing checks return CONDITIONAL (exit 3)")
    sp.add_argument("--official-challenge", default=None, help="(--conditional-mode) official pinned challenge export C")
    sp.add_argument("--official-challenge-sha256", default=None, help="(--conditional-mode) SHA-256 pin of official challenge export C")
    sp.add_argument("--frontier", default=None, help="(--conditional-mode) file listing frontier open-lemma axiom names F")
    sp.add_argument("--skip-selftest", action="store_true")
    sp.add_argument("--require-sorried-holes", action="store_true", help="refuse to start if a definition hole of the challenge is not sorried (the 4.37 rule for every release)")

    cd = sub.add_parser("check-delta")
    cd.add_argument("--state", required=True)
    cd.add_argument("--delta", required=True)
    cd.add_argument("--config", default=None, help="optional (must match startup-pinned --config if provided)")
    cd.add_argument("--timeout", type=float, default=300.0)

    cf_p = sub.add_parser("check-full")
    cf_p.add_argument("--state", required=True)
    cf_p.add_argument("--export", required=True)
    cf_p.add_argument("--config", default=None, help="optional (must match startup-pinned --config if provided)")
    cf_p.add_argument("--timeout", type=float, default=300.0)

    st = sub.add_parser("stats")
    st.add_argument("--state", required=True)

    stp = sub.add_parser("stop")
    stp.add_argument("--state", required=True)

    args = ap.parse_args()
    if args.cmd == "serve":
        run_serve(args)
    elif args.cmd == "check-delta":
        req = {"op": "check_delta", "delta": os.path.realpath(args.delta), "timeout": args.timeout}
        if args.config:
            req["config"] = os.path.realpath(args.config)
        resp = send_req(args.state, req, args.timeout + 30.0)
        print(json.dumps(resp))
        sys.exit(int(resp.get("exit", 2)))
    elif args.cmd == "check-full":
        req = {"op": "check_full", "export": os.path.realpath(args.export), "timeout": args.timeout}
        if args.config:
            req["config"] = os.path.realpath(args.config)
        resp = send_req(args.state, req, args.timeout + 30.0)
        print(json.dumps(resp))
        sys.exit(int(resp.get("exit", 2)))
    elif args.cmd == "stats":
        print(json.dumps(send_req(args.state, {"op": "stats"})))
    elif args.cmd == "stop":
        print(json.dumps(send_req(args.state, {"op": "stop"})))


if __name__ == "__main__":
    main()

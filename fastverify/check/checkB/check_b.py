#!/usr/bin/python3 -I
"""Fast check B: statement/axiom comparison (kcompare) + independent kernels, fail closed.

  check-b.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--timeout SEC]
             [--dual | --single | --mode dual|single] [--unsafe ignore-order] [--workdir DIR] [--bin DIR]
  (menu: option C3 = --dual (default, gruszka AND nano-lean), option C4 = --single (gruszka only, UNSAFE opt-in);
   --unsafe ignore-order = do not count prechk's replay-order classes, UNSAFE opt-in, recorded in the result)
  check-b.sh --preflight [--bin DIR]

What it runs (all concurrently, each in its own fresh empty working directory under `env -i`, binaries pinned by sha256):
  * kcompare  -- the comparison half of Lean 4.36 `lake comparator` (compareAt + checkAxioms) on the two exports,
                 theorem names / definition names / permitted axioms taken from the PROJECT's comparator.json
                 (definition_names = 4.36 definition "holes": type, level params and safety must match the challenge's,
                 the value is the solution's own and is checked by the kernels and by checkAxioms);
  * gruszka   -- independent Lean 4 kernel (fork 4ad120b + fixes 053/055/058/068), checks EVERY declaration;
  * nl-fast   -- second independent kernel (nano-lean 10b28d2 + fixes 060/065), mode dual only (default);
  * nanoda_bin (the OFFICIAL binary bundled with Lean 4.36, invoked as `lake comparator` invokes it) -- only when the
                 comparator.json names nanoda (enable_nanoda or external_kernels {"<..noda..>": ["nanoda_bin"]});
  * the official-limits pre-check (check/prechk/prechk.sh) -- decline where the OFFICIAL comparator itself fails
                 for its own reasons (replay order, walk depth, parser panics, ...).
Verdict (exit status, plus one JSON object on stdout and in --json FILE):
  0 ACCEPTED  -- every leg ran and accepted, the pre-check is clean, the config is fully supported;
  1 REJECTED  -- some leg definitely rejected (kcompare / nanoda: the official comparator rejects too; a kernel reject is
                 a fast-checker verdict only -- the official comparator stays the reference);
  2 DECLINED  -- anything else: unsupported config (an external kernel other than nanoda, names kcompare cannot take), a binary
                 that is missing / has the wrong sha256 / cannot start, a decline, crash, timeout or signal of any leg,
                 a pre-check hazard or a missing pre-check, an input that changed while checking.
Nothing verdict-relevant is read from the environment or the working directory.
"""
import hashlib
import json
import os
import signal
import stat
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.realpath(__file__))
ROOT = os.path.realpath(os.path.join(HERE, "..", ".."))
PINS = os.path.join(HERE, "components.json")
PKG_COMPONENTS = os.path.join(ROOT, "config", "components.json")
PRECHK = os.path.join(ROOT, "check", "prechk", "prechk.sh")
SAFE_PATH = "/usr/bin:/bin"
BWRAP = "/usr/bin/bwrap"


def die_usage():
    sys.stderr.write(__doc__.split("\n\n")[1] + "\n")
    sys.exit(2)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 20)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def load_pins(bin_dir):
    """Pinned binaries: {name: (path, sha256)}; bin_dir overrides the directory, never the hashes."""
    with open(PINS) as f:
        pins = json.load(f)
    d = bin_dir or pins["bin_dir"]
    out = {name: (os.path.join(d, name), digest) for name, digest in pins["sha256"].items()}
    # the official nanoda binary: pinned by the package's component list (Lean 4.36 release)
    with open(PKG_COMPONENTS) as f:
        comp = json.load(f)["comparator"]
    out["nanoda_bin"] = (os.path.join(comp["prefix"], "bin", "nanoda_bin"), comp["sha256"]["bin/nanoda_bin"])
    return out


def preflight(bins, need):
    """[] if every needed binary exists, matches its sha256 and starts on this host; else a list of reasons."""
    bad = []
    for name in need:
        path, digest = bins[name]
        try:
            have = sha256(path)
        except OSError as e:
            bad.append(f"{name}: cannot read {path}: {e.strerror}")
            continue
        if have != digest:
            bad.append(f"{name}: {path} sha256 {have} != pinned {digest}")
            continue
        # must START (no missing glibc symbols / illegal instructions / loader errors): run with no input
        try:
            r = subprocess.run([path] if name != "kcompare" else [path, "--parse-only", "/dev/null"],
                               stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               env={"PATH": SAFE_PATH, "LANG": "C.UTF-8"}, cwd="/", timeout=60)
            out = r.stdout.decode("utf-8", "replace")
            if r.returncode < 0 or r.returncode in (126, 127) or "GLIBC" in out or "error while loading" in out:
                bad.append(f"{name}: {path} does not start on this host (exit {r.returncode}): {out.strip()[:200]}")
        except (OSError, subprocess.TimeoutExpired) as e:
            bad.append(f"{name}: {path} does not start: {e}")
    if not os.path.isfile(PRECHK):
        bad.append(f"prechk: {PRECHK} missing (the official-limits pre-check is mandatory for an ACCEPT)")
    return bad


def regular_file(path):
    st = os.stat(path)  # follows symlinks: the target must be a regular file (no pipe / device / directory)
    if not stat.S_ISREG(st.st_mode):
        raise ValueError(f"not a regular file: {path}")
    return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns)


class Unsupported(Exception):
    pass


# Lean 4.36 identifier characters (Init/Meta/Defs.lean isLetterLike / isSubScriptAlnum / isIdFirst / isIdRest; Char.isAlpha
# and Char.isAlphanum are ASCII-only)
def _letter_like(o):
    return ((0x3b1 <= o <= 0x3c9 and o != 0x3bb) or (0x391 <= o <= 0x3a9 and o not in (0x3a0, 0x3a3))
            or 0x3ca <= o <= 0x3fb or 0x1f00 <= o <= 0x1ffe or 0x2100 <= o <= 0x214f or 0x1d49c <= o <= 0x1d59f
            or (0xc0 <= o <= 0xff and o not in (0xd7, 0xf7)) or 0x100 <= o <= 0x17f)


def _subscript_alnum(o):
    return 0x2080 <= o <= 0x2089 or 0x2090 <= o <= 0x209c or 0x1d62 <= o <= 0x1d6a or o == 0x2c7c


def _id_first(c):
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or c == "_" or _letter_like(ord(c))


def _id_rest(c):
    return _id_first(c) or ("0" <= c <= "9") or c in "'!?" or _subscript_alnum(ord(c))


def plain_lean_name(n):
    """True iff Lean 4.36 String.toName(n) is exactly the naive split of n at '.' into STRING components (what kcompare
    looks up): every component is a plain identifier (isIdFirst isIdRest*). Anything else - «» escapes, numeric components,
    empty components, other characters (String.toName gives `.anonymous` for e.g. "my-thm" or "a b") - is not taken."""
    parts = n.split(".")
    return bool(n) and all(p and _id_first(p[0]) and all(_id_rest(c) for c in p[1:]) for p in parts)


def parse_config(path):
    """Mirror Lake.Check.Config (Lean 4.36 lake/Lake/CLI/Check.lean) and refuse what check B cannot reproduce."""
    with open(path, "rb") as f:
        raw = f.read()
    # stricter than Python's json module where Lean.Json.parse is stricter: NaN / Infinity are not JSON (Lean refuses
    # them -> the official comparator cannot run), and a duplicate key is ambiguous -> DECLINED, never a verdict
    def no_constants(c):
        raise ValueError(f"non-JSON constant {c}")

    def no_duplicates(pairs):
        keys = [k for k, _ in pairs]
        if len(keys) != len(set(keys)):
            raise ValueError("duplicate key in a JSON object")
        return dict(pairs)
    try:
        cfg = json.loads(raw.decode("utf-8"), parse_constant=no_constants, object_pairs_hook=no_duplicates)
    except (UnicodeDecodeError, ValueError) as e:
        raise Unsupported(f"comparator.json is not valid JSON: {e}")
    if not isinstance(cfg, dict):
        raise Unsupported("comparator.json is not a JSON object")

    def strs(key, required):
        if key not in cfg or cfg[key] is None:
            if required:
                raise Unsupported(f"comparator.json lacks {key}")
            return []
        v = cfg[key]
        if not isinstance(v, list) or not all(isinstance(x, str) for x in v):
            raise Unsupported(f"comparator.json: {key} must be an array of strings")
        return v

    for key in ("challenge_module", "solution_module"):
        if not isinstance(cfg.get(key), str):
            raise Unsupported(f"comparator.json: {key} must be a string")
    theorems = strs("theorem_names", True)
    axioms = strs("permitted_axioms", True)
    defs = strs("definition_names", False)
    if not theorems and not defs:
        raise Unsupported("nothing to check: no theorem_names / definition_names (the official comparator cannot run either)")
    for n in theorems + defs + axioms:
        # Lake reads each name with String.toName; kcompare splits at '.' (names travel comma-separated): only names on
        # which both agree are taken (no commas, escapes, numeric components or non-identifier characters, found in the regression runs:
        # "my-thm" is `.anonymous` for Lean -> the official comparator rejects, a naive split would find «my-thm»)
        if not plain_lean_name(n):
            raise Unsupported(f"name {n!r} cannot be passed to kcompare exactly (not a plain dotted Lean identifier)")
    nanoda = cfg.get("enable_nanoda")
    kernels = cfg.get("external_kernels")
    if nanoda is not None and not isinstance(nanoda, bool):
        raise Unsupported("enable_nanoda must be a boolean")
    if kernels is not None and not isinstance(kernels, dict):
        raise Unsupported("external_kernels must be an object")
    kernels = kernels or {}
    if nanoda and kernels:
        raise Unsupported("enable_nanoda together with external_kernels (the official comparator refuses to run)")
    use_nanoda = bool(nanoda)
    for name, cmd in kernels.items():
        if not isinstance(cmd, list) or not cmd or not all(isinstance(x, str) for x in cmd):
            raise Unsupported(f"external kernel {name!r}: command must be a non-empty array of strings")
        if "noda" in name and cmd == ["nanoda_bin"]:
            use_nanoda = True
        else:
            raise Unsupported(f"external kernel {name!r} {cmd} cannot be reproduced by check B")
    return theorems, defs, axioms, use_nanoda


def main(argv):
    if not argv:
        die_usage()
    opts = {"--threads": "16", "--json": None, "--timeout": "0", "--mode": "dual", "--workdir": None, "--bin": None,
            "--unsafe": ""}
    pos = []
    i = 0
    flags = set()
    while i < len(argv):
        a = argv[i]
        if a == "--preflight":
            flags.add(a)
            i += 1
        elif a in ("--single", "--dual"):   # menu options C4 / C3 (= --mode single / --mode dual)
            opts["--mode"] = a[2:]
            i += 1
        elif a in opts:
            if i + 1 >= len(argv):
                die_usage()
            opts[a] = argv[i + 1]
            i += 2
        elif a.startswith("--"):
            sys.stderr.write(f"checkB: unknown option {a}\n")
            sys.exit(2)
        else:
            pos.append(a)
            i += 1
    try:
        bins = load_pins(opts["--bin"])
    except (OSError, ValueError, KeyError) as e:
        sys.stderr.write(f"checkB: cannot read the pinned component list: {e}\n")
        sys.exit(2)
    if "--preflight" in flags:
        bad = preflight(bins, ["kcompare", "gruszka", "nl-fast", "nanoda_bin"])
        for b in bad:
            sys.stderr.write(f"checkB: preflight: {b}\n")
        sys.exit(0 if not bad else 2)
    if len(pos) != 3:
        die_usage()
    t0 = time.time()
    result = {"checker": "checkB", "tool": "kcompare + gruszka [+ nl-fast] [+ official nanoda] + prechk (fast, unofficial)",
              "verdict": "DECLINED", "exit": 2, "detail": "", "seconds": 0.0, "legs": {}}

    def emit(verdict, code, detail):
        result.update(verdict=verdict, exit=code, detail=detail, seconds=round(time.time() - t0, 3))
        line = json.dumps(result, sort_keys=True)
        print(line, flush=True)
        if opts["--json"]:
            with open(opts["--json"], "w") as f:
                f.write(line + "\n")
        sys.exit(code)

    try:
        threads = int(opts["--threads"])
        timeout = float(opts["--timeout"])
        if threads < 1 or threads > 4096 or timeout < 0:
            raise ValueError
    except ValueError:
        emit("DECLINED", 2, "bad --threads / --timeout")
    mode = opts["--mode"]
    if mode not in ("dual", "single"):
        emit("DECLINED", 2, "--mode must be dual or single")
    # OPT-IN UNSAFE options (menu preset 'fastest'): recorded in the result, never on by default
    #   ignore-order: do not count prechk's replay-ORDER classes (finding 012: the official replay may reject string-literal
    #                 / Nat-literal / Quot declarations that check B's kernels accept) -> check B may ACCEPT what the
    #                 official comparator REJECTS on such exports (by definition: a completeness bug of the official replay)
    unsafe = [u for u in opts["--unsafe"].split(",") if u]
    bad_unsafe = [u for u in unsafe if u not in ("ignore-order",)]
    if bad_unsafe:
        emit("DECLINED", 2, f"unknown --unsafe option(s) {bad_unsafe} (known: ignore-order)")
    result["unsafe"] = unsafe
    result["trust"] = "UNSAFE (opt-in: " + ",".join(unsafe) + ")" if unsafe else \
        "unofficial independent kernels; can only veto in the package's default fast policy"
    export, challenge, config = (os.path.realpath(p) for p in pos)
    try:
        ids = [regular_file(p) for p in (export, challenge, config)]
    except (OSError, ValueError) as e:
        emit("DECLINED", 2, f"input: {e}")
    try:
        theorems, defs, axioms, use_nanoda = parse_config(config)
    except (OSError, Unsupported) as e:
        emit("DECLINED", 2, f"config: {e}")
    result["config"] = {"theorem_names": theorems, "definition_names": defs, "permitted_axioms": axioms,
                        "nanoda": use_nanoda, "mode": mode}
    need = ["kcompare", "gruszka"] + (["nl-fast"] if mode == "dual" else []) + (["nanoda_bin"] if use_nanoda else [])
    bad = preflight(bins, need)
    have_prechk = os.path.isfile(PRECHK)
    if [b for b in bad if not b.startswith("prechk:")]:
        emit("DECLINED", 2, "preflight: " + "; ".join(bad))

    if opts["--workdir"]:
        wd = os.path.realpath(opts["--workdir"])
        os.makedirs(wd, exist_ok=True)
        clean = False
    else:
        wd = tempfile.mkdtemp(prefix="fv-checkB.", dir=os.environ.get("TMPDIR") or "/tmp")
        clean = True
    th = str(threads)
    legs = {}
    # one empty private directory per leg: nl-fast reads ./nano-lean.toml (finding 049), Rust tools read nothing else;
    # HOME/TMPDIR point into it, PATH is fixed, nothing else is inherited (finding 016)
    empty_cfg = os.path.join(wd, "nl-empty.toml")
    with open(empty_cfg, "w"):
        pass
    legs["kcompare"] = [bins["kcompare"][0], "-j", th, "--challenge", challenge,
                        "--theorems", ",".join(theorems), "--axioms", ",".join(axioms)] \
        + (["--definitions", ",".join(defs)] if defs else []) + [export]
    legs["gruszka"] = [bins["gruszka"][0], export, th]
    if mode == "dual":
        # explicit empty config (049), no cache, budgets as ceilings large enough for heavy valid proofs (064)
        legs["nl-fast"] = [bins["nl-fast"][0], "--config", empty_cfg, "--no-cache", "-q", "-j", th,
                           "--steps", "100000000000", "--arena-mib", "65536", export]
    if use_nanoda:
        # exactly the config Lean 4.36 Lake writes for an external nanoda kernel (Check.lean runExternalKernel),
        # except num_threads: nanoda (tc.rs check_all_declars_par) hands declarations one by one to num_threads workers,
        # each with the same STACK_SIZE stack, and fails if any fails -> the verdict does not depend on the worker count
        # as long as it is >= 2 (num_threads <= 1 would check serially on the MAIN thread, whose stack differs; the
        # official value is 4)
        ncfg = os.path.join(wd, "nanoda.json")
        with open(ncfg, "w") as f:
            f.write(json.dumps({"use_stdin": False, "export_file_path": export, "permitted_axioms": axioms,
                                "unpermitted_axiom_hard_error": False, "num_threads": max(2, threads),
                                "nat_extension": True, "string_extension": True}, separators=(",", ":")))
        legs["nanoda"] = [bins["nanoda_bin"][0], ncfg]
    if have_prechk:
        # nanoda_* hazards are not counted (--no-nanoda): when the config names nanoda, check B runs the OFFICIAL nanoda
        # binary itself, which reproduces every nanoda limit exactly; without nanoda they do not affect the official verdict
        # --mode checkB: every limit class AND the replay-ORDER classes count (gruszka / nano-lean do not replay in
        # Lean.Replay's order, so where the official replay may fail on order (finding 012) check B must decline)
        legs["prechk"] = ["/bin/bash", PRECHK, "--mode", "checkB", "--nanoda", "no", "--threads", th,
                          "--json", os.path.join(wd, "prechk", "report.json")]
        if "ignore-order" in unsafe:
            legs["prechk"] += ["--ignore", "order_quot,order_strlit,order_natlit"]
        legs["prechk"].append(export)
    procs = {}
    readable = sorted({export, challenge, config, ROOT, os.path.dirname(PKG_COMPONENTS)}
                      | {os.path.dirname(b[0]) for b in bins.values()})
    for name, cmd in legs.items():
        d = os.path.join(wd, name)
        os.makedirs(d, exist_ok=True)
        env = {"PATH": SAFE_PATH, "HOME": d, "TMPDIR": d, "LANG": "C.UTF-8"}
        if name == "nanoda":
            env["LEAN_ABORT_ON_PANIC"] = "1"  # as the official comparator passes it
        # each leg in its own bwrap sandbox, like the official comparator runs its kernels: / read-only, home
        # directories and /tmp hidden, no network, only its own directory writable, environment cleared
        box = [BWRAP, "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp",
               "--dev", "/dev", "--proc", "/proc"]
        if os.path.isdir("/run/user"):
            box += ["--tmpfs", "/run/user"]
        for r in readable:
            box += ["--ro-bind", r, r]
        for extra in (empty_cfg, os.path.join(wd, "nanoda.json")):
            if os.path.exists(extra):
                box += ["--ro-bind", extra, extra]
        box += ["--bind", d, d, "--unshare-all", "--die-with-parent", "--new-session", "--clearenv"]
        for k, v in env.items():
            box += ["--setenv", k, v]
        box += ["--chdir", d, "--"]
        log = open(os.path.join(wd, name + ".log"), "wb")
        try:
            procs[name] = (subprocess.Popen(box + cmd, cwd=d, env=env, stdin=subprocess.DEVNULL, stdout=log,
                                            stderr=subprocess.STDOUT, start_new_session=True), log, time.time())
        except OSError as e:
            for p, _, _ in procs.values():
                os.killpg(p.pid, signal.SIGKILL)
            emit("DECLINED", 2, f"{name}: cannot start: {e}")
    deadline = t0 + timeout if timeout > 0 else None
    codes = {}
    timed_out = False
    stopped = set()
    while len(codes) < len(procs):
        for name, (p, log, ts) in procs.items():
            if name in codes:
                continue
            rc = p.poll()
            if rc is not None:
                codes[name] = rc
                log.close()
                result["legs"][name] = {"exit": rc, "seconds": round(time.time() - ts, 3)}
        # once an ACCEPT is impossible (the pre-check found a hazard or could not run) the official nanoda leg is stopped:
        # its only remaining use would be a veto that the official comparator itself reports, and on RH-sized exports
        # its serial parse alone takes ~20 min. The independent legs (kcompare, gruszka, nl-fast) keep running: their
        # rejects stay a veto. A leg stopped this way is reported as "stopped" and never counts as a reject.
        if "prechk" in codes and codes["prechk"] != 0 and "nanoda" in procs and "nanoda" not in codes \
                and "nanoda" not in stopped:
            stopped.add("nanoda")
            try:
                os.killpg(procs["nanoda"][0].pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if deadline and time.time() > deadline and len(codes) < len(procs):
            timed_out = True
            for name, (p, log, ts) in procs.items():
                if name not in codes:
                    try:
                        os.killpg(p.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
        time.sleep(0.05)

    def tail(name, n=400):
        try:
            with open(os.path.join(wd, name + ".log"), "rb") as f:
                f.seek(0, 2)
                size = f.tell()
                f.seek(max(0, size - 4096))
                lines = [l for l in f.read().decode("utf-8", "replace").splitlines() if l.strip()]
            return " | ".join(lines[-3:])[-n:]
        except OSError:
            return ""

    for name in result["legs"]:
        result["legs"][name]["tail"] = tail(name)
        if name in stopped:
            result["legs"][name]["stopped"] = "pre-check hazard: an ACCEPT was impossible, the official nanoda leg was stopped"
    try:  # the pre-check's counted hazard classes (informative; the verdict uses its exit status only)
        with open(os.path.join(wd, "prechk", "report.json")) as f:
            rep = json.load(f)
        result["prechk"] = {k: v.get("count") for k, v in (rep.get("hazards") or {}).items()
                            if isinstance(v, dict) and v.get("counted")}
    except (OSError, ValueError, AttributeError):
        pass
    try:
        changed = [regular_file(p) for p in (export, challenge, config)] != ids
    except (OSError, ValueError):
        changed = True
    # the pinned binaries must still be the pinned ones at the end (closes the window between the preflight hash and the
    # exec of each leg; a swap during the run -> no verdict)
    for name in need:
        try:
            if sha256(bins[name][0]) != bins[name][1]:
                changed = True
        except OSError:
            changed = True
    if clean:
        subprocess.run(["rm", "-rf", wd])
    else:
        result["workdir"] = wd
    if timed_out:
        emit("DECLINED", 2, f"timeout after {timeout:g} s")
    if changed:
        emit("DECLINED", 2, "an input file or a pinned binary changed while checking")
    kernels = [n for n in ("gruszka", "nl-fast") if n in codes]
    # definite rejections: kcompare 1 (comparison/axiom failure as the official compare step reports it), the official
    # nanoda binary failing (the official comparator then rejects too: any nonzero exit except "cannot execute"),
    # or a kernel's explicit reject (exit 1)
    rejects = []
    if codes.get("kcompare") == 1:
        rejects.append("kcompare: " + result["legs"]["kcompare"]["tail"])
    if "nanoda" in codes and "nanoda" not in stopped and codes["nanoda"] not in (0, 126, 127, -signal.SIGKILL, 128 + signal.SIGKILL):
        rejects.append(f"official nanoda exit {codes['nanoda']}: " + result["legs"]["nanoda"]["tail"])
    for n in kernels:
        if codes[n] == 1:
            rejects.append(f"{n}: " + result["legs"][n]["tail"])
    if rejects:
        emit("REJECTED", 1, " ; ".join(rejects))
    others = [n for n in codes if n != "prechk" and n not in stopped and codes[n] != 0]
    if others:
        emit("DECLINED", 2, " ; ".join(f"{n} exit {codes[n]}: {result['legs'][n]['tail']}" for n in others))
    if not have_prechk:
        emit("DECLINED", 2, "every leg accepted, but the official-limits pre-check (check/prechk/prechk.sh) is missing")
    if codes.get("prechk") != 0:
        emit("DECLINED", 2, f"pre-check exit {codes.get('prechk')} (the official comparator may fail on this export): "
             + result["legs"]["prechk"]["tail"])
    emit("ACCEPTED", 0, "kcompare ok; " + ", ".join(n + " accepted" for n in kernels)
         + ("; official nanoda accepted" if use_nanoda else "") + "; pre-check clean")


if __name__ == "__main__":
    # exit 1 (REJECTED) only ever comes from an explicit emit("REJECTED", 1, ...) above; any internal error (exception,
    # Python's own exit status 1 for an uncaught exception) must never look like a verdict -> DECLINED, exit 2
    try:
        main(sys.argv[1:])
    except SystemExit:
        raise
    except BaseException as e:  # noqa: BLE001
        sys.stdout.write(json.dumps({"checker": "checkB", "verdict": "DECLINED", "exit": 2,
                                     "detail": f"internal error: {e!r}"}) + "\n")
        sys.exit(2)

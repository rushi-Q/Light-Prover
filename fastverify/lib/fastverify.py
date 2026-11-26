#!/usr/bin/python3 -I
"""fastverify: complete verification of a Lean 4 project against a clean challenge.

    bin/fastverify PROJECT CHALLENGE OUT [options]       (see README.md; `bin/fastverify --help`)

Stages: preflight -> prepare -> build -> export -> checks -> OUT/result.json.
Every stage is a separate executable (config/components.json) with the exit convention
    0 = ok / ACCEPTED, 1 = failed / REJECTED, 2 = declined / could not run (fail closed).
The OFFICIAL verdict (unmodified Lean 4.36 `lake comparator` from the exports) is the reference result; the fast checkers
are reported separately and can never turn a non-accept into an accept.
This process runs under `env -i` (bin/fastverify) and never reads verdict-relevant settings from the environment.
"""
import argparse
import datetime
import hashlib
import json
import os
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
VERSION = "0.1.0"
PY = "/usr/bin/python3"
BWRAP = "/usr/bin/bwrap"
# top-level directories an untrusted sandbox still sees (system dirs, pseudo filesystems, and the ones
# the sandbox already replaces by a tmpfs); every other top-level directory is hidden behind an empty tmpfs
SBX_KEEP = frozenset(("bin", "sbin", "lib", "lib32", "lib64", "libx32", "usr", "etc", "dev", "proc", "sys", "nix", "gnu",
                      "home", "root", "tmp", "run", "var"))

# 4.36 Lake/CLI/Check.lean primitiveTargets (verbatim order)
# host/resource failures: never the project's verdict (fail closed -> ERROR); same list in build/official-build.sh
HOST_ERROR_RE = r"No space left on device|Cannot allocate memory|Resource temporarily unavailable|failed to create " \
                r"thread|Too many open files|mmap.*failed|out of memory|Stale file handle|failed to read file '"
PRIMITIVES = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble",
              "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat",
              "List", "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam",
              "outParam"]
S1_PERMITTED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")   # GOAL S1(3)


# ---- Lean names and releases exactly as the judges and the cross-version gate read them
_XV = []


def _xvcheck():
    """check/xversion/xvcheck.py (loaded once by path): parse_lean_name = the exact `String.toName` mirror that the judges
    (check-sound*.sh q02_canon) and the gate use; parse_meta_line / load_release_table = the gate's strict release reader"""
    if not _XV:
        import importlib.util
        p = os.path.join(ROOT, "check", "xversion", "xvcheck.py")
        spec = importlib.util.spec_from_file_location("fastverify_xvcheck", p)
        if spec is None or spec.loader is None:
            raise Refuse(f"{p} missing: Lean names / the challenge release cannot be read")
        m = importlib.util.module_from_spec(spec)
        try:
            spec.loader.exec_module(m)
        except (OSError, SyntaxError) as e:
            raise Refuse(f"{p}: {e}") from e
        _XV.append(m)
    return _XV[0]


def sha256_and_first_line(path):
    """sha256 of the whole file and its first line (<= 1 MiB, with the newline) from ONE read"""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        first = f.readline(1 << 20)
        h.update(first)
        for chunk in iter(lambda: f.read(1 << 24), b""):
            h.update(chunk)
    return h.hexdigest(), first


def lean_name_key(x):
    """the canonical Lean name (component tuple) of a config / target-list string; () for a non-string or a string that
    String.toName maps to Name.anonymous. `«propext»` and `propext` are the same name; `«Quot.sound»` is the ONE-component
    name «Quot.sound», not Quot.sound."""
    return _xvcheck().parse_lean_name(x) if isinstance(x, str) else ()


def split_lean_names(text):
    """a target list (export-targets.txt) -> its names: separated by whitespace OUTSIDE «...» (whitespace inside «...»
    belongs to the name, as in String.toName). Reads both layouts exactly: one name per line (what this package writes) and
    several names per line (the RH challenge's file). None if a « is never closed."""
    out, cur, inq = [], [], False
    for c in text:
        if inq:
            cur.append(c)
            inq = c != "»"
        elif c == "«":
            cur.append(c)
            inq = True
        elif c.isspace():
            if cur:
                out.append("".join(cur))
                cur = []
        else:
            cur.append(c)
    if inq:
        return None
    if cur:
        out.append("".join(cur))
    return out


# a child killed by a resource limit (SIGXFSZ / SIGXCPU: exit 128+25 / 128+24, or EFBIG) or by
# any signal did not judge the proof: such a stage failure is ERROR / no verdict, never REJECTED
RESOURCE_KILL_RE = (r"File size limit exceeded|File too large|EFBIG|SIGXFSZ|CPU time limit exceeded|SIGXCPU|"
                    r"exited with code (?:1(?:2[89]|[3-9][0-9])|2[0-5][0-9])\b")


def resource_limits_finite():
    """the finite RLIMIT_FSIZE / RLIMIT_CPU this run inherited (ulimit -f / -t, tools/guard --guard fsize= / cpu=): with
    them a failing child may have been stopped by the host, so a build / export failure is not a judgement"""
    import resource
    out = []
    for nm in ("RLIMIT_FSIZE", "RLIMIT_CPU"):
        try:
            soft, _hard = resource.getrlimit(getattr(resource, nm))
        except (AttributeError, ValueError, OSError):
            continue
        if soft != resource.RLIM_INFINITY:
            out.append(f"{nm}={soft}")
    return out


def resource_failure_evidence(paths):
    """'' or why the failure in these logs (files / directories, last 4 MB of each) looks like a host / resource / signal
    stop rather than a compile error"""
    import re as _re
    # a finite but unhit limit is no evidence: only an actual stop in the logs counts
    rx = _re.compile(RESOURCE_KILL_RE + "|" + HOST_ERROR_RE)
    files = []
    for p in paths:
        if os.path.isdir(p):
            for r, _ds, fs in os.walk(p):
                files += [os.path.join(r, f) for f in fs]
        elif os.path.isfile(p):
            files.append(p)
    for f in files[:2000]:
        try:
            with open(f, "rb") as fh:
                fh.seek(max(0, os.path.getsize(f) - (4 << 20)))
                m = rx.search(fh.read().decode("utf-8", "replace"))
        except OSError:
            continue
        if m:
            return f"{os.path.basename(f)}: '{m.group(0)}'"
    return ""


def json_finite(o):
    """result.json carries only finite JSON numbers: NaN / Infinity (not JSON) -> null"""
    if isinstance(o, float):
        return o if o == o and o not in (float("inf"), float("-inf")) else None
    if isinstance(o, dict):
        return {k: json_finite(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [json_finite(v) for v in o]
    return o


SVC_SCRIPT = "check/sound/check-sound-svc.sh"   # check-sound.sh + --integrity-cache
FRONTIER_SCRIPT = "check/frontier/check-frontier.sh"   # conditional check modulo a sorry frontier (--modulo-frontier)
# ---- the option menu (README "Option matrix") ----
CHECK_OPTS = {   # option -> (result key = stage key in config/components.json stages, description)
    "C0": ("official", "official lake comparator OF THE CHALLENGE'S RELEASE (THE verdict): 4.36.0 -> the 4.36.0 comparator; "
                       ">= 4.37 (4.37.0-rc1) -> that release's own comparator; earlier releases -> the 4.36.0 comparator "
                       "after the cross-version gate (check/official/check.sh)"),
    "C3": ("checkB", "dual independent kernels gruszka + nano-lean + kcompare"),
    "C4": ("checkB_single", "single independent kernel gruszka + kcompare - UNSAFE opt-in"),
    "CS": ("sound", "SOUND check (GOAL S1): official judge code (compareAt + checkAxioms) + official 4.36 kernel libraries "
                    "(parallel Lean.Replay walk) + an independent second kernel (gruszka); no equivalence gates"),
    "CN": ("notary", "NOTARY check: unmodified official Lean 4.36 release libraries + runtime 3-leg "
                     "canonical env SHA-256 digest cross-check + selectable vetted second kernels"),
}
# RETIRED together with the legacy judge check A (C1 = checkA, C2 = checkA_patched; its successor is the sound judge CS).
# A retired name is REFUSED (exit 2) with this message, never mapped to another option. check A and its documentation
# remain available on the archive branch archive/checkA of the release repository.
RETIRED_NOTE = "was retired in v0.1 together with the legacy judge check A (C1/C2; kept on the branch archive/checkA)"
RETIRED_REPLACEMENT = "use --preset sound (or --preset sound-auto): its trusted check CS is check A's successor"
RETIRED_CHECKS = {
    "C1": f"--check C1 (check A) {RETIRED_NOTE}; {RETIRED_REPLACEMENT}, or --check CS with explicit options",
    "C2": f"--check C2 (check A with the patched kernel, UNSAFE) {RETIRED_NOTE}; {RETIRED_REPLACEMENT}, or --check CS "
          "with explicit options",
    "fast": f"--check fast (= C1,C3) {RETIRED_NOTE}; {RETIRED_REPLACEMENT} (check B alone: --check C3)",
    "both": f"--check both (= C1,C3,C0) {RETIRED_NOTE}; {RETIRED_REPLACEMENT} (official verdict: --preset reference; "
            "check B + official comparator on B1+E1: --check C3,C0)",
}
RETIRED_PRESETS = {
    "fast-exact": f"--preset fast-exact (B2+E1+C1) {RETIRED_NOTE}; {RETIRED_REPLACEMENT}. (The B3 build item "
                  "'fast-exact' of the sound presets is unrelated and unchanged.)",
    "default": f"--preset default (B1+E1+C1,C3,C0) {RETIRED_NOTE}; {RETIRED_REPLACEMENT} (official verdict: --preset "
               "reference; check B + official comparator on B1+E1: --check C3,C0)",
}
RETIRED_UNSAFE = {
    "nanoda-c07": f"--unsafe nanoda-c07 (a modifier of C1/C2) {RETIRED_NOTE}; {RETIRED_REPLACEMENT}",
}
RETIRED_FAST_CHECKS = (f"--fast-checks (choice between checkA and checkB for --check fast|both) {RETIRED_NOTE}; "
                       f"{RETIRED_REPLACEMENT} (check B alone: --check C3)")
RETIRED_FAST_POLICY = (f"--fast-policy checkA (an alias of 'primary') {RETIRED_NOTE}; use --fast-policy primary (the "
                       "default), and for a trusted verdict --preset sound (or --preset sound-auto)")
NO_PRESET = (f"no --preset and no --check given: the former default preset 'default' (B1+E1+C1,C3,C0) {RETIRED_NOTE}; "
             "choose a preset - --preset sound (or sound-auto) for the trusted verdict, --preset reference for the "
             "official lake comparator, --preset notary - or give the checks explicitly with --check")
# E1 (native exporter) is validated only up to 128 threads: its f581123 core keeps the worker index in a uint8, so >= 256
# workers silently drop dependencies (observed: truncated export, exit 0). Never give it more.
E1_MAX_THREADS = 128
# with the output on tmpfs (--export-dir) more threads help a little (128 27.2 s / 192 25.2 s / 256 24.9 s, all
# byte-identical; the pinned exporter 979c4f8 has a 16-bit worker index); on ext4 they hurt
E1_MAX_THREADS_TMPFS = 256
FAST_PRIORITY = ("CN", "CS", "C3", "C4")   # the strongest selected fast check decides verdict_fast, the others can veto
UNSAFE_BUILD_OPTS = {   # B3 options (names = build/build.sh --unsafe) -> finding tests (tests/NNN-*) that break them (OPEN: opt-in only)
    "skip-kernel-tc": "007 017 030 038", "linter-off": "022", "retries": "062", "native-pkg": "015 057",
    "toolchain-T1": "004 014 020 031 037 040 046 048 050 052 061",
    # sound items (sound preset; outside sound mode they are UNSAFE like every B3 item; ARGS after '=' allowed)
    "merge": "sound mode only (S02: module merging changes names/visibility inside merged groups)",
    "fast-exact": "sound mode only (S04: plugin skips the elaborator's own check of with_unfolding_all exact)",
    "premise-off": "sound mode only (S07: setup.json imports a helper that suppresses premise-selection metadata)",
    "lean-path-order": "sound mode only (S07: LEAN_PATH reordered, root lib first)",
    "zygote": "sound mode only (S01: forked zygote process with memoized imports)",
    "zygote-prefix": "sound mode only (S01: children continue a pre-imported prefix; not bit-identical)",
    "j1-saturated": "sound mode only (S01: elaboration thread count)",
    "sound-fast-path": "sound mode only (S07: skips the exactness-only guards plancheck/depcheck/source digests)",
    "cost-hints": "sound mode only (S07: per-module cost estimates of an earlier run steer priorities/threads)",
    "check-tail": "sound mode only (S07: modules with long kernel-check jobs get build priority, for --overlap-targeted)",
    "closure-only": "sound mode only (A05/A03, D22: only the import closure of the solution module is built, as the official "
                    "lake comparator does; a failing module outside it does not fail the build)",
}   # the deny item (findings 021 023 025 028) of the older fast build is not offered: it edits sources


LEGACY_UNSAFE_BUILD = ["linter-off", "native-pkg", "retries", "skip-kernel-tc", "toolchain-T1"]   # preset fastest, 'all'


def build_opt_base(u):
    """'merge=max-members=24' -> 'merge' (B3 items may carry arguments after '=')."""
    return u.split("=", 1)[0]
UNSAFE_CHECK_OPTS = {   # unsafe modifiers of fast checks -> (applies to, extra args, what breaks)
    "ignore-order": (("C3", "C4"), ["--unsafe", "ignore-order"],
                     "012 OPEN: the official replay can reject valid string-literal/Quot/Nat-literal proofs depending on "
                     "names; independent kernels cannot reproduce that"),
}   # nanoda-c07 (C1/C2 only) retired with check A: RETIRED_UNSAFE
# SOUND mode (preset sound / sound-fastest, check CS): soundness is the guarantee, equivalence with the official
# toolchain only a test oracle (docs/concepts/soundness.md, soundness rules S1-S5). The build and the
# exporter are UNTRUSTED: every transform below can only make the trusted check reject or give no verdict, never accept
# (the trusted check re-establishes statements, axioms and every declaration's kernel acceptance from the export alone).
SOUND_TRANSFORMS = {   # B3 item -> why it cannot cause a false ACCEPT (README "Sound mode")
    "skip-kernel-tc": "the build-time kernel check is redone by the trusted kernels on every exported declaration; an "
                      "ill-typed declaration in the closure is rejected there, one outside the closure is irrelevant to "
                      "the targets",
    "linter-off": "linters only produce messages; they never change a declaration",
    "toolchain-T1": "the patched/PGO lean only produces .olean files; whatever it elaborates is re-checked from the export "
                    "(statements compared with the OFFICIAL challenge export, every declaration replayed by the official "
                    "kernel and gruszka)",
    "native-pkg": "native tactic code only changes how the build elaborates; the result is re-checked from the export",
    "retries": "a rebuild only changes whether the build succeeds; the result is re-checked from the export",
    "merge": "merging modules (S02) only changes how the untrusted build elaborates (one lean process per group, a failed "
             "group falls back to its members' exact invocations); statements are compared with the OFFICIAL challenge "
             "export and every exported declaration is replayed by both trusted kernels, so a declaration missing or "
             "changed by the build can only cause a rejection",
    "fast-exact": "the plugin (S04) only skips the elaborator's own type check of `with_unfolding_all exact` when the "
                  "kernel's definitional-equality check confirms it (else the official tactic runs); it only changes how "
                  "the untrusted build produces .olean files, every exported declaration is re-checked by both trusted "
                  "kernels",
    "premise-off": "only changes which library-suggestion metadata (premise selection) the untrusted build writes into "
                   "its own .olean files (S07; via setup.json imports, no source edit); the deny lists are read only by "
                   "premise-selection code, never by the exporter or the trusted checkers; the export is re-checked from "
                   "scratch against the official challenge",
    "lean-path-order": "the same LEAN_PATH entries in another order (root lib first, S07); plancheck refuses any module "
                       "present in two search roots, so every import resolves to the same file; the build is untrusted "
                       "anyway",
    "zygote": "a forked zygote that read the immutable package oleans once (memoized module data, optionally copied "
              "into huge-page memory; S01) only changes how the untrusted build loads imports; its .olean files are "
              "re-checked from the export by both trusted kernels",
    "zygote-prefix": "zygote children continue a pre-imported prefix environment (S01; not bit-identical to a fresh "
                     "import): this can only change what the untrusted build elaborates, which is re-checked from the export",
    "j1-saturated": "only the number of elaboration threads of the untrusted build (S01)",
    "sound-fast-path": "skips guards that only serve EXACTNESS of the build (plancheck's importArts equivalence, Lake's "
                       "dependency up-to-date check, the source digests before/after; S07): a stale dependency, a "
                       "colliding olean or a source changed during the build can only change what the untrusted build "
                       "produces, which is re-checked from the export against the official challenge",
    "cost-hints": "per-module cost estimates from an earlier run of the same project (S07; for RH: run-1 walls x S04's "
                  "fast-exact factors) only steer the scheduler's ORDER and the per-lean thread count; every module is "
                  "still built by lean from the same sources and the export is re-checked from scratch, so a wrong or "
                  "hostile hint file can only make the build slower",
    "check-tail": "the longest kernel-check job of each module (from an earlier check's slow-job log) is added to the "
                  "module's scheduling priority (S07), so that modules whose declarations the targeted overlap checks "
                  "early are built early; ORDER only - the build output and every trusted check are unchanged",
    "closure-only": "only the modules in the import closure of the solution module are built (A05; exactly the module set "
                    "the official `lake comparator` builds: safeLakeBuild #[solution module]; planned by the planner's "
                    "--targets, A03): the exporter reads only that closure, so modules outside it cannot contribute a "
                    "declaration to the export, and a closure module that is missing or wrong can only fail the "
                    "build/export or be rejected by the trusted check",
}
PRESETS = {
    "reference": {"build": "B0", "export": "E0", "check": ["C0"], "unsafe": []},
    # fastest uses check B (C4), not check A: unchanged by check A's retirement (experimental, labelled UNSAFE)
    "fastest": {"build": "B3", "export": "E1", "check": ["C4"], "unsafe": LEGACY_UNSAFE_BUILD + ["ignore-order"]},
    # 'fast-exact' and 'default' (both C1-based) were retired: RETIRED_PRESETS (refused, never mapped)
    # sound: untrusted fast build (B3 with the transforms measured on RH) + E1 + the trusted
    # check CS. toolchain-T1 tries the PORTABLE zygote-capable PGO tree first (same sources/profile, identical .olean and
    # export bytes, needs only glibc >= 2.17), then the original zygote tree (glibc >= 2.38 + host libuv/OpenSSL 3/GMP); the
    # 4.37.0-rc1 PGO tree is taken only for 4.37 projects (build.sh's base filter),
    # then the PGO / portable trees; zygote items fall back to plain lean without a zygote-capable lean; the cost-hints
    # default file is RH's (modules absent from it count as unknown -> static priority).
    "sound": {"build": "B3", "export": "E1", "check": ["CS"],
              # skip-kernel-tc=except-translate (G1-ML-2 fix): modules that mention to_additive / to_dual keep the
              # build-time kernel check (Mathlib's translation reads kernel errors; skipping gave false REJECTs)
              "unsafe": ["toolchain-T1=lean4-s01zy-3cf5641cbd-pgo-portable lean4-s01zy-3cf5641cbd-pgo lean4-v4.37.0-rc1-pgo-portable lean4-d5e35ef223-pgo-portable lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo-portable lean4-7586a50cec-nopgo",
                         "skip-kernel-tc=except-translate", "linter-off", "retries", "premise-off", "fast-exact",
                         "zygote",
                         "zygote-prefix", "j1-saturated", "sound-fast-path", "cost-hints", "native-pkg", "merge",
                         "check-tail"],
              # orchestrator defaults of the preset (explicit flags win): the untrusted export on tmpfs if >= 256 GB free;
              # the targeted overlap of the Lean-kernel leg with the build (S04/S08) is OFF by default since internal assurance
              # findings: its skip path can accept a target the plain replay rejects (the official-kernel
              # leg then rests on gruszka alone); measured gain ~0 (RH run 7 plain 1,789 s vs runs 8/9 targeted 1,766 /
              # 1,803 s). Explicit '--overlap-targets FILE' still enables it.
              "options": {"export_dir": "/dev/shm", "overlap_targets": "none"}},
    # sound-auto (additive): the SAME trusted check CS; the untrusted build option, the B3 items (a subset of
    # the sound preset's, plus skip-kernel-tc=except-translate), threads, export dir and overlap are chosen per project and
    # host by lib/autotune.py from the sources' headers/markers and the host's limits (recorded in result.json "autotune";
    # `python3 -I lib/autotune.py PROJECT` prints the choice). Explicit flags win, as for every preset.
    "sound-auto": {"build": "B3", "export": "E1", "check": ["CS"], "unsafe": [], "auto": True},
    # notary (additive, default-off): maximum offline assurance — official build/export (B0+E0) +
    # unmodified official Lean 4.36 release kernel libraries + runtime 3-leg canonical SHA-256 digest cross-check
    # (ccmp-notary == pleanchecker-notary == gruszka-r7) + optional extra bundled kernels (--notary-kernels).
    "notary": {"build": "B0", "export": "E0", "check": ["CN"], "unsafe": []},
}


# markers in an exact retry's messages that can come from an import built differently by the transformed build
RETRY_SUSPECT = ("(kernel)", "to_dual", "to_additive", "translated value")


def exact_retry_failures(sched_out):
    """The scheduler records of a FAILED fast build -> [{module, rc, error}] if EVERY module whose final record failed
    was retried with its exact official invocation (build/sched.py event 'retry-exact': official lean, Lake's argv and
    setup) and failed again with lean's error exit; None otherwise (then the full exact rebuild B1 decides, as before).
    The failed set comes from the final per-module records, not from the (truncated) 'BUILD FAILED' line."""
    try:
        lines = open(sched_out, encoding="utf-8", errors="replace").read().splitlines()
    except OSError:
        return None
    last, retried, saw_failed_line = {}, {}, False
    for i, ln in enumerate(lines):
        if ln.startswith("BUILD FAILED:"):
            saw_failed_line = True
            continue
        if not ln.startswith("{"):
            continue
        try:
            r = json.loads(ln)
        except ValueError:
            continue
        m = r.get("module") if isinstance(r, dict) else None
        if not isinstance(m, str):
            continue
        if r.get("event") == "retry-exact":
            retried.setdefault(m, i)
        elif r.get("event") == "module":
            last[m] = (i, r)
    failed = [m for m, (i, r) in last.items() if r.get("rc") != 0 or r.get("error_msg") or r.get("missing")]
    if not saw_failed_line or not failed:
        return None
    out = []
    for m in sorted(failed):
        i, r = last[m]
        if m not in retried or retried[m] > i or r.get("rc") not in (0, 1) or r.get("missing"):
            return None   # not retried exactly (e.g. released early), killed / crashed, or outputs missing: full B1 decides
        txt = str(r.get("stdout_head") or "") + "\n" + str(r.get("stderr_head") or "")
        if any(k in txt for k in RETRY_SUSPECT):
            return None   # kernel / translation error: an import built by the transformed build may differ from the
            # official one (@[to_dual] without kernel TC upstream -> the exact retry fails too), so B1 decides
        err = None
        for ln in str(r.get("stdout_head") or "").splitlines():
            try:
                msg = json.loads(ln)
            except ValueError:
                continue
            if isinstance(msg, dict) and msg.get("severity") == "error":
                pos = msg.get("pos") or {}
                err = f"{os.path.basename(str(msg.get('fileName', '')))}:{pos.get('line')}:{pos.get('column')}: " \
                      f"{str(msg.get('data', ''))[:300]}"
                break
        out.append({"module": m, "rc": r.get("rc"), "error": err})
    return out


TMPFS_EXPORT_MIN_BUDGET = 512 << 30   # as sound-auto's autotune rule for the /dev/shm export


def memory_budget_bytes():
    """min(MemAvailable, memory.max - memory.current of every limited cgroup of this process), None if unknown."""
    vals = []
    try:
        for ln in open("/proc/meminfo"):
            if ln.startswith("MemAvailable:"):
                vals.append(int(ln.split()[1]) * 1024)
    except (OSError, ValueError):
        pass
    try:
        rel = [ln.split("::", 1)[1].strip() for ln in open("/proc/self/cgroup") if ln.startswith("0::")]
        d = "/sys/fs/cgroup" + (rel[0].rstrip("/") if rel else "")
        while d.startswith("/sys/fs/cgroup") and d != "/sys/fs/cgroup":
            try:
                m = open(os.path.join(d, "memory.max")).read().strip()
                if m != "max":
                    c = int(open(os.path.join(d, "memory.current")).read().strip())
                    vals.append(int(m) - c)
            except (OSError, ValueError):
                pass
            d = os.path.dirname(d)
    except OSError:
        pass
    return min(vals) if vals else None


def is_tmpfs(path):
    """the file system holding path is a tmpfs (longest mount-point prefix in /proc/self/mounts)."""
    try:
        p = os.path.realpath(path)
        best, typ = "", ""
        for ln in open("/proc/self/mounts"):
            f = ln.split()
            if len(f) >= 3 and (p == f[1] or p.startswith(f[1].rstrip("/") + "/")) and len(f[1]) >= len(best):
                best, typ = f[1], f[2]
        return typ == "tmpfs"
    except OSError:
        return False


def integrity_cache_dir(top=None):
    """(sound-auto) private directory for integrity records: /tmp/fastverify-icache-UID/<sha256(host, package root)>,
    both levels created 0700; None unless both are real directories owned by this user without group/other access (then
    every integrity check runs in full, as in the other presets)."""
    import stat as st_
    uid = os.getuid()
    top = top or f"/tmp/fastverify-icache-{uid}"
    sub = os.path.join(top, hashlib.sha256(f"{socket.gethostname()}\0{os.path.realpath(ROOT)}".encode()).hexdigest()[:16])
    for d in (top, sub):
        try:
            os.mkdir(d, 0o700)
        except FileExistsError:
            pass
        except OSError:
            return None
        try:
            s = os.lstat(d)
        except OSError:
            return None
        if not st_.S_ISDIR(s.st_mode) or s.st_uid != uid or (s.st_mode & 0o077):
            return None
    return sub


def tree_stamp(root):
    """The service integrity stamp (check/sound/check-sound-svc.sh): sha256 over (path, device, inode, mode incl. type, size,
    mtime ns, ctime ns, link count, symlink target) of the root and every entry below it, sorted. Any content change of a
    file sets its ctime (write/truncate/chmod/rename/link; unprivileged code cannot set ctime back) or gives a new inode, so
    an unchanged stamp means unchanged files. None (= no stamp, verify in full) if the root is a symlink or anything below
    it cannot be listed or stat'ed."""
    import stat as st_
    if os.path.islink(root) or not os.path.isdir(root):
        return None
    lines = []

    def ent(p):
        s = os.lstat(p)
        tgt = os.readlink(p) if st_.S_ISLNK(s.st_mode) else ""
        lines.append(f"{p}\0{s.st_dev}\0{s.st_ino}\0{s.st_mode}\0{s.st_size}\0{s.st_mtime_ns}\0{s.st_ctime_ns}\0"
                     f"{s.st_nlink}\0{tgt}")

    def fail(e):
        raise e
    try:
        ent(root)
        for dp, dns, fns in os.walk(root, onerror=fail):   # symlinks to directories are listed, not followed
            for n in dns + fns:
                ent(os.path.join(dp, n))
    except OSError:
        return None
    lines.sort()
    return hashlib.sha256("\n".join(lines).encode("utf-8", "surrogateescape")).hexdigest()


def _tree_record_key(prefix, tid):
    """An integrity record holds for exactly this tree, pinned manifest and verifier (lib/toolchain.py)."""
    h = hashlib.sha256()
    man = os.path.join(ROOT, "toolchains", tid.replace("/", "--").replace(":", "---") + ".json")
    for f in (man, os.path.join(ROOT, "lib", "toolchain.py")):
        h.update(sha256_file(f).encode() + b"\0")
    h.update(f"{os.path.realpath(prefix)}\0{tid}".encode())
    return h.hexdigest()


def _read_private(path):
    """Content of a regular file owned by this user (not a symlink), else None."""
    import stat as st_
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    except OSError:
        return None
    with os.fdopen(fd, "rb") as f:
        s = os.fstat(f.fileno())
        if not st_.S_ISREG(s.st_mode) or s.st_uid != os.getuid():
            return None
        return f.read(4096).decode("ascii", "replace")


def autotune_preset(a, pre):
    """--preset sound-auto: the preset dictionary chosen by lib/autotune.py (untrusted; only selects sound-preset items)."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("fv_autotune", os.path.join(ROOT, "lib", "autotune.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    given = any(x == "--threads" or x.startswith("--threads=") for x in sys.argv[1:])
    d = mod.plan(a.project, getattr(a, "packages", None), a.threads if given else None, ROOT)
    if not given:
        a.threads = d["threads"]
        a.autotune_check_threads = getattr(mod, "check_threads", None)
    a.autotune_check_plan = getattr(mod, "check_plan", None)
    # integrity records for the one-shot run's fixed cost (tree verifications, the trusted check's pin checks)
    a.integrity_cache = None if getattr(a, "no_integrity_cache", False) else integrity_cache_dir()
    out = dict(pre, build=d["build"], unsafe=list(d["unsafe"]), options=dict(d["options"]))
    return out, d


CHILDREN = set()          # running stage processes (each in its own session / process group)
CHILDREN_LOCK = threading.Lock()


def run_child(argv, **kw):
    """subprocess.run in a new session, registered so that SIGTERM/SIGINT of fastverify stops the whole stage tree."""
    timeout = kw.pop("timeout", None)
    inp = kw.pop("input", None)
    with subprocess.Popen(argv, start_new_session=True, **kw) as p:
        with CHILDREN_LOCK:
            CHILDREN.add(p)
        try:
            out, err = p.communicate(inp, timeout=timeout)
        except subprocess.TimeoutExpired:
            kill_tree(p)
            p.wait()
            raise
        finally:
            with CHILDREN_LOCK:
                CHILDREN.discard(p)
        return subprocess.CompletedProcess(argv, p.returncode, out, err)


def kill_tree(p):
    import signal
    try:
        os.killpg(p.pid, signal.SIGTERM)
    except (ProcessLookupError, PermissionError):
        pass


class Refuse(Exception):
    """The run cannot be performed exactly: report ERROR (exit 2), never a verdict."""


def now_iso():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 24)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def tree_digest(root, threads=16, skip_top=(".lake",)):
    """sha256 over the sorted list of (relative path, kind, content sha256 / link target) of every entry under root."""
    import concurrent.futures
    entries = []
    for d, dns, fns in os.walk(root):
        if d == root:
            for x in skip_top:
                if x in dns:
                    dns.remove(x)
                if x in fns:
                    fns.remove(x)
        dns.sort()
        for n in sorted(dns + fns):
            p = os.path.join(d, n)
            rel = os.path.relpath(p, root)
            if os.path.islink(p):
                entries.append((rel, "l", os.readlink(p)))
            elif os.path.isdir(p):
                entries.append((rel, "d", ""))
            else:
                entries.append((rel, "f", p))
    files = [e for e in entries if e[1] == "f"]
    with concurrent.futures.ThreadPoolExecutor(threads) as ex:
        sums = dict(zip((e[2] for e in files), ex.map(sha256_file, (e[2] for e in files))))
    h = hashlib.sha256()
    for rel, kind, x in sorted(entries):
        h.update(f"{rel}\0{kind}\0{sums[x] if kind == 'f' else x}\n".encode("utf-8", "surrogateescape"))
    return h.hexdigest(), len(files)


def copy_project(src, dst, threads=32):
    """Measured on a 384-thread server (local disk): the thread pool made the 175k-file copy SLOWER (23.5 s vs
    6.3 s for shutil.copytree; GIL + per-file syscalls), while on an NFS-backed server it helped (98.6 -> 40.0 s). The default is
    therefore the sequential copytree; the pool is used only when the source is on NFS."""
    try:
        nfs = any(ln.split()[1] != "/" and os.path.realpath(src).startswith(ln.split()[1].rstrip("/") + "/")
                  and ln.split()[2].startswith("nfs") for ln in open("/proc/mounts"))
    except OSError:
        nfs = False
    if not nfs:
        shutil.copytree(src, dst, symlinks=True, ignore=lambda d, names: [".lake"] if os.path.realpath(d) ==
                        os.path.realpath(src) else [])
        return
    return _copy_project_pool(src, dst, threads)


def _copy_project_pool(src, dst, threads=32):
    """shutil.copytree(src, dst, symlinks=True) without src's top-level .lake, with the file copies done by a thread pool
    (the 175k-file RH project took 6.3 s sequentially on a 384-thread server). Same result: every directory, regular
    file (shutil.copy2: data + mode + times) and symlink (link target verbatim), directory stats copied last."""
    import concurrent.futures
    src = os.path.realpath(src)
    dirs, items = [], []
    for root, dns, fns in os.walk(src):
        if root == src and ".lake" in dns:
            dns.remove(".lake")
        if root == src and ".lake" in fns:
            fns.remove(".lake")
        d = os.path.normpath(os.path.join(dst, os.path.relpath(root, src)))
        dirs.append((root, d))
        for n in list(dns):
            if os.path.islink(os.path.join(root, n)):   # copytree(symlinks=True) copies a dir symlink as a symlink
                dns.remove(n)
                items.append((os.path.join(root, n), os.path.join(d, n)))
        items += [(os.path.join(root, n), os.path.join(d, n)) for n in fns]
    for _, d in dirs:
        os.makedirs(d, exist_ok=True)

    def cp(sd):
        s_, d_ = sd
        if os.path.islink(s_):
            os.symlink(os.readlink(s_), d_)
        else:
            shutil.copy2(s_, d_)
    with concurrent.futures.ThreadPoolExecutor(threads) as ex:
        for _ in ex.map(cp, items, chunksize=256):
            pass
    for s_, d_ in reversed(dirs):
        shutil.copystat(s_, d_)


def rmtree_force(path):
    """rmtree that also removes trees a build made read-only (chmod u+w on the way down)."""
    def onerror(func, p, exc):
        try:
            os.chmod(os.path.dirname(p), 0o700)
            if os.path.isdir(p) and not os.path.islink(p):
                os.chmod(p, 0o700)
            func(p)
        except Exception:  # noqa: BLE001
            pass
    if os.path.lexists(path):
        shutil.rmtree(path, onerror=onerror)
    if os.path.lexists(path):
        raise Refuse(f"cannot remove {path}")


def log(msg):
    print(f"[{now_iso()}] fastverify: {msg}", file=sys.stderr, flush=True)


class Run:
    def __init__(self, a):
        self.a = a
        self.cfg = json.load(open(os.path.join(ROOT, "config", "components.json")))
        if "${" in json.dumps(self.cfg):
            raise Refuse("config/components.json still contains ${...} variables: run tools/configure.py first")
        self.out = a.out
        self.work = os.path.join(self.out, "work")
        self.logdir = os.path.join(self.out, "log")
        self.tmp = os.path.join(self.out, "tmp")
        self.lock = threading.Lock()
        self.res = {
            "fastverify": {"version": VERSION, "root": ROOT, "argv": sys.argv[1:]},
            "host": socket.gethostname(),
            "started": now_iso(),
            "threads": a.threads,
            "mode": {"preset": a.preset, "build": a.build, "unsafe": a.unsafe, "export": a.export_opt,
                     "check": a.checks, "export_given": bool(a.export), "fast_policy": a.fast_policy,
                     "sound": a.sound, "confirm_reject": bool(getattr(a, "confirm_reject", False))},
            "inputs": {},
            "components": {},
            "build": None,
            "export": None,
            "checks": {},
            "stage_seconds": {},
            "verdict": "ERROR",
            "verdict_basis": "not finished",
            "warnings": [],
        }

    # ---------------------------------------------------------------- utilities
    def save(self):
        with self.lock:
            self.res["updated"] = now_iso()
            p = os.path.join(self.out, "result.json")
            t = p + ".tmp"
            doc = json_finite(self.res)
            # a verdict is final only after the end-of-run integrity check and the final save: until then the
            # file says PENDING (the decision is kept under verdict_pending), so an interrupted run never shows a verdict
            if not getattr(self, "final", False) and doc.get("verdict") in ("ACCEPTED", "REJECTED", "CONDITIONAL"):
                doc = dict(doc, verdict="PENDING", verdict_pending=doc.get("verdict"))
            fd = os.open(t, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
            with os.fdopen(fd, "w") as f:
                json.dump(doc, f, indent=1, sort_keys=False, allow_nan=False)
                f.write("\n")
            os.chmod(t, 0o644)   # explicit mode: readable, writable only by the verifier
            os.replace(t, p)

    def warn(self, msg):
        log("WARNING: " + msg)
        with self.lock:
            self.res["warnings"].append(msg)

    def stage_path(self, key):
        rel = self.cfg["stages"].get(key)
        if not rel:
            return None
        p = os.path.join(ROOT, rel)
        return p if os.path.isfile(p) and os.access(p, os.X_OK) else None

    def child_env(self):
        return {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "HOME": os.path.join(self.tmp, "home"),
                "TMPDIR": self.tmp}

    def run_stage(self, name, argv, logfile, timeout=None):
        """Runs a stage executable; returns (exit, seconds, json_or_None, last_stdout_json_line)."""
        jpath = os.path.join(self.logdir, f"{name}.json")
        if os.path.exists(jpath):
            os.unlink(jpath)
        t0 = time.time()
        with open(logfile, "ab") as lf:
            lf.write(f"[{now_iso()}] $ {' '.join(argv)}\n".encode())
            lf.flush()
            try:
                p = run_child(argv + ["--json", jpath], stdout=subprocess.PIPE, stderr=lf, env=self.child_env(),
                              cwd=self.tmp, timeout=timeout)
                rc = p.returncode
                out = p.stdout.decode("utf-8", "replace")
            except subprocess.TimeoutExpired:
                rc, out = 2, ""
                lf.write(b"fastverify: stage timed out\n")
        sec = round(time.time() - t0, 3)
        lf_json = None
        if os.path.exists(jpath):
            try:
                lf_json = json.load(open(jpath))
            except Exception:  # noqa: BLE001
                lf_json = None
        line_json = None
        for line in reversed(out.strip().splitlines()):
            line = line.strip()
            if line.startswith("{"):
                try:
                    line_json = json.loads(line)
                    break
                except Exception:  # noqa: BLE001
                    pass
        with open(logfile, "ab") as lf:
            lf.write(out.encode())
        if rc < 0:
            rc = 128 - rc
        return rc, sec, lf_json if lf_json is not None else line_json

    @staticmethod
    def stage_report_problem(rc, j, want_verdict=None):
        """None iff the stage's own report j (its --json file, else its last stdout JSON line; run_stage) is
        a JSON object whose integer 'exit' equals the process status rc and, if want_verdict is given, whose 'verdict'
        equals it; else the reason. A verdict (ACCEPTED / REJECTED / CONDITIONAL) is only taken from a stage whose report
        is present, readable and agrees with its exit status; anything else is ERROR (no verdict)."""
        if not isinstance(j, dict):
            return f"stage exited {rc} without a readable report (missing, unreadable or not a JSON object)"
        ex = j.get("exit")
        if type(ex) is not int or ex != rc:
            return f"stage report says exit {ex!r} but the stage exited {rc}"
        if want_verdict is not None and j.get("verdict") != want_verdict:
            return f"stage report says verdict {j.get('verdict')!r} but the stage exited {rc} ({want_verdict})"
        return None

    def sandbox_argv(self, tc, ro=(), rw=(), env=None, chdir="/", binds=()):
        args = [BWRAP, "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", 
                "--tmpfs", "/tmp", "--dir", "/tmp/home", "--tmpfs", "/run", "--tmpfs", "/var"]
        # the official exporter reads UNTRUSTED .olean files: every other top-level directory except
        # the system ones is hidden too (/scratch, /data, ...: OUT with the overlap FIFO, service state dirs, other runs)
        masks = ["/" + d for d in sorted(os.listdir("/"))
                 if d not in SBX_KEEP and os.path.isdir("/" + d) and not os.path.islink("/" + d)]
        for d in masks:
            args += ["--tmpfs", d]
        args += ["--dev", "/dev", "--proc", "/proc", "--clearenv", "--ro-bind", tc, tc]
        for p in ro:
            args += ["--ro-bind", p, p]
        for p in rw:
            args += ["--bind", p, p]
        for src, dst in binds:
            args += ["--ro-bind", src, dst]
        for d in masks:   # read-only after the binds: only visibility changes (a write there fails as before)
            args += ["--remount-ro", d]
        e = {"PATH": f"{tc}/bin:/usr/bin:/bin", "HOME": "/tmp/home", "LANG": "C.UTF-8"}
        e.update(env or {})
        for k, v in e.items():
            args += ["--setenv", k, v]
        args += ["--unshare-all", "--die-with-parent", "--new-session", "--chdir", chdir, "--"]
        return args

    # ---------------------------------------------------------------- preflight
    def resolve_pins(self):
        """the pins file of the trusted check CS: --pins FILE (must be a pins*.env inside check/sound/ of this
        package: no caller paths), or with --preset sound-auto the check/sound/pins-*.env whose TC_VERSION equals the
        challenge's toolchain (the trusted check built from that release, e.g. the 4.37.0-rc1 check). None = the default
        check/sound/pins.env (the 4.36 judge)."""
        import glob
        self.cs_pins = None
        d = os.path.realpath(os.path.join(ROOT, "check", "sound"))
        given = getattr(self.a, "pins", None)
        if given:
            p = os.path.realpath(given if os.path.isabs(given) else os.path.join(ROOT, given))
            if os.path.dirname(p) != d or not os.path.basename(p).startswith("pins") or not p.endswith(".env") \
                    or not os.path.isfile(p):
                raise Refuse(f"--pins {given}: must name a pins*.env file in {d}")
            how = "--pins"
        elif getattr(self.a, "autotune", None) is not None or getattr(self.a, "sound", False):
            # sound-auto with or without autotune, and --preset sound: the trusted
            # check built from the challenge's release (a 4.37 challenge gets the 4.37 judge, never the 4.36 one)
            tc = self.res["inputs"].get("toolchain")
            tc_src = "lean-toolchain"
            if self.given_challenge_export() and (getattr(self.a, "sound", False) or tc is None):
                # the given (pinned) challenge export's own release decides (lean-toolchain must be consistent with it)
                tc, tc_src = self.challenge_export_release(), "the challenge export's meta line"
            if tc is None and self.given_challenge_export():   # export-only, no lean-toolchain
                tc, tc_src = self.challenge_export_release(), "the challenge export's meta line"
            p = None
            for f in sorted(glob.glob(os.path.join(d, "pins-*.env"))):
                try:
                    tv = [ln.split("=", 1)[1].strip() for ln in open(f, encoding="utf-8")
                          if ln.startswith("TC_VERSION=")]
                except OSError:
                    continue
                if tc and tv and tv[0] == tc:
                    p = os.path.realpath(f)
                    break
            if not p:
                self.refuse_436_judge_for_newer_release(None)   # e.g. a 4.37+ release without its own pins file
                return
            # auto-selection only if every pinned file of that judge is installed on this host (the 4.37
            # binaries are missing on some nodes -> no verdict); otherwise the default 4.36 judge decides, which judges other
            # releases' exports under check/xversion's cross-version argument, and the run says so
            missing = []
            try:
                for ln in open(p, encoding="utf-8"):
                    f = ln.split()
                    if len(f) >= 4 and f[0] == "PIN" and not os.path.isfile(f[3]):
                        missing.append(f[3])
            except OSError as e:
                missing.append(str(e))
            if missing:
                # NO fallback to the 4.36 judge: on a 4.37 RH-scale export it ran 60+ min at 1.1 TB RSS without
                # finishing - a memory trap for every job on the node. Refuse before anything is built
                self.res["check_pins_missing"] = {"path": p, "missing": missing[:10]}
                raise Refuse(f"{'sound-auto' if getattr(self.a, 'autotune', None) is not None else 'sound mode'}: "
                             f"{os.path.basename(p)} (the trusted check of {tc}) is not installed on this "
                             f"host (missing: {', '.join(missing[:3])}); deploy it (tools/deploy.sh) or run on a host that has "
                             "it - a challenge of this release is judged only by its own release's judge (no fallback to the "
                             "4.36 judge, also not with --pins: the 4.36 replay order rejects valid 4.37 proofs, and on the "
                             "4.37 RH-scale export the 4.36 judge's run reached 1.1 TB)")
            how = (f"{'sound-auto' if getattr(self.a, 'autotune', None) is not None else 'sound mode'}: the trusted check "
                   f"built from the challenge's release {tc}") + (f" (read from {tc_src})" if tc_src != "lean-toolchain" else "")
        else:
            self.refuse_436_judge_for_newer_release(None)
            return
        self.refuse_436_judge_for_newer_release(p)
        if os.path.realpath(os.path.join(d, "pins.env")) == p:
            if how == "--pins":   # record an explicit selection of the default judge as well
                self.res["check_pins"] = {"path": p, "sha256": sha256_file(p), "selected_by": how, "default": True}
            return
        self.cs_pins = p
        self.res["check_pins"] = {"path": p, "sha256": sha256_file(p), "selected_by": how}
        # the release's hide list (availability only, the verdict is identical with or without it)
        self.cs_hide = None
        hd = os.path.realpath(os.path.join(ROOT, "check", "sound", "hide"))
        want = getattr(self.a, "check_hide", None)
        if want and want != "none":
            h = os.path.realpath(want if os.path.isabs(want) else os.path.join(ROOT, want))
            if os.path.dirname(h) != hd or not os.path.isfile(h):
                raise Refuse(f"--check-hide {want}: must name a file in {hd}")
        elif not want:
            tv = [ln.split("=", 1)[1].strip() for ln in open(p, encoding="utf-8") if ln.startswith("TC_VERSION=")]
            ver = tv[0].split(":v", 1)[-1] if tv else ""
            h = os.path.join(hd, f"lean-{ver}-no-expose.txt") if ver else ""
            h = h if h and os.path.isfile(h) else None
        else:
            h = None
        if h:
            self.cs_hide = h
            self.res["check_pins"]["hide"] = {"path": h, "sha256": sha256_file(h)}
            self.res.setdefault("components", {})["check_hide"] = {"path": h, "sha256": sha256_file(h)}
        self.res.setdefault("components", {})

    def given_challenge_export(self):
        """the private snapshot of CHALLENGE/challenge.export taken ONCE by read_inputs, or None (the challenge is
        then built officially). Unit harnesses that skip read_inputs fall back to the challenge directory itself."""
        snap = getattr(self, "snap", None)
        if snap is None:
            c = getattr(self.a, "challenge", None)
            ce = os.path.join(c, "challenge.export") if c else None
        else:
            ce = os.path.join(snap, "challenge.export")
        return ce if ce and os.path.isfile(ce) else None

    def export_release_tuple(self):
        """(version, githash) of the given challenge export's meta line, read as the gate reads it (strict
        parse_meta_line; the pair must be an entry of releases.json); Refuse otherwise"""
        xv = _xvcheck()
        ce = self.given_challenge_export()   # the snapshot
        if not ce:
            raise Refuse("the challenge export's release cannot be read: no challenge.export was given")
        try:
            with open(ce, "rb") as f:
                raw = f.readline(1 << 20)
            ver, gh, _fmt = xv.parse_meta_line(raw)
            table = xv.load_release_table(os.path.join(ROOT, "check", "xversion", "releases.json"))
        except Exception as e:  # noqa: BLE001
            raise Refuse(f"the challenge export's release cannot be read from its meta line ({str(e)[:200]})") from e
        r = table["releases"].get(ver)
        if r is None or r.get("githash") != gh:
            raise Refuse(f"the challenge export names Lean {ver} ({gh}), a release outside the verified table "
                         f"(check/xversion/releases.json)")
        self.selection_release = (ver, gh)   # re-checked against the HASHED bytes (prepare_challenge_export)
        return ver, gh

    def refuse_436_judge_for_newer_release(self, pins):
        """a challenge of a release >= 4.37 is never judged by
        a Lean 4.36 judge: the 4.36 Lean.Replay order rejects valid 4.37 proofs (String.ofList). Sound mode selects the
        release's own pins (resolve_pins); an explicit --pins naming another release's judge, and the notary judge (4.36
        libraries only), are refused for such a challenge."""
        xb = [c for c in (getattr(self.a, "checks", None) or []) if c in ("C3", "C4")]
        if not (getattr(self.a, "sound", False) or getattr(self.a, "notary", False) or xb):
            return   # a standalone C3 / C4 run is checked as well
        if self.given_challenge_export():
            ver = self.export_release_tuple()[0]
        else:
            tcn = self.res["inputs"].get("toolchain") or ""
            ver = tcn.split(":v", 1)[1] if tcn.startswith("leanprover/lean4:v") else ""
        try:
            newer = tuple(int(x) for x in ver.split("-")[0].split(".")) >= (4, 37, 0)
        except ValueError:
            newer = False
        if not newer:
            return
        if getattr(self.a, "notary", False):
            raise Refuse(f"the challenge is from Lean {ver}: the notary judge has only the Lean 4.36 libraries and never "
                         "judges a 4.37+ challenge; use --preset sound / sound-auto (the release's own judge)")
        if xb:   # check B resolves nanoda from the 4.36 comparator tree: never a 4.37+ judge
            raise Refuse(f"the challenge is from Lean {ver}: {'/'.join(xb)} (check B, the 4.36 comparator tree's nanoda) "
                         "cannot judge a 4.37+ challenge; drop it (the sound check's extra kernels follow the release's pins)")
        tv = []
        if pins:
            try:
                tv = [ln.split("=", 1)[1].strip() for ln in open(pins, encoding="utf-8") if ln.startswith("TC_VERSION=")]
            except OSError:
                tv = []
        if (tv[0] if tv else "leanprover/lean4:v4.36.0") != "leanprover/lean4:v" + ver:
            raise Refuse(f"the challenge is from Lean {ver} but the selected trusted check is "
                         f"{os.path.basename(pins) if pins else 'the default 4.36 judge'}: a 4.37+ challenge is never judged "
                         "by another release's judge (the 4.36 replay order rejects valid 4.37 proofs); use the release's "
                         "pins (automatic with --preset sound / sound-auto)")

    def challenge_export_release(self):
        """export-only mode without lean-toolchain: the release that produced the given challenge
        export, read exactly as the cross-version gate reads it (check/xversion/xvcheck.py: line 1 parsed strictly with
        parse_meta_line; version AND githash must be an entry of releases.json) -> 'leanprover/lean4:vX'. No silent default:
        an unreadable meta line or a release outside the table -> Refuse (no verdict). It only selects which installed
        judge runs; every judge still runs the gate on its own private copies."""
        ver, gh = self.export_release_tuple()   # one reader; the release is bound to the pinned bytes later
        self.res["inputs"]["challenge_release"] = {"version": ver, "githash": gh,
                                                   "source": "challenge export meta line"}
        return "leanprover/lean4:v" + ver

    def judge_release_label(self):
        """the Lean release of the trusted check CS that decides: TC_VERSION of the selected pins file
        (sound-auto / --pins), else the default judge's 4.36"""
        p = getattr(self, "cs_pins", None)
        if p:
            try:
                tv = [ln.split("=", 1)[1].strip() for ln in open(p, encoding="utf-8") if ln.startswith("TC_VERSION=")]
            except OSError:
                tv = []
            if tv and tv[0].startswith("leanprover/lean4:v") and tv[0] != "leanprover/lean4:v4.36.0":
                return tv[0].split(":v", 1)[1]
        return "4.36"

    def c0_comparator(self):
        """the lake comparator that check/official/check.sh (C0) will run, chosen exactly as it chooses:
        a challenge export of a release >= 4.37 whose toolchain is registered in config/components.json lean_toolchains
        with the same commit -> THAT release's comparator; anything else (4.36.0, earlier releases admitted by the gate,
        unreadable meta: check.sh decides / refuses itself) -> config 'comparator' (4.36.0). Without a given challenge
        export the challenge is built + exported with the project's toolchain, whose release then decides.
        -> (prefix, toolchain id, listed sha256s); only used for the component manifest / preflight of C0."""
        import re as _re
        dflt = self.cfg["comparator"]
        ver = gh = None
        ce = self.given_challenge_export() or ""   # the snapshot
        try:
            if os.path.isfile(ce):
                with open(ce, "rb") as f:
                    ver, gh, _fmt = _xvcheck().parse_meta_line(f.readline(1 << 20).rstrip(b"\n"))
            elif self.res["inputs"].get("toolchain"):
                tcn = self.res["inputs"]["toolchain"]
                ver = tcn.split(":v", 1)[1] if tcn.startswith("leanprover/lean4:v") else None
        except Exception:  # noqa: BLE001 - check.sh refuses such an export itself (ERROR); the manifest keeps the default
            ver = None
        if not ver or not _re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?", ver) or \
                tuple(int(x) for x in ver.split("-")[0].split(".")) < (4, 37, 0):
            return dflt["prefix"], dflt["id"], dflt["sha256"]
        tid = "leanprover/lean4:v" + ver
        t = (self.cfg.get("lean_toolchains") or {}).get(tid)
        m = _re.search(r"commit ([0-9a-f]{40})", (t or {}).get("lean_version") or "")
        if not t or not t.get("prefix") or not t.get("sha256") or not m or (gh is not None and m.group(1) != gh):
            return dflt["prefix"], dflt["id"], dflt["sha256"]
        return t["prefix"], tid, t["sha256"]

    def preflight(self):
        t0 = time.time()
        self.resolve_pins()
        ch = getattr(self.a, "check_hints", None)   # fail before the build, not at the check
        if ch and ch != "none" and not os.path.isfile(ch):
            raise Refuse(f"--check-hints {ch}: not a file")
        comps = {}
        bad = []
        if not os.access(BWRAP, os.X_OK):
            bad.append(f"{BWRAP} missing")
        # official toolchain of the project
        tcname = self.res["inputs"]["toolchain"]
        tcs = self.cfg["lean_toolchains"]
        self.tc = None
        if tcname is not None:   # None only with --export and a given challenge.export: nothing is built or exported
            if tcname not in tcs:
                raise Refuse(f"lean-toolchain '{tcname}' is not supported by this package (supported: "
                             f"{', '.join(tcs)}); no exact build/export is possible")
            tc = tcs[tcname]
            self.tc = tc["prefix"]
            self.official_exporter = tc["official_lean4export"]["path"]
            for rel, want in tc["sha256"].items():
                comps[f"toolchain:{rel}"] = self._pin(os.path.join(self.tc, rel), want, bad)
            comps["official_lean4export"] = self._pin(self.official_exporter, tc["official_lean4export"]["sha256"],
                                                      bad)
        cmp_ = self.cfg["comparator"]
        # with C0 the manifest names the comparator check/official/check.sh will really run: for a
        # challenge of a release >= 4.37 with its own registered toolchain that release's lake / lean / leanchecker /
        # nanoda_bin (listed sha256s + its whole-tree manifest), not the 4.36.0 binaries (which that run does not use)
        c0p, c0id, c0sha = self.c0_comparator() if "C0" in self.a.checks else (cmp_["prefix"], cmp_["id"], cmp_["sha256"])
        if c0id != cmp_["id"]:
            for rel in sorted(set(c0sha) | set(cmp_["sha256"])):
                fp = os.path.join(c0p, rel)
                if rel in c0sha:
                    comps[f"comparator:{rel}"] = self._pin(fp, c0sha[rel], bad)
                else:
                    try:
                        comps[f"comparator:{rel}"] = {"path": fp, "sha256": sha256_file(fp),
                                                      "pinned_by": f"toolchain-tree:{c0id}"}
                    except OSError as e:
                        bad.append(f"{fp}: {e}")
            comps["comparator"] = {"id": c0id, "prefix": c0p, "selected_by": "C0: the challenge release's own comparator "
                                   "(check/official/check.sh)"}
            cmp_ = {"prefix": c0p, "id": c0id}
        else:
            for rel, want in cmp_["sha256"].items():
                comps[f"comparator:{rel}"] = self._pin(os.path.join(cmp_["prefix"], rel), want, bad)
        # whole-tree verification of both official toolchains against the pinned manifests (lib/toolchain.py):
        # every file (core .olean, shared libs, binaries) sha256 + mode, no extra/missing entries (findings 020/052/061).
        # The tree verifications and the stage preflights are independent processes: they run CONCURRENTLY (
        # ~11 s -> ~4 s); results are collected in the original order, so the outcome is unchanged.
        import concurrent.futures
        tv = os.path.join(ROOT, "lib", "toolchain.py")
        trees = list((((self.tc, tcname),) if self.tc else ()) + ((cmp_["prefix"], cmp_["id"]),))
        trees = [t for i, t in enumerate(trees) if t not in trees[:i]]   # one verification per tree
        if not os.path.isfile(tv):
            bad.append("lib/toolchain.py missing")
            trees = []
        wanted = list(self.a.checks)
        if not self.a.export:
            wanted += ["build_official"]
            if self.a.build != "B0":
                wanted += ["build_fast"]
            if self.a.export_opt == "E1":
                wanted += ["export"]
        stage_args = {}
        for key in wanted:
            extra = []
            if key in CHECK_OPTS:   # check option: script + option args from config/components.json check_options
                co = self.cfg.get("check_options", {}).get(key, {})
                if key == "CS" and getattr(self.a, "modulo_frontier", None):   # conditional check (additive)
                    co = dict(co, script=FRONTIER_SCRIPT)
                    if getattr(self, "cs_pins", None):   # the wrapper must accept --pins
                        co["args"] = list(co.get("args", [])) + self.frontier_pins_args()
                    if getattr(self.a, "integrity_cache", None) and (not getattr(self, "cs_pins", None) or
                                                                     self.script_has_pins(SVC_SCRIPT)):
                        # the frontier wrapper hands it to check-sound-svc.sh (v2.1 takes --pins too)
                        co["args"] = list(co.get("args", [])) + ["--integrity-cache", self.a.integrity_cache]
                elif key == "CS" and (getattr(self, "cs_pins", None) or self.cs_svc(co)):
                    if self.cs_svc(co):   # the reviewed service variant with integrity records
                        co = dict(co, script=SVC_SCRIPT, args=list(co.get("args", [])) + ["--integrity-cache",
                                                                                           self.a.integrity_cache])
                    if getattr(self, "cs_pins", None):   # check-sound(-svc).sh v2.1 --pins
                        co = dict(co, args=list(co.get("args", [])) + ["--pins", self.cs_pins])
                p = os.path.join(ROOT, co["script"]) if co.get("script") else None
                p = p if p and os.path.isfile(p) and os.access(p, os.X_OK) else None
                extra = list(co.get("args", []))
                if key == "CS" and p:   # the preflight sees the same extra-kernel options as the check
                    xk = [x for k in getattr(self.a, "extra_kernel", []) for x in ("--kernel", k)] + \
                        [x for k in getattr(self.a, "require_kernel", []) for x in ("--require-kernel", k)] + \
                        [x for k in getattr(self.a, "skip_extra_kernel", []) for x in ("--skip-kernel", k)]
                    try:
                        has_xk = "--require-kernel" in open(p, encoding="utf-8", errors="replace").read()
                    except OSError:
                        has_xk = False
                    if getattr(self.a, "require_kernel", None) and (not has_xk or getattr(self.a, "modulo_frontier", None)):
                        raise Refuse(f"--require-kernel: {os.path.basename(p)} cannot run the extra kernels")
                    if xk and has_xk and not getattr(self.a, "modulo_frontier", None):
                        extra += xk
            else:
                p = self.stage_path(key)
            if key == "C0" and p and c0id != self.cfg["comparator"]["id"]:   # preflight the comparator C0 runs
                extra += ["--release", c0id.split(":v", 1)[1]]
            if key == "CS" and p and os.path.basename(p) in ("check-sound.sh", "check-sound-svc.sh"):
                extra += ["--threads", str(self.a.threads)]   # the explicit thread budget, as in the check
            stage_args[key] = (p, None if p is None else
                               [p, "--preflight"] + ([self.tc] if key in ("build_official", "build_fast", "export")
                                                     else extra)
                               + (["--build-cache", self.a.build_cache] if key == "build_fast" and
                                  getattr(self.a, "build_cache", None) else []))

        icache = getattr(self.a, "integrity_cache", None)
        tree_info = {}

        def verify_tree(prefix, tid):
            # (sound-auto) the service's integrity record: the full verification is skipped only if a record written right
            # after an earlier FULL verification of this tree (same manifest, same verifier) holds the current stamp
            info = tree_info.setdefault(tid, {})
            s0 = tree_stamp(prefix) if icache else None
            recf = key = None
            if s0:
                try:
                    key = _tree_record_key(prefix, tid)
                except OSError:   # manifest / verifier unreadable: no record; the full verification reports it
                    s0 = None
            if s0:
                recf = os.path.join(icache, "tree-" + hashlib.sha256(key.encode()).hexdigest()[:24] + ".record")
                if _read_private(recf) == f"{key} {s0}\n":
                    info.update(stamp=s0, integrity="record of an earlier full verification (stamp unchanged)")
                    return subprocess.CompletedProcess([], 0, "", "")
            r = subprocess.run([PY, "-I", tv, "verify", prefix, tid], capture_output=True, text=True,
                               env=self.child_env(), timeout=900)
            if s0 and r.returncode == 0 and tree_stamp(prefix) == s0:   # unchanged while it was verified
                info.update(stamp=s0, integrity="full verification")
                try:
                    fd, tmp = tempfile.mkstemp(prefix=".tree.", dir=icache)
                    with os.fdopen(fd, "w") as f:
                        f.write(f"{key} {s0}\n")
                    os.replace(tmp, recf)
                    info["record"] = "written"
                except OSError:
                    pass
            return r

        def stage_preflight(args):
            try:
                r = subprocess.run(args, capture_output=True, env=self.child_env(), cwd=self.tmp, timeout=600)
                return r.returncode == 0, (r.stderr.decode("utf-8", "replace").strip().splitlines() or [""])[-1]
            except Exception as e:  # noqa: BLE001
                return False, str(e)
        self._cs_deferred = None
        if icache and not self.a.preflight_only and stage_args.get("CS", (None,))[0] and \
                stage_args["CS"][0] in (os.path.join(ROOT, SVC_SCRIPT), os.path.join(ROOT, FRONTIER_SCRIPT)):
            p_cs, args_cs = stage_args.pop("CS")
            self._cs_ex = concurrent.futures.ThreadPoolExecutor(1)
            self._cs_deferred = (p_cs, self._cs_ex.submit(stage_preflight, args_cs))
            self._cs_deferred_retry = (stage_preflight, args_cs)   # re-run once, alone, if it failed
        with concurrent.futures.ThreadPoolExecutor(max(1, len(trees) + len(stage_args))) as ex:
            tree_f = [(prefix, tid, ex.submit(verify_tree, prefix, tid)) for prefix, tid in trees]
            stage_f = {k: (p, ex.submit(stage_preflight, args) if args else None)
                       for k, (p, args) in stage_args.items()}
            for prefix, tid, f in tree_f:
                r = f.result()
                comps[f"toolchain-tree:{tid}"] = {"path": prefix, "verify": "ok" if r.returncode == 0 else
                                                  (r.stderr.strip().splitlines() or ["failed"])[-1]}
                if r.returncode == 0 and tree_info.get(tid, {}).get("stamp"):
                    comps[f"toolchain-tree:{tid}"].update(tree_info[tid])
                if r.returncode != 0:
                    bad.append(f"toolchain {tid} at {prefix} does not match its pinned manifest: "
                               + " ".join(r.stderr.strip().splitlines()[-2:]))
            # the official exporter must start (in the sandbox it will run in)
            if not bad and self.tc:
                p = subprocess.run(self.sandbox_argv(self.tc, ro=[self.official_exporter]) + [self.official_exporter,
                                   "--help"], capture_output=True, env={}, timeout=120)
                if p.returncode not in (0, 1) or not (p.stdout or p.stderr):
                    bad.append(f"official lean4export does not start (exit {p.returncode})")
            # stage preflights
            self.available = {}
            for key in wanted:
                if key == "CS" and self._cs_deferred:
                    self.available[key] = (True, "deferred: the trusted check's own preflight runs concurrently and is "
                                                 "awaited before the check")
                    continue
                p, f = stage_f[key]
                if f is None:
                    self.available[key] = (False, "stage script not installed")
                    continue
                ok, why = f.result()
                self.available[key] = (ok, "ok" if ok else f"preflight failed: {why}")
                comps[f"stage:{key}"] = {"path": p, "sha256": sha256_file(p), "preflight": "ok" if ok else why}
        if getattr(self, "cs_pins", None):
            comps["check_pins"] = {"path": self.cs_pins, "sha256": sha256_file(self.cs_pins)}
        if getattr(self, "cs_hide", None):   # end-of-run re-hash covers the hide list too
            comps["check_hide"] = {"path": self.cs_hide, "sha256": sha256_file(self.cs_hide)}
        self.res["components"] = comps
        self.res["preflight"] = {k: v[1] for k, v in self.available.items()}
        if bad:
            raise Refuse("preflight: " + "; ".join(bad))
        # mandatory stages
        for key in ("C0", "build_official"):
            if key in self.available and not self.available[key][0]:
                raise Refuse(f"preflight: {key}: {self.available[key][1]}")
        if self.a.require_fast and not self.a.preflight_only:
            miss = [k for k, v in self.available.items() if not v[0]]
            if miss:
                raise Refuse("--require-fast: unusable fast components: " + "; ".join(
                    f"{k}: {self.available[k][1]}" for k in miss))
        self.res["stage_seconds"]["preflight"] = round(time.time() - t0, 3)

    def await_cs_preflight(self):
        """the deferred preflight of check-sound-svc.sh: its result decides whether CS runs, as before."""
        d = getattr(self, "_cs_deferred", None)
        if not d:
            return
        p, f = d
        ok, why = f.result()   # idempotent: a second caller waits for the same result
        retry = getattr(self, "_cs_deferred_retry", None)
        if not ok and retry:
            # the deferred preflight ran concurrently with prepare / build; under a tight memory cgroup its
            # self-test can fail for lack of memory (export-in under 1.6 GB, 16:35Z). Re-run it once, now that it runs
            # alone; the check itself repeats every integrity check and the self-test anyway
            self._cs_deferred_retry = None
            self.warn(f"deferred trusted-check preflight failed while the build ran ({why}); re-running it alone")
            ok, why = retry[0](retry[1])
        self.available["CS"] = (ok, "ok" if ok else f"preflight failed: {why}")
        self._cs_deferred = None   # only after the result is recorded
        with self.lock:
            self.res.setdefault("components", {})["stage:CS"] = {"path": p, "sha256": sha256_file(p),
                                                                 "preflight": "ok" if ok else why, "deferred": True}
            self.res.setdefault("preflight", {})["CS"] = self.available["CS"][1]
        self._cs_ex.shutdown(wait=False)

    @staticmethod
    def script_has_pins(rel):
        """the check script implements --pins (its text names the option)."""
        try:
            return "--pins" in open(os.path.join(ROOT, rel), encoding="utf-8", errors="replace").read()
        except OSError:
            return False

    def frontier_pins_args(self):
        """ --pins for check/frontier/check-frontier.sh, only if that script accepts it (else refuse: a 4.37
        conditional verdict must not silently use the 4.36 judge)."""
        try:
            ok = "--pins" in open(os.path.join(ROOT, FRONTIER_SCRIPT), encoding="utf-8").read()
        except OSError:
            ok = False
        if not ok:
            raise Refuse("--pins with --modulo-frontier: check/frontier/check-frontier.sh has no --pins option yet")
        return ["--pins", self.cs_pins]

    def cs_svc(self, co):
        """(sound-auto) use check/sound/check-sound-svc.sh --integrity-cache (the
        same judge, self-test and verdict mapping as check-sound.sh; the pin + 4.36 tree checks become a stamp comparison
        after one full verification) when the configured CS script is the plain check-sound.sh and the cache dir is usable."""
        d = getattr(self.a, "integrity_cache", None)
        if getattr(self, "cs_pins", None) and not self.script_has_pins(SVC_SCRIPT):
            return False
        p = os.path.join(ROOT, SVC_SCRIPT)
        return bool(d and co.get("script") == "check/sound/check-sound.sh" and os.path.isfile(p) and os.access(p, os.X_OK))

    def verify_components_end(self):
        """TOCTOU guard: the official toolchain trees and every pinned file/stage script must be unchanged at the end of
        the run (a swap during a 1-2 h run would otherwise go unnoticed). Returns a list of changes (empty = ok)."""
        changed = []
        self.await_cs_preflight()
        comps = self.res.get("components", {})
        for name, c in comps.items():
            if name.startswith("toolchain-tree:"):
                tid = name.split(":", 1)[1]
                if c.get("stamp") and tree_stamp(c["path"]) == c["stamp"]:
                    c["verify_end"] = "ok (stamp unchanged since the start-of-run verification)"
                    continue
                r = subprocess.run([PY, "-I", os.path.join(ROOT, "lib", "toolchain.py"), "verify", c["path"], tid],
                                   capture_output=True, text=True, env=self.child_env(), timeout=900)
                c["verify_end"] = "ok" if r.returncode == 0 else (r.stderr.strip().splitlines() or ["failed"])[-1]
                if r.returncode != 0:
                    changed.append(f"toolchain {tid} at {c['path']}: {c['verify_end']}")
            elif c.get("sha256") and c.get("path"):
                # a recorded component that vanished or is no longer a regular file is a CHANGE (before: the
                # isfile() guard skipped it, so a deleted / replaced-by-a-directory stage script passed the end check)
                try:
                    h = sha256_file(c["path"]) if os.path.isfile(c["path"]) else "missing or not a regular file"
                except OSError as e:
                    h = f"unreadable: {e}"
                c["sha256_end"] = h
                if h != c["sha256"]:
                    changed.append(f"{name} ({c['path']}) changed during the run ({h if len(h) != 64 else 'sha256 differs'})")
        return changed

    def _pin(self, path, want, bad):
        try:
            have = sha256_file(path)
        except OSError as e:
            bad.append(f"{path}: {e}")
            return {"path": path, "sha256": None}
        if have != want:
            bad.append(f"{path}: sha256 {have} != pinned {want}")
        return {"path": path, "sha256": have}

    # ---------------------------------------------------------------- inputs
    def read_inputs(self):
        a = self.a
        for d, what in ((a.challenge, "CHALLENGE"),) + (() if a.export else ((a.project, "PROJECT"),)):
            if not os.path.isdir(d):
                raise Refuse(f"{what} {d} is not a directory")
        cfg_src = a.comparator_config or os.path.join(a.challenge, "comparator.json")
        if not os.path.isfile(cfg_src):
            raise Refuse(f"comparator config {cfg_src} missing")
        # ONE snapshot of the challenge inputs, taken here before any decision: the comparator
        # config, challenge.export (+ its .sha256) and lean-toolchain are copied once into the run's private directory and
        # every later read (pins, release / judge selection, given-or-built, the judges' inputs) uses only the snapshot. A
        # challenge.export that appears / changes / vanishes in the caller's directory later has no effect.
        self.snap = os.path.join(self.tmp, "challenge-inputs")
        # the snapshot and its parents are private to this user: OUT without group / other write,
        # OUT/tmp and the snapshot 0700, each owned by us (verified) - no other writer can swap the pinned copies
        os.makedirs(self.snap, mode=0o700, exist_ok=True)
        for d, m in (((self.out, None),) if getattr(self, "out", None) else ()) + ((self.tmp, 0o700), (self.snap, 0o700)):
            try:
                st = os.stat(d)
                if st.st_uid != os.getuid():
                    raise Refuse(f"{d} is not owned by this user: the private snapshot cannot be protected")
                os.chmod(d, m if m is not None else (st.st_mode & 0o7777) & ~0o022)
                st = os.stat(d)
                if st.st_mode & (0o022 if m is None else 0o077):
                    raise Refuse(f"{d} keeps group / other access (mode {oct(st.st_mode & 0o777)}): refused")
            except OSError as e:
                raise Refuse(f"{d}: cannot protect the private snapshot ({e})") from e
        def snapshot(src, name):
            dst = os.path.join(self.snap, name)
            cp = subprocess.run(["cp", "--reflink=auto", "--", src, dst], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            if cp.returncode != 0 or not os.path.isfile(dst) or os.path.islink(dst):
                why = cp.stderr.decode('utf-8', 'replace').strip()[:200] or (
                    f"cp killed by signal {-cp.returncode}" if cp.returncode < 0 else f"cp exit {cp.returncode}")
                raise Refuse(f"{src}: cannot make the private snapshot ({why}; a host / resource failure, no verdict)")
            os.chmod(dst, 0o444)
            return dst
        cfgp = snapshot(cfg_src, "comparator.json")
        ce_src = os.path.join(a.challenge, "challenge.export")
        if os.path.isfile(ce_src):
            snapshot(ce_src, "challenge.export")
            if os.path.isfile(ce_src + ".sha256"):
                snapshot(ce_src + ".sha256", "challenge.export.sha256")
        if os.path.isfile(os.path.join(a.challenge, "lean-toolchain")):
            snapshot(os.path.join(a.challenge, "lean-toolchain"), "lean-toolchain")
        self.challenge_export_src = os.path.realpath(ce_src)
        if (getattr(a, "sound", False) or getattr(a, "notary", False)) and not getattr(a, "comparator_sha256", None) and \
                (getattr(a, "challenge_sha256", None) or self.given_challenge_export()):
            # comparator pin "scheme 2": with a given challenge export or --challenge-sha256, the challenge identity is
            # the PAIR (challenge export + comparator config): refuse before anything runs
            raise Refuse("sound / notary mode with --challenge-sha256 or a given challenge export needs --comparator-sha256 "
                         "HEX (the sha256 of the official comparator.json; with --challenge-sha256 it is the challenge "
                         "identity) - refused before anything runs")
        if getattr(a, "comparator_sha256", None):   # the caller's pin of the config
            got = sha256_file(cfgp)
            if got != a.comparator_sha256:
                raise Refuse(f"comparator config sha256 {got} != --comparator-sha256 {a.comparator_sha256} (the challenge "
                             "identity is the pair challenge export + comparator config)")
        try:
            cc = json.load(open(cfgp, encoding="utf-8"))
        except Exception as e:  # noqa: BLE001
            raise Refuse(f"comparator config {cfgp}: {e}") from e
        for k in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
            if k not in cc:
                raise Refuse(f"comparator config: missing {k}")
        thms = list(cc["theorem_names"])
        defs = list(cc.get("definition_names") or [])
        axs = list(cc["permitted_axioms"])
        # GOAL S1(3): a SOUND or NOTARY verdict means "derivable from propext, Quot.sound, Classical.choice";
        # only the challenge EXPORT is pinned by default (--challenge-sha256), the comparator config is read from the
        # challenge dir, so its axiom list is held to S1(3) here (a config permitting sorryAx / Lean.ofReduceBool / any
        # custom axiom would otherwise turn a sorry or a native_decide proof into ACCEPTED trust=sound). No verdict.
        # the names are compared as LEAN names (lean_name_key = the judges' / the official comparator's
        # String.toName): `«propext»` IS propext. The set is not widened: only a string whose canonical name is propext,
        # Quot.sound or Classical.choice passes; a non-string, a non-name and `«Quot.sound»` (one component) stay outside.
        s1 = {lean_name_key(n) for n in S1_PERMITTED_AXIOMS}
        if getattr(a, "sound", False) or getattr(a, "notary", False):
            bad_ax = [x for x in axs if not isinstance(x, str) or lean_name_key(x) not in s1]
            if bad_ax:
                raise Refuse(f"comparator config {cfgp}: permitted_axioms {bad_ax} outside GOAL S1(3) "
                             f"({', '.join(S1_PERMITTED_AXIOMS)}): a sound/notary verdict cannot permit them")
        # 4.36 Lake compareIt: builtinTargets ++ theoremNames ++ legalAxioms ++ primitiveTargets ++ definitionNames
        # (builtinTargets: `legalAxioms.contains ``Quot.sound` on the parsed names)
        builtin = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if lean_name_key("Quot.sound") in \
            {lean_name_key(x) for x in axs} else []
        targets = builtin + thms + axs + PRIMITIVES + defs
        tf = os.path.join(a.challenge, "export-targets.txt")
        if os.path.isfile(tf):
            # names separated by whitespace OUTSIDE «...» (one per line, or several per line as in the RH
            # challenge's file), each compared as a Lean name; every entry must be a name. Before: split() at EVERY
            # whitespace, so `Check.«space in name»` became three entries and a correct list was refused.
            given = split_lean_names(open(tf, encoding="utf-8").read())
            if given is None or any(not lean_name_key(x) for x in given) or \
                    [lean_name_key(x) for x in given] != [lean_name_key(x) for x in targets]:
                raise Refuse(f"{tf} differs from the export targets Lake's comparator derives from {cfgp}")
        # toolchain: the project's lean-toolchain (and the challenge's) must name a supported official release
        def toolchain_of(d):
            p = os.path.join(d, "lean-toolchain")
            if not os.path.isfile(p):
                raise Refuse(f"{d} has no lean-toolchain")
            return open(p, encoding="utf-8").read().strip()
        if a.export and self.given_challenge_export() and not os.path.isfile(os.path.join(self.snap, "lean-toolchain")):
            tcname = None   # judging given exports only: no toolchain is used
        elif not os.path.isfile(os.path.join(self.snap, "lean-toolchain")):
            raise Refuse(f"{a.challenge} has no lean-toolchain")
        else:
            tcname = toolchain_of(self.snap)   # the snapshot
        if not a.export:
            ptc = toolchain_of(a.project)
            if ptc != tcname:
                raise Refuse(f"project toolchain {ptc} != challenge toolchain {tcname}")
        if (getattr(a, "sound", False) or getattr(a, "notary", False)) and tcname is not None and \
                self.given_challenge_export():
            # the given challenge export is the pinned challenge identity (S1(1)); its own release decides
            # the judge. An UNPINNED lean-toolchain beside it naming another release is an inconsistent challenge: refused
            ver, _gh = self.export_release_tuple()
            if tcname != "leanprover/lean4:v" + ver:
                raise Refuse(f"the challenge's lean-toolchain says {tcname} but its challenge.export was produced by Lean "
                             f"{ver}: inconsistent challenge directory (the export's release decides the judge); refused")
        self.cc = cc
        self.targets = targets
        self.cfgp = os.path.realpath(cfgp)
        self.res["inputs"] = {
            "project": os.path.realpath(a.project) if a.project else None,
            "challenge": os.path.realpath(a.challenge),
            "comparator_config": {"path": os.path.realpath(cfg_src), "private_copy": self.cfgp,
                                  "sha256": sha256_file(self.cfgp), "content": cc,
                                  "pinned_sha256": getattr(a, "comparator_sha256", None)},
            "toolchain": tcname,
            "export_targets": targets,
            "solution_module": cc["solution_module"],
            "challenge_module": cc["challenge_module"],
        }
        if getattr(a, "comparator_sha256", None) and self.res["inputs"]["comparator_config"]["sha256"] != a.comparator_sha256:
            # the recorded sha256 is what the judge verifies its private copy against: it must be the caller's pin
            raise Refuse("comparator config changed while it was read (sha256 != --comparator-sha256)")

    # ---------------------------------------------------------------- prepare
    def prepare(self):
        t0 = time.time()
        a = self.a
        pk = a.packages
        if pk is None and os.path.isdir(os.path.join(a.challenge, ".lake", "packages")):
            pk = a.challenge
        self.packages_ws = os.path.realpath(pk) if pk else "/nonexistent"
        self.res["inputs"]["packages_workspace"] = pk and self.packages_ws
        if not a.export:
            proj = os.path.join(self.work, "proj")
            # only directories, regular files and symlinks (a FIFO/device in the project would hang or leak the copy)
            for root, dirs, files in os.walk(a.project):
                if os.path.realpath(root) == os.path.realpath(a.project) and ".lake" in dirs:
                    dirs.remove(".lake")
                for n in dirs + files:
                    st = os.lstat(os.path.join(root, n))
                    import stat as _st
                    if not (_st.S_ISDIR(st.st_mode) or _st.S_ISREG(st.st_mode) or _st.S_ISLNK(st.st_mode)):
                        raise Refuse(f"project contains a special file {os.path.join(root, n)}")
            # sources + manifest only: no shipped .lake (build artifacts, packages, config caches) - finding 066/067
            copy_project(a.project, proj)
            for root, dirs, files in os.walk(proj):
                for n in dirs + files:
                    p = os.path.join(root, n)
                    if os.path.islink(p):
                        t = os.path.realpath(p)
                        if not (t == proj or t.startswith(proj + os.sep)):
                            raise Refuse(f"project symlink {os.path.relpath(p, proj)} points outside the project")
            self.proj = proj
            src = a.project

            def digest():
                t1 = time.time()
                try:
                    dg, nf = tree_digest(src)
                except Exception as e:  # noqa: BLE001  - only the recorded digest is affected
                    dg, nf = f"error: {e}", None
                with self.lock:
                    self.res["inputs"]["project_tree"] = {
                        "sha256": dg, "files": nf, "seconds": round(time.time() - t1, 3),
                        "definition": "sha256 over sorted lines 'relpath NUL kind NUL sha256-or-link-target' of PROJECT "
                                      "without its top-level .lake (= the judged sources)"}
            self.digest_thread = threading.Thread(target=digest)
            self.digest_thread.start()
            r = subprocess.run([PY, "-I", os.path.join(ROOT, "lib", "manifest.py"), proj, self.packages_ws],
                               capture_output=True, text=True, env=self.child_env())
            if r.returncode != 0:
                raise Refuse(r.stderr.strip() or "dependencies cannot be resolved")
            self.binds = [tuple(ln.split("\t")) for ln in r.stdout.splitlines() if ln]
            self.binds_file = os.path.join(self.logdir, "binds.tsv")
            with open(self.binds_file, "w") as f:
                f.write(r.stdout)
            self.res["inputs"]["dependencies"] = [b[0] for b in self.binds]
        if not a.export:
            self.check_map_count()
        self.prepare_challenge_export()
        self.res["stage_seconds"]["prepare"] = round(time.time() - t0, 3)
        self.save()

    def check_map_count(self):
        """Host-limit guard (OFFICIAL_BUGS E5): Lean mmaps every imported .olean part (one map per part; `import Mathlib`
        alone = 52,576 maps). With too small a vm.max_map_count the official build/export fail for HOST reasons, which
        must never become a REJECTED verdict. Preflight = a NECESSARY condition (it never refuses a feasible run): a
        project whose root imports all its modules needs >= 1 map per project module (+ headroom 16384). Failures that
        still happen at run time ("failed to read file '...olean'", mmap/ENOMEM/ENOSPC...) are classified as host errors
        (ERROR, no verdict) by the build and export stages."""
        mods = 0
        for _, dns, fns in os.walk(self.proj):
            if ".lake" in dns:
                dns.remove(".lake")
            mods += sum(1 for n in fns if n.endswith(".lean"))
        need = mods + 16384
        try:
            have = int(open("/proc/sys/vm/max_map_count").read().split()[0])
        except (OSError, ValueError):
            have = None
        self.res["inputs"]["host_limits"] = {"vm.max_map_count": have, "necessary": need, "project_modules": mods}
        if have is not None and have < need:
            raise Refuse(f"host limit: vm.max_map_count = {have} < {need} (>= 1 mmap per project module + 16384 "
                         "headroom); the official build/export would fail for host reasons on this host")

    def prepare_challenge_export(self):
        a = self.a
        ce = self.given_challenge_export()   # the snapshot taken in read_inputs (None: built officially)
        info = {}
        if ce:
            sha, first = sha256_and_first_line(ce)
            if getattr(self, "selection_release", None):
                # the judge was selected from the meta line read earlier; it must be the meta line of
                # exactly the bytes whose sha256 is checked against the pin now (read in the same pass)
                try:
                    v2, g2, _f2 = _xvcheck().parse_meta_line(first)
                except Exception as e:  # noqa: BLE001
                    raise Refuse(f"{ce}: meta line unreadable at the pin check ({e})") from e
                if (v2, g2) != self.selection_release:
                    raise Refuse(f"{ce} changed during the run: the judge was selected for Lean {self.selection_release[0]} "
                                 f"but the hashed export names Lean {v2}")
            sf = ce + ".sha256"
            if os.path.isfile(sf):
                want = open(sf).read().split()[0]
                if want != sha:
                    raise Refuse(f"{ce}: sha256 {sha} != {sf} ({want})")
            info = {"path": getattr(self, "challenge_export_src", None) or os.path.realpath(ce), "private_copy": ce,
                    "source": "given", "sha256": sha, "size": os.path.getsize(ce)}
            self.challenge_export = os.path.realpath(ce)
        else:
            # build the clean challenge with the official toolchain and export it with the official exporter
            log("challenge.export missing: building it officially")
            cdir = os.path.join(self.work, "challenge")
            shutil.copytree(a.challenge, cdir, symlinks=True,
                            ignore=lambda d, names: [".lake"] if os.path.realpath(d) == os.path.realpath(a.challenge) else [])
            ws = a.challenge if os.path.isdir(os.path.join(a.challenge, ".lake", "packages")) else self.packages_ws
            lp = os.path.join(self.logdir, "challenge.lean_path")
            bp = self.stage_path("build_official")   # the challenge-build stage is a component too
            if bp:
                self.res.setdefault("components", {})["stage:challenge_build"] = {"path": bp, "sha256": sha256_file(bp)}
            rc, sec, j = self.run_stage("challenge_build", [self.stage_path("build_official"), cdir, ws, self.tc,
                                        "--targets", self.cc["challenge_module"],   # the configured module
                                        "--lean-path-out", lp, "--log", os.path.join(self.logdir, "challenge-build")],
                                        os.path.join(self.logdir, "challenge_build.log"))
            if rc != 0:
                raise Refuse(f"the clean challenge does not build officially (exit {rc})")
            out = os.path.join(self.out, "challenge.export")
            r = subprocess.run([PY, "-I", os.path.join(ROOT, "lib", "manifest.py"), cdir, ws], capture_output=True,
                               text=True, env=self.child_env())
            if r.returncode != 0:
                raise Refuse("challenge dependencies: " + r.stderr.strip())
            cbinds = [tuple(ln.split("\t")) for ln in r.stdout.splitlines() if ln]
            rc, esec = self.official_export(cdir, open(lp).read().strip(), self.cc["challenge_module"], out,
                                            os.path.join(self.logdir, "challenge_export.log"), binds=cbinds)
            if rc != 0:
                raise Refuse(f"the clean challenge cannot be exported officially (exit {rc})")
            self.challenge_export = out
            info = {"path": out, "source": "built (official lake build + official lean4export)",
                    "sha256": sha256_file(out), "size": os.path.getsize(out), "seconds": round(sec + esec, 3)}
        self.res["inputs"]["challenge_export"] = info
        if (getattr(a, "sound", False) or getattr(a, "notary", False)) and info.get("source") == "given" and not getattr(a, "challenge_sha256", None):
            # GOAL S1(1): the challenge must be THE official challenge export. A file next to the challenge (incl. its
            # .sha256) has no independent provenance, so sound mode needs the verifier's own pin (or an official build)
            raise Refuse("sound mode: a given challenge export needs --challenge-sha256 HEX (the sha256 of the official "
                         "challenge export, GOAL S1(1)); without challenge.export the challenge is built and exported "
                         "officially (B0 + E0) instead")
        if (getattr(a, "sound", False) or getattr(a, "notary", False)) and info.get("source") == "given" and \
                not getattr(a, "comparator_sha256", None):
            # re-asserted on the bytes that are judged: a given export needs the pair
            raise Refuse("sound / notary mode: a given challenge export needs --comparator-sha256 HEX as well (the challenge "
                         "identity is the pair challenge export + comparator config)")
        if getattr(a, "challenge_sha256", None) and info.get("sha256") != a.challenge_sha256:
            raise Refuse(f"challenge export sha256 {info.get('sha256')} != --challenge-sha256 {a.challenge_sha256} "
                         "(GOAL S1(1): the challenge must be the official challenge export)")

    def xversion_gate(self):
        """SOUND mode, cross-version gate (check/xversion/xvcheck.py + check/xversion/README.md): the trusted
        check judges with the Lean 4.36 judge code and kernel; the release R that produced the (pinned, official)
        challenge export must be one whose kernel built-in extensions and comparator judge code were verified equal to
        4.36's (check/xversion/releases.json), else there is no verdict; R's extra comparator rules (4.37: 'Challenge
        definition is not sorried') veto. Returns 0 (R admitted, rules hold) or 1 (REJECTED by an extra rule); raises
        Refuse (no verdict) otherwise. It can never produce an acceptance."""
        xv = os.path.join(ROOT, "check", "xversion", "xvcheck.py")
        jf = os.path.join(self.logdir, "xversion.json")
        t0 = time.time()
        if not os.path.isfile(xv):
            raise Refuse("sound mode: check/xversion/xvcheck.py missing")
        try:
            # the same switch as the judge: with --require-sorried-holes a non-sorried hole DECLINES here
            # first (before: the gate ran without it, so a later build error could turn the declined challenge REJECTED)
            rsh = ["--require-sorried-holes"] if getattr(self.a, "require_sorried_holes", False) else []
            p = subprocess.run([PY, "-I", xv, self.challenge_export, self.cfgp, "--json", jf] + rsh, capture_output=True,
                               text=True, env=self.child_env(), timeout=3600)
            rc = p.returncode
        except subprocess.TimeoutExpired:
            rc = 2
        try:
            j = json.load(open(jf))
        except (OSError, ValueError):
            j = {"verdict": "DECLINED", "reason": "cross-version gate: no result"}
        j["seconds"] = round(time.time() - t0, 3)
        j["script_sha256"] = sha256_file(xv)
        self.res["inputs"]["challenge_export"]["xversion"] = j
        self.save()
        if rc == 0:
            return 0
        if rc == 1 and j.get("verdict") == "REJECTED":
            return 1
        raise Refuse("sound mode: " + str(j.get("reason") or f"cross-version gate exit {rc}"))

    def notary_scope_gate(self):
        """NOTARY preset: the v0.1 kernel-scope decision of the notary stage
        (check/notary/check-notary.sh --scope-check, on its own private copies with both identity pins) runs BEFORE the
        cross-version gate and the solution build: a challenge outside the notary's v0.1 scope gives no verdict whatever
        the candidate is (a build failure can no longer report REJECTED first). Only SCOPE_OK (exit 0) continues; DECLINED,
        a crash or a timeout raises Refuse. A notary stage WITHOUT --scope-check (an older stage) falls
        through unchanged (today's behaviour), recorded as notary_scope.skipped; the stage re-checks the scope itself."""
        cn = os.path.join(ROOT, "check", "notary", "check-notary.sh")
        try:
            knows = "--scope-check" in open(cn, encoding="utf-8", errors="replace").read()
        except OSError as e:   # a missing / unreadable checker is no "older checker": no verdict
            raise Refuse(f"notary mode: the notary stage {cn} is not usable ({e})") from e
        if not knows:
            self.res["notary_scope"] = {"skipped": "check-notary.sh has no --scope-check (older notary stage): unchanged behaviour"}
            return
        ins = self.res.get("inputs") or {}
        ce_sha = (ins.get("challenge_export") or {}).get("sha256")
        cfg_sha = (ins.get("comparator_config") or {}).get("sha256")
        argv = [cn, "--scope-check", self.challenge_export, self.cfgp]
        if getattr(self.a, "notary_kernels", None):   # a bad selection refuses before the build too
            argv += ["--kernels", self.a.notary_kernels]
        if ce_sha:
            argv += ["--challenge-sha256", ce_sha]
        if cfg_sha:
            argv += ["--comparator-sha256", cfg_sha]
        t0 = time.time()
        try:
            p = subprocess.run(argv, capture_output=True, text=True, env=self.child_env(), timeout=3600)
            rc, out = p.returncode, p.stdout
        except (OSError, subprocess.TimeoutExpired) as e:
            rc, out = 2, '{"verdict": "DECLINED", "reason": "scope check did not finish: %s"}' % str(e)[:200]
        try:
            j = json.loads((out.strip().splitlines() or ["{}"])[-1])
        except ValueError:
            j = {}
        if not isinstance(j, dict):
            j = {}
        self.res["notary_scope"] = {"verdict": j.get("verdict"), "reason": j.get("reason"), "exit": rc,
                                    "seconds": round(time.time() - t0, 3)}
        self.save()
        if rc == 0 and j.get("verdict") == "SCOPE_OK" and j.get("exit") == 0:
            return
        raise Refuse("notary mode: " + str(j.get("reason") or f"notary scope check exit {rc}"))

    def export_absence(self):
        """the reason if the official exporter failed because the SUBMISSION lacks what it must
        provide - the solution module's .olean after the build, or one of the export targets - after a successful EXACT
        build (B0 / B1: official lean, Lake's plan; a transformed build B3 could itself have omitted it -> None). Only the
        exporter's own messages naming exactly the solution module / a target count; anything else -> None (no verdict)."""
        b = self.res.get("build") or {}
        if b.get("option") not in ("B0", "B1") or b.get("exit") != 0:
            return None
        try:
            err = open(os.path.join(self.logdir, "export_official.log"), encoding="utf-8", errors="replace").read()[-200000:]
        except OSError:
            return None
        import re as _re
        mod = self.cc.get("solution_module") or ""
        if mod and (_re.search(r"object file \S+ of module " + _re.escape(mod) + r" does not exist", err) or
                    _re.search(r"unknown module prefix '" + _re.escape(mod.split(".")[0]) + r"'", err)):
            # B0 / B1 build the DEFAULT targets, while the official comparator runs
            # `lake build <solution_module>`: a module that HAS a source file in the project may simply not be a default
            # target (the official flow would build it) -> no verdict. REJECTED only when the project has no source file
            # for the module at all (then `lake build <module>` fails too).
            rel = os.path.join(*mod.split(".")) + ".lean"
            for root, dirs, files in os.walk(self.proj):
                dirs[:] = [d for d in dirs if d != ".lake"]
                if os.path.basename(rel) in files and os.path.join(root, os.path.basename(rel)).endswith(os.sep + rel):
                    return None
            return (f"the project has no source for the solution module {mod} (no {rel}); the official comparator's "
                    f"`lake build {mod}` fails too")
        for ln in err.splitlines():
            # only lean4export's own unknown-constant / not-found message for a target
            m = _re.search(r"(?:unknown constant '([^']+)'|[Cc]onstant (\S+) not found in environment)", ln)
            name = m and (m.group(1) or m.group(2))
            if name and name in set(self.targets or []):
                return f"the target {name} is not declared by the project (the official comparator fails too)"
        return None

    def official_export(self, proj, lean_path, module, out, logfile, binds=()):
        """Official lean4export in the sandbox (LEAN_ABORT_ON_PANIC=1 as in 4.36 `lake comparator`); stdout -> a regular
        file opened here.  Returns (exit, seconds)."""
        t0 = time.time()
        ro = [proj, self.official_exporter]
        argv = self.sandbox_argv(self.tc, ro=ro, env={"LEAN_PATH": lean_path, "LEAN_ABORT_ON_PANIC": "1"},
                                 chdir=proj, binds=binds) + [self.official_exporter, module, "--"] + self.targets
        with open(out, "wb") as f, open(logfile, "ab") as lf:
            lf.write(f"[{now_iso()}] $ {' '.join(argv)}\n".encode())
            p = run_child(argv, stdout=f, stderr=subprocess.PIPE, env={})
            lf.write(p.stderr)
        rc = p.returncode if p.returncode >= 0 else 128 - p.returncode
        if rc != 0:
            import re
            # 4.36 `lake comparator` semantics: any exporter failure is a rejection - except host/resource failures
            # and kills from outside (SIGKILL/SIGTERM), which give no verdict
            if rc in (137, 143) or re.search(HOST_ERROR_RE, p.stderr.decode("utf-8", "replace")):
                rc = 2
            else:
                rc = 1
        return rc, round(time.time() - t0, 3)

    # ---------------------------------------------------------------- overlap (orchestration only)
    def overlap_start(self):
        """Start the incremental Lean-kernel leg and the snapshot driver (sound mode, CS selected, --overlap)."""
        a = self.a
        targeted = getattr(a, "overlap_targeted", False) or bool(getattr(a, "overlap_targets", None))
        if not ((getattr(a, "overlap", False) or targeted) and a.sound and getattr(self, "overlap_dir", None) is None):
            return
        co = self.cfg.get("check_options", {}).get("CS", {})
        pins = os.path.join(ROOT, os.path.dirname(co.get("script", "check/sound/check-sound.sh")), "pins.env")
        if getattr(self, "cs_pins", None):   # the selected pins decide the overlap leg too
            pins = self.cs_pins
        plc = exp = None
        for ln in open(pins):
            f = ln.split()
            if len(f) >= 4 and f[0] == "PIN" and f[1] == "pleanchecker_incr":
                plc = (f[3], f[2])
            if len(f) >= 4 and f[0] == "PIN" and f[1] == "snapshot_exporter":
                exp = (f[3], f[2])
        if not plc or not exp or sha256_file(plc[0]) != plc[1] or sha256_file(exp[0]) != exp[1]:
            self.warn("overlap: pleanchecker_incr / snapshot_exporter not pinned or sha256 mismatch -> no overlap")
            return
        targets = None
        if targeted:
            targets = os.path.join(ROOT, os.path.dirname(co.get("script", "check/sound/check-sound.sh")), "hints",
                                   "default.txt")
            if getattr(a, "overlap_targets", None):
                targets = os.path.join(ROOT, a.overlap_targets)
            elif os.path.isfile(os.path.join(ROOT, "overlap", "targets-top40.txt")):
                targets = os.path.join(ROOT, "overlap", "targets-top40.txt")   # the measured default (run 6)
            if not os.path.isfile(targets):
                self.warn("overlap: --overlap-targeted but no hint list " + targets + " -> no overlap")
                return
        d = os.path.join(self.out, "incr")
        sd = os.path.join(self.out, "snapshots")
        os.makedirs(d, exist_ok=True)
        os.makedirs(sd, exist_ok=True)
        self.overlap_dir = d
        self.overlap_server = subprocess.Popen([os.path.join(ROOT, "overlap", "incr-server.sh"), d, plc[0],
                                                str(a.threads)] + ([targets] if targets else []), start_new_session=True, stdin=subprocess.DEVNULL,
                                               stdout=subprocess.DEVNULL, stderr=open(os.path.join(d, "launcher.log"), "wb"))
        self.overlap_driver = subprocess.Popen(
            ["/usr/bin/python3", "-I", os.path.join(ROOT, "overlap", "snapdriver.py"),
             "--log", os.path.join(self.logdir, "build-fast"), "--proj", self.proj, "--toolchain", self.tc,
             "--binds", self.binds_file, "--exporter", exp[0], "--incr-dir", d, "--snap-dir", sd,
             "--threads", str(min(a.threads, 8 if targets else 128)), "--server-log", os.path.join(d, "server.log")]
            + (["--targets", targets] if targets else []),
            start_new_session=True, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
            stderr=open(os.path.join(sd, "driver.log"), "wb"))
        with CHILDREN_LOCK:
            CHILDREN.add(self.overlap_server)
            CHILDREN.add(self.overlap_driver)
        self.res["overlap"] = {"dir": d, "snapshots": sd, "started": now_iso(), "mode": "targeted" if targets else "full"}
        log(f"overlap: incremental Lean-kernel leg + snapshot driver started ({d})")

    def overlap_stop_driver(self):
        p = getattr(self, "overlap_driver", None)
        if p is not None and p.poll() is None:
            kill_tree(p)   # the driver and a running snapshot export: never compete with the final export
            try:
                p.wait(timeout=30)
            except subprocess.TimeoutExpired:
                import signal
                os.killpg(p.pid, signal.SIGKILL)
        if p is not None:
            self.res.setdefault("overlap", {})["driver_stopped"] = now_iso()

    def overlap_kill(self):
        self.overlap_stop_driver()
        p = getattr(self, "overlap_server", None)
        if p is not None and p.poll() is None:
            kill_tree(p)
            try:
                p.wait(timeout=30)
            except subprocess.TimeoutExpired:
                pass
        if p is not None:
            try:
                tail = open(os.path.join(self.overlap_dir, "server.log"), errors="replace").read().splitlines()
                self.res.setdefault("overlap", {})["server_log_tail"] = [ln for ln in tail if ln.startswith("[incr]")][-12:]
            except OSError:
                pass
            for src, dst in ((os.path.join(self.overlap_dir, "server.log"), "overlap-server.log"),
                             (os.path.join(self.res.get("overlap", {}).get("snapshots") or self.overlap_dir, "driver.log"),
                              "overlap-driver.log")):
                try:
                    shutil.copyfile(src, os.path.join(self.logdir, dst))
                except OSError:
                    pass
            if not self.a.keep_work:   # the snapshot exports (tens of GB on big projects) are only inputs of the server
                sd = self.res.get("overlap", {}).get("snapshots")
                if sd:
                    for fn in os.listdir(sd):
                        if fn.endswith(".export") or fn.endswith(".export.part"):
                            try:
                                os.unlink(os.path.join(sd, fn))
                            except OSError:
                                pass

    # ---------------------------------------------------------------- build
    def build(self):
        a = self.a
        lp = os.path.join(self.logdir, "lean_path.txt")
        common = ["--threads", str(a.threads), "--lean-path-out", lp]
        # private cache of untrusted build helpers (build/bcache.py): fast builds only (official-build.sh takes none)
        bcache = ["--build-cache", a.build_cache] if getattr(a, "build_cache", None) else []
        b = {"attempts": []}
        rc = None
        if a.build != "B0":
            ok, why = self.available.get("build_fast", (False, "not requested"))
            if ok:
                variant = [] if a.build == "B1" else ["--preset", a.build]
                if a.build == "B3" and a.unsafe_build:
                    # closure-only: the module is the comparator's solution module
                    variant += ["--unsafe", ",".join(f"closure-only={self.cc['solution_module']}" if u == "closure-only"
                                                     else u for u in a.unsafe_build)]
                self.overlap_start()
                rc, sec, j = self.run_stage("build_fast", [self.stage_path("build_fast"), self.proj, self.packages_ws,
                                            self.tc, "--log", os.path.join(self.logdir, "build-fast"),
                                            "--require-modules", self.cc["solution_module"]] + variant
                                            + common + bcache, os.path.join(self.logdir, "build_fast.log"))
                b["attempts"].append({"mode": "fast", "option": a.build, "exit": rc, "seconds": sec, "stage": j})
                if rc == 2:
                    self.warn("fast build declined -> official lake build")
                elif rc == 1 and a.confirm_build_failure:
                    self.warn("fast build failed -> confirming with the official lake build (no false rejects)")
                elif rc not in (0, 1):
                    self.warn(f"fast build exit {rc} -> official lake build")
                    rc = 2
            else:
                self.warn(f"fast build unavailable ({why}) -> official lake build")
        cbf = a.confirm_build_failure
        # DISABLED: the 'exact retry' re-ran a failing module against the TRANSFORMED build's .olean files
        # (e.g. premise-off helpers), so it confirmed nothing: a valid `grind +suggestions` project was REJECTED. A failure
        # of the transformed build B3 now always goes to the exact rebuild B1 below (as --preset sound), whose own failure
        # is the confirmed one. (`False and` keeps the hunk minimal.)
        if False and (a.sound and a.build == "B3" and rc == 1 and cbf and getattr(a, "confirm_failure", None) == "exact-retry"
                and not getattr(a, "confirm_build_failure_full", False) and "retries" in a.unsafe_build
                and not any(u.split("=", 1)[0] == "merge" for u in a.unsafe_build)):
            fm = exact_retry_failures(os.path.join(self.logdir, "build-fast", "sched.out"))
            if fm:   # (sound-auto) every failing module also failed with its exact official invocation
                b["confirmed_by"] = "exact-retry"
                b["failed_modules"] = fm
                cbf = False
                self.warn("the failing module(s) also fail with their exact official invocation -> REJECTED without a full "
                          "exact rebuild (sound-auto; --confirm-build-failure-full forces one)")
        if a.sound and a.build == "B3" and rc != 0 and not (rc == 1 and not cbf) \
                and not a.no_build_fallback and self.available.get("build_fast", (False,))[0]:
            # SOUND mode: the transformed build is untrusted anyway, so a decline/failure of it is retried with the exact
            # official invocations (B1: official lean, Lake's plan) - availability only, never a verdict by itself
            self.warn(f"sound mode: transformed build (B3) exit {rc} -> exact build B1 (official binaries)")
            rmtree_force(self.proj)
            copy_project(self.a.project, self.proj)
            rc, sec, j = self.run_stage("build_fast_b1", [self.stage_path("build_fast"), self.proj, self.packages_ws,
                                        self.tc, "--log", os.path.join(self.logdir, "build-fast-b1"),
                                        "--require-modules", self.cc["solution_module"]] + common + bcache,
                                        os.path.join(self.logdir, "build_fast_b1.log"))
            b["attempts"].append({"mode": "fast", "option": "B1", "exit": rc, "seconds": sec, "stage": j})
            if rc not in (0, 1, 2):
                rc = 2
        # sound mode: if the exact build B1 (official lean, Lake's plan) failed, the official build fails too -> REJECTED
        # without a third build (README 1b; the former 'pass' fell through to the official lake build)
        b1_failed = a.sound and b["attempts"] and b["attempts"][-1]["option"] == "B1" and rc == 1
        if rc != 0 and not (rc == 1 and not cbf) and not b1_failed:
            sound_unavail = (a.sound and a.build == "B3" and not a.no_build_fallback and not b["attempts"]
                             and not self.available.get("build_fast", (False,))[0])
            if (a.no_build_fallback or a.build == "B3") and a.build != "B0" and not (
                    a.sound and b["attempts"] and b["attempts"][-1]["option"] == "B1") and not sound_unavail:
                # an UNSAFE request never turns silently into the official build. SOUND mode: the build is
                # untrusted, so a fast build that is UNAVAILABLE for this project (its preflight fails, e.g. the planner
                # does not compile against another Lean release's Lake) goes to the official build B0 exactly like a fast
                # build that DECLINES at run time (B3 -> B1 -> B0 above); only --no-build-fallback keeps the ERROR
                self.res["build"] = dict(b, exit=2, mode="fast", seconds=round(sum(x["seconds"] for x in
                                                                                   b["attempts"]), 3))
                raise Refuse(f"fast build {'declined' if rc == 2 else 'unavailable' if rc is None else 'failed'} "
                             "and the official lake build fallback is disabled (--no-build-fallback)")
            # official path: fresh copy of the prepared sources (the fast build may have written into PROJ)
            if rc is not None:
                rmtree_force(self.proj)
                copy_project(self.a.project, self.proj)
            rc, sec, j = self.run_stage("build_official", [self.stage_path("build_official"), self.proj,
                                        self.packages_ws, self.tc, "--log", os.path.join(self.logdir, "build-official"),
                                        # `lake build MOD` exactly as the official comparator
                                        "--targets", self.cc["solution_module"]]
                                        + common, os.path.join(self.logdir, "build_official.log"))
            b["attempts"].append({"mode": "official", "option": "B0", "exit": rc, "seconds": sec, "stage": j})
        last = b["attempts"][-1]
        if rc == 1 and (a.sound or getattr(a, "notary", False)) and last.get("option") == "B3":   # notary too
            # a failure of the TRANSFORMED build that no exact build confirmed (--no-confirm-build-failure)
            # is not a judgement of the proof: no verdict (REJECTED only after B1 / B0 confirms)
            self.warn("sound mode: the transformed build B3 failed and no exact build confirmed it (--no-confirm-build-failure) "
                      "-> no verdict")
            last["unconfirmed"] = True
            rc = 2
        if rc == 1:   # a build stopped by a signal / resource limit / host error is no verdict
            # the LOGS of the attempt that failed (never the helper-source snapshots kept beside them)
            lg = {"official": ("build_official.log", "build-official/build.log")}.get(last.get("mode")) or (
                ("build_fast_b1.log", "build-fast-b1/sched.out", "build-fast-b1/build.log")
                if len(b["attempts"]) > 1 and last.get("option") == "B1" and b["attempts"][0].get("option") != "B1"
                else ("build_fast.log", "build-fast/sched.out", "build-fast/build.log"))
            res_why = resource_failure_evidence([os.path.join(self.logdir, f) for f in lg])
            if res_why:
                self.warn(f"build stage {last['option']} failed under a host / resource condition ({res_why}) -> no verdict")
                last["host_failure"] = res_why
                rc = 2
        if rc == 1:   # 'the build failed' (REJECTED) only from a stage whose report says exit 1 too
            why = self.stage_report_problem(1, last.get("stage"))
            if why:
                self.warn(f"build stage {last['option']}: {why} -> no verdict")
                last["report_error"] = why
                rc = 2
        b.update({"exit": rc, "mode": last["mode"], "option": last["option"],
                  "seconds": round(sum(x["seconds"] for x in b["attempts"]), 3)})
        self.res["build"] = b
        self.res["stage_seconds"]["build"] = b["seconds"]
        self.overlap_stop_driver()
        self.save()
        if rc == 0:
            self.lean_path = open(lp).read().strip()
            if not self.lean_path:
                raise Refuse("build reported success but no LEAN_PATH")
        return rc

    # ---------------------------------------------------------------- export
    def export(self):
        a = self.a
        out = os.path.join(self.out, "solution.export")
        if getattr(a, "export_dir", None):
            # the export is an UNTRUSTED intermediate; writing its ~60 GB into one ext4 file is bound by page-cache
            # insertion (E1 37.6 s on a local ext4 disk vs 26.4 s on tmpfs). Only used if the directory has >= 256 GB free.
            try:
                st = os.statvfs(a.export_dir)
                free = st.f_bavail * st.f_frsize
            except OSError:
                free = 0
            budget = memory_budget_bytes()
            if free >= 256 << 30 and is_tmpfs(a.export_dir) and budget is not None and budget < TMPFS_EXPORT_MIN_BUDGET:
                # tmpfs pages are RAM charged to the memory cgroup and cannot be reclaimed while the
                # trusted check runs next to them: below the budget the export goes to OUT (disk) instead
                self.warn(f"--export-dir {a.export_dir} is a tmpfs and the memory budget is {budget >> 30} GB < "
                          f"{TMPFS_EXPORT_MIN_BUDGET >> 30} GB -> export in OUT (observed: OOM of the check next to a 62 GB "
                          "tmpfs export in a 256 GiB cgroup)")
            elif free >= 256 << 30:
                self.export_tmpdir = tempfile.mkdtemp(prefix="fastverify-export.", dir=a.export_dir)
                out = os.path.join(self.export_tmpdir, "solution.export")
                os.symlink(out, os.path.join(self.out, "solution.export"))
            else:
                self.warn(f"--export-dir {a.export_dir}: less than 256 GB free -> export in OUT")
        e = {"path": out, "attempts": []}
        tf = os.path.join(self.logdir, "export-targets.txt")
        with open(tf, "w") as f:   # one name per line, verbatim (names may contain spaces: «a b»)
            f.write("\n".join(self.targets) + "\n")
        rc = None
        ok, why = self.available.get("export", (False, "not requested"))
        if a.export_opt == "E0":
            ok, why = False, "E0 selected"
        if ok:
            eargs = ["--lean-path", self.lean_path, "--module", self.cc["solution_module"], "--targets-nl", tf,
                     "--toolchain", self.tc, "--project", self.proj, "--binds", self.binds_file, "--out", out,
                     "--threads", str(min(a.threads, E1_MAX_THREADS_TMPFS if getattr(self, "export_tmpdir", None)
                                          else E1_MAX_THREADS))]
            # (sound-auto) the byte-identical low-memory exporter (untrusted like E1): first when the memory budget is
            # small ("prefer"), else as the fallback of a failed / killed E1 before the official exporter ("fallback")
            lowmode = getattr(a, "export_lowmem", None)
            lows = os.path.join(ROOT, "export", "export-lowmem.sh")
            lowok = lowmode in ("prefer", "fallback") and os.path.isfile(lows) and os.access(lows, os.X_OK)
            order = ["lowmem", "E1"] if (lowok and lowmode == "prefer") else (["E1", "lowmem"] if lowok else ["E1"])
            for kind in order:
                if kind == "lowmem":
                    self.res.setdefault("components", {})["stage:export_lowmem"] = {"path": lows, "sha256": sha256_file(lows)}
                rc, sec, j = self.run_stage("export" if kind == "E1" else "export_lowmem",
                                            [self.stage_path("export") if kind == "E1" else lows] + eargs,
                                            os.path.join(self.logdir, "export.log" if kind == "E1" else "export_lowmem.log"))
                e["attempts"].append({"mode": "fast", "option": "E1" if kind == "E1" else "E1-lowmem", "exit": rc,
                                      "seconds": sec, "stage": j})
                if rc == 0:
                    break
                if os.path.lexists(out):
                    os.chmod(out, 0o644)
                    os.unlink(out)
            if rc != 0:   # only a complete native export is used; anything else -> the official exporter decides
                self.warn(f"fast export stage exit {rc} -> official lean4export")
        elif a.export_opt == "E1":
            self.warn(f"fast export stage unavailable ({why}) -> official lean4export")
        if rc != 0:
            rc, sec = self.official_export(self.proj, self.lean_path, self.cc["solution_module"], out,
                                           os.path.join(self.logdir, "export_official.log"), binds=self.binds)
            e["attempts"].append({"mode": "official", "option": "E0", "exit": rc, "seconds": sec})
        e.update({"exit": rc, "mode": e["attempts"][-1]["mode"], "option": e["attempts"][-1]["option"],
                  "seconds": round(sum(x["seconds"] for x in e["attempts"]), 3)})
        if rc == 0:
            os.chmod(out, 0o444)   # the checks and the hash must all see the same bytes
            e["size"] = os.path.getsize(out)   # sha256: computed beside the checks (hash_in_background)
        self.res["export"] = e
        self.res["stage_seconds"]["export"] = e["seconds"]
        self.save()
        return rc

    # ---------------------------------------------------------------- checks
    def check(self, opt, export):
        name = CHECK_OPTS[opt][0]
        if opt == "CS":
            self.await_cs_preflight()
        co = self.cfg.get("check_options", {}).get(opt, {})
        ok, why = self.available.get(opt, (False, "not requested"))
        if not ok:
            r = {"option": opt, "exit": 2, "verdict": "NOT_RUN", "detail": why, "seconds": 0}
        else:
            frontier = opt == "CS" and getattr(self.a, "modulo_frontier", None)
            if frontier:   # check/frontier/check-frontier.sh = untrusted preparation + the UNCHANGED check-sound.sh x2
                co = dict(co, script=FRONTIER_SCRIPT)
            thr = self.a.threads
            lowmem_args = []
            ctf = getattr(self.a, "autotune_check_threads", None)
            if ctf and opt == "CS":   # sound-auto (untrusted orchestration): thread count of the trusted check by export size
                try:
                    thr = ctf(os.path.getsize(export), thr)
                    self.res.setdefault("autotune", {})["check_threads"] = thr
                except (OSError, TypeError, ValueError):
                    thr = self.a.threads
            cpf = getattr(self.a, "autotune_check_plan", None)
            lm_pins = None   # the low-memory check's own pins file for the selected release (same name)
            if getattr(self, "cs_pins", None):
                lm_pins = os.path.join(ROOT, "check", "lowmem", os.path.basename(self.cs_pins))
                if not (os.path.isfile(lm_pins) and self.script_has_pins("check/lowmem/check-sound-lowmem.sh")):
                    lm_pins = None
            if cpf and opt == "CS" and not frontier and getattr(self, "cs_pins", None) and not lm_pins:
                self.res.setdefault("autotune", {})["check_plan"] = {"lowmem": False, "why": "pins file selected: no "
                                                                     "low-memory check with --pins for it (check/lowmem/"
                                                                     + os.path.basename(self.cs_pins) + ")"}
                cpf = None
            if cpf and opt == "CS" and getattr(self.a, "require_kernel", None):   # a required extra
                # kernel runs only in check-sound(-svc).sh: never trade it for the low-memory check
                self.res.setdefault("autotune", {})["check_plan"] = {"lowmem": False, "why": "--require-kernel "
                                                                     + ",".join(self.a.require_kernel) + ": the normal "
                                                                     "check (the low-memory check has no extra kernels)"}
                cpf = None
            if cpf and opt == "CS" and not frontier:   # which reviewed trusted check fits the memory budget
                try:
                    plan = cpf(os.path.getsize(export), thr, ROOT)
                except (OSError, TypeError, ValueError):
                    plan = None
                if isinstance(plan, dict):
                    self.res.setdefault("autotune", {})["check_plan"] = plan
                    if plan.get("lowmem") and plan.get("script"):
                        co = dict(co, script=plan["script"])
                        thr = plan.get("threads") or thr
                        lp = os.path.join(ROOT, plan["script"])   # end-of-run TOCTOU check covers this script too
                        self.res.setdefault("components", {})["stage:CS_lowmem"] = {"path": lp, "sha256": sha256_file(lp)}
                        if plan.get("mem_budget_mb"):
                            lowmem_args = ["--mem-budget-mb", str(int(plan["mem_budget_mb"]))]
                        if getattr(self.a, "integrity_cache", None):   # reviewed option of the low-memory script
                            lowmem_args += ["--integrity-cache", self.a.integrity_cache]
                        if lm_pins:   # only reached when the script accepts --pins and the sibling exists
                            lowmem_args += ["--pins", lm_pins]
                            self.res.setdefault("components", {})["check_pins_lowmem"] = {"path": lm_pins,
                                                                                          "sha256": sha256_file(lm_pins)}
            if frontier and getattr(self, "cs_pins", None):   # as in preflight
                co = dict(co, args=list(co.get("args", [])) + self.frontier_pins_args())
            if frontier and getattr(self.a, "integrity_cache", None) and (not getattr(self, "cs_pins", None) or
                                                                          self.script_has_pins(SVC_SCRIPT)):
                co = dict(co, args=list(co.get("args", [])) + ["--integrity-cache", self.a.integrity_cache])
            elif opt == "CS" and getattr(self, "cs_pins", None) and \
                    co.get("script") == "check/sound/check-sound.sh":   # check-sound(-svc).sh v2.1 --pins
                co = dict(co, args=list(co.get("args", [])) + ["--pins", self.cs_pins])
            if opt == "CS" and not frontier and self.cs_svc(co):   # as in preflight (not with the low-memory
                # check: cs_svc needs the configured plain script); the end-of-run check covers this script
                co = dict(co, script=SVC_SCRIPT, args=list(co.get("args", [])) + ["--integrity-cache",
                                                                                   self.a.integrity_cache])
            argv = [os.path.join(ROOT, co["script"]), export, self.challenge_export, self.cfgp, "--threads",
                    str(thr)] + list(co.get("args", [])) + lowmem_args
            if frontier and self.a.modulo_frontier != "auto":
                argv += ["--allowed", self.a.modulo_frontier]
            if frontier and getattr(self.a, "frontier_pin", None):
                argv += ["--pinned", self.a.frontier_pin]
            if frontier and getattr(self.a, "frontier_base", None):
                argv += ["--base", self.a.frontier_base]
            for u in self.a.unsafe_check:
                if opt in UNSAFE_CHECK_OPTS[u][0]:
                    argv += UNSAFE_CHECK_OPTS[u][1]
            if opt == "CS":
                # check-sound v2: the export the orchestrator judges is PRIVATE - written by the package's own sandboxed
                # exporter (exited) into OUT / --export-dir, or (export-in) the private copy made into OUT above - so
                # assert it: an export > 4 GiB is then hard-linked instead of copied a second time by the check
                argv += ["--private-inputs"]
            if opt == "CN":
                argv += ["--private-inputs"]
                if getattr(self.a, "notary_kernels", None):
                    argv += ["--kernels", self.a.notary_kernels]
            if opt in ("CS", "CN"):   # the judge verifies the pins on its OWN private copies (no window between this
                # process's sha check at the start of the run and the judge's copy); only scripts that implement the options
                try:
                    knows_pins = "--challenge-sha256)" in open(argv[0], encoding="utf-8", errors="replace").read()
                except OSError:
                    knows_pins = False
                if not knows_pins:   # never run a trusted check without the identity pins
                    raise Refuse(f"{os.path.basename(argv[0])} does not take --challenge-sha256 / --comparator-sha256: a "
                                 "sound / notary check needs the judge to verify the challenge identity itself")
                if knows_pins:
                    ins = self.res.get("inputs") or {}
                    ce_sha = (ins.get("challenge_export") or {}).get("sha256")
                    cfg_sha = (ins.get("comparator_config") or {}).get("sha256")
                    if ce_sha:
                        argv += ["--challenge-sha256", ce_sha]
                    if cfg_sha:
                        argv += ["--comparator-sha256", cfg_sha]
            if opt in ("CS", "CN"):   # --require-sorried-holes switch, recorded in result.json
                rsh = bool(getattr(self.a, "require_sorried_holes", False))
                self.res["require_sorried_holes"] = rsh
                if rsh:
                    try:
                        knows_rsh = "--require-sorried-holes)" in open(argv[0], encoding="utf-8", errors="replace").read()
                    except OSError:
                        knows_rsh = False
                    if not knows_rsh:
                        raise Refuse(f"--require-sorried-holes: the judge {argv[0]} does not implement the switch")
                    argv += ["--require-sorried-holes"]
            if opt == "CS" and getattr(self, "overlap_dir", None):
                argv += ["--incr-dir", self.overlap_dir]
            if opt == "CS":   # veto-only extra kernels of check-sound(-svc).sh v2.3-H
                xk_args = [x for k in getattr(self.a, "extra_kernel", []) for x in ("--kernel", k)] + \
                    [x for k in getattr(self.a, "require_kernel", []) for x in ("--require-kernel", k)] + \
                    [x for k in getattr(self.a, "skip_extra_kernel", []) for x in ("--skip-kernel", k)]
                base = os.path.basename(argv[0])
                if base in ("check-sound.sh", "check-sound-svc.sh") and not frontier:
                    try:
                        has_xk = "--require-kernel" in open(argv[0], encoding="utf-8", errors="replace").read()
                    except OSError:
                        has_xk = False
                    if xk_args and not has_xk:
                        if getattr(self.a, "require_kernel", None):
                            raise Refuse(f"--require-kernel: {base} has no extra kernels (check-sound v2.3-H needed)")
                        self.warn(f"{base} has no extra kernels: --extra-kernel/--skip-extra-kernel ignored")
                    elif xk_args:
                        argv += xk_args
                else:   # the low-memory check runs the two-kernel judge only; check-frontier.sh runs check-sound(-svc).sh
                    # twice with its DEFAULT extra kernels (both opt-in unless the default switch is flipped) and passes no
                    # options through (--require-kernel disables the low-memory plan and is refused with --modulo-frontier)
                    if frontier:
                        self.res["extra_kernels"] = ("default only: %s runs check-sound twice with its default extra kernels "
                                                     "(none unless check-sound.sh's default switch is on); --extra-kernel is "
                                                     "not passed through" % base)
                    else:
                        self.res["extra_kernels"] = ("%s - the memory budget selected %s (the sequential low-memory check: "
                                                     "two-kernel judge, no extra kernels)" % (
                                                         "con-leche/nanoda: skipped (memory)" if xk_args else "none", base))
                    if getattr(self.a, "require_kernel", None):   # a requirement is never dropped silently
                        raise Refuse(f"--require-kernel: {base} cannot run the extra kernels")
                    if xk_args:
                        self.warn(f"{base} has no extra kernels: --extra-kernel/--skip-extra-kernel ignored")
            if opt == "CS" and getattr(self, "cs_hide", None):   # only scripts that implement --hide get it
                try:
                    has_hide = "--hide" in open(argv[0], encoding="utf-8", errors="replace").read()
                except OSError:
                    has_hide = False
                if has_hide:
                    argv += ["--hide", self.cs_hide]
                else:
                    self.warn(f"{os.path.basename(argv[0])} has no --hide: the hide list is not used (availability only)")
            if opt == "CS" and getattr(self.a, "check_hints", None):   # replay scheduling hints, order only
                h = self.a.check_hints
                if h != "none":
                    h = os.path.realpath(h)
                    if not os.path.isfile(h):
                        raise Refuse(f"--check-hints {self.a.check_hints}: not a file")
                    self.res.setdefault("components", {})["check_hints"] = {"path": h, "sha256": sha256_file(h)}
                argv += ["--hints", h]
            if opt == "C0" and self.a.official_timeout:
                argv += ["--timeout", str(self.a.official_timeout)]
            log(f"check {name} started")
            rc, sec, j = self.run_stage(name, argv, os.path.join(self.logdir, f"check_{name}.log"))
            verdict = {0: "ACCEPTED", 1: "REJECTED"}.get(rc, "DECLINED" if rc == 2 else "ERROR")
            if frontier and rc == 3:
                verdict = "CONDITIONAL"
            # a verdict needs the check's own report, agreeing with its exit status (every check, every
            # preset): a missing / unreadable / malformed / inconsistent report is ERROR, never ACCEPTED (or REJECTED)
            report_bad = self.stage_report_problem(rc, j, verdict) if verdict in ("ACCEPTED", "REJECTED", "CONDITIONAL") \
                else None
            if report_bad:
                verdict = "ERROR"
            r = {"option": opt, "exit": 2 if report_bad else (rc if rc in ((0, 1, 2, 3) if frontier else (0, 1, 2)) else 2),
                 "raw_exit": rc, "verdict": verdict, "seconds": sec, "stage": j}
            if report_bad:
                r["report_error"] = report_bad
                self.warn(f"check {name}: {report_bad} -> ERROR (no verdict)")
            log(f"check {name}: {verdict} (exit {rc}, {sec} s)")
        with self.lock:
            self.res["checks"][name] = r
            self.res["stage_seconds"][f"check_{name}"] = r["seconds"]
        self.save()

    def checks(self, export):
        a = self.a
        names = list(a.checks)   # fast checks first (priority order), C0 last
        t0 = time.time()
        if a.sequential_checks:
            for n in names:
                self.check(n, export)
                self.decide_fast_partial()
        else:
            # the official comparator (hours on big projects, mostly single-threaded) starts at once in the background;
            # the fast checks run one after the other beside it (all at once with --parallel-checks)
            bg = [n for n in names if n == "C0" or a.parallel_checks]
            th = [threading.Thread(target=self.check, args=(n, export)) for n in bg]
            for t in th:
                t.start()
            for n in names:
                if n not in bg:
                    self.check(n, export)
            self.decide_fast_partial()
            for t in th:
                t.join()
        self.res["stage_seconds"]["checks_total"] = round(time.time() - t0, 3)

    def hash_in_background(self, export, reference):
        """sha256 of the export (and of the reference export) in threads beside the checks (~1 GB/s each)."""
        def job(key, path):
            t0 = time.time()
            try:
                h = sha256_file(path)
            except OSError as e:
                h = None
                self.warn(f"cannot hash {path}: {e}")
            with self.lock:
                if key == "export":
                    self.res["export"]["sha256"] = h
                else:
                    self.res["export"].setdefault("reference", {}).update(
                        {"path": path, "sha256": h, "size": os.path.getsize(path)})
                self.res["stage_seconds"][f"sha256_{key}"] = round(time.time() - t0, 3)
        th = [threading.Thread(target=job, args=("export", export))]
        if reference:
            th.append(threading.Thread(target=job, args=("reference", reference)))
        for t in th:
            t.start()
        return th

    def finish_hashes(self, th):
        for t in th:
            t.join()
        if getattr(self, "hashes_done", False):
            return
        self.hashes_done = True
        e = self.res["export"]
        if "reference" in e:
            ref = e["reference"]
            ref["identical"] = (ref.get("sha256") is not None and ref.get("sha256") == e.get("sha256")
                                and ref.get("size") == e.get("size"))
            log(f"export vs reference: {'BYTE-IDENTICAL' if ref['identical'] else 'DIFFERENT'}")
        self.save()

    # ---------------------------------------------------------------- verdict
    def decide_fast_partial(self):
        """Publish the fast verdict as soon as the fast checks are done (the official comparator can take hours)."""
        with self.lock:
            fast = [c for c in self.a.checks if c != "C0"]
            fast_done = bool(fast) and all(CHECK_OPTS[c][0] in self.res["checks"] for c in fast)
            off_pending = "C0" in self.a.checks and "official" not in self.res["checks"]
        if fast_done and off_pending and not getattr(self.a, "sound", False):
            # the export hash / reference identity are final now too (they ran beside the fast checks)
            if getattr(self, "hash_threads", None) is not None and not getattr(self, "hashes_done", False):
                self.finish_hashes(self.hash_threads)
            self.decide()
            with self.lock:
                self.res["verdict"] = "PENDING"
                self.res["verdict_basis"] = ("official comparator still running (fast checks finished; verdict_fast is "
                                             "final and UNOFFICIAL)")
            self.save()

    def confirm_reject(self):
        """--confirm-reject (SOUND mode, opt-in; finding G1-ML-2). Called after decide() when the verdict is
        REJECTED. The build and the exporter are untrusted: an export of the TRANSFORMED build (B3) that CS rejects may
        be the transforms' fault (e.g. debug.skipKernelTC=true makes Mathlib's @[to_dual] keep an ill-typed first
        attempt), not the proof's. So, only if the rejected export came from a successful B3 build, the project is built
        again with the exact build B1 (official lean, Lake's plan, the fresh prepared sources), exported, and every
        selected check runs again on that export (plain replay: the overlap server belonged to the B3 build). decide()
        then decides on the NEW export exactly as before: ACCEPTED only if CS accepts it. If B1 fails the verdict stays
        REJECTED (the official build fails too); if B1 / the export cannot run, the first REJECTED stands (the behaviour
        without the option). Orchestration only: no trusted component and no decision rule changes."""
        a = self.a
        b = self.res.get("build") or {}
        if not (a.sound and b.get("option") == "B3" and b.get("exit") == 0 and self.res.get("verdict") == "REJECTED"):
            return
        t0 = time.time()
        first = {"build": b, "export": self.res.get("export"), "checks": dict(self.res.get("checks") or {}),
                 "verdict": self.res.get("verdict"), "verdict_basis": self.res.get("verdict_basis")}
        rec = {"first": first, "started": now_iso()}
        self.res["confirm_reject"] = rec
        self.warn("sound mode --confirm-reject: CS rejected the export of the transformed build (B3) -> exact build B1 "
                  "(official lean), export and checks once more; REJECTED only if that path rejects too")
        self.overlap_kill()
        # the confirmation check is the plain (unchanged) replay of the whole export; the overlap server/driver of the
        # B3 build are finished (overlap_kill above copied their logs), so the final overlap_kill() must be a no-op
        self.overlap_dir = None
        self.overlap_server = None
        self.overlap_driver = None
        out = os.path.join(self.out, "solution.export")
        old_tmp = getattr(self, "export_tmpdir", None)
        if os.path.lexists(out):   # keep the rejected export only with --keep-work (it is an untrusted intermediate)
            if a.keep_work:
                os.rename(out, os.path.join(self.out, "solution.b3-rejected.export"))
            else:
                if old_tmp:
                    shutil.rmtree(old_tmp, ignore_errors=True)
                    self.export_tmpdir = None
                try:
                    os.chmod(out, 0o644)
                except OSError:
                    pass
                if os.path.lexists(out):
                    os.unlink(out)
        rmtree_force(self.proj)
        copy_project(a.project, self.proj)
        lp = os.path.join(self.logdir, "lean_path.txt")
        if os.path.lexists(lp):
            os.unlink(lp)
        # confirm on a fresh build of the CONFIGURED target only: B1 with
        # --require-modules (a failure outside the solution module's closure DECLINES instead of failing), and the
        # official `lake build MOD` (B0) when B1 declines - exactly what the official comparator builds
        rc, sec, j = self.run_stage("build_confirm_b1", [self.stage_path("build_fast"), self.proj, self.packages_ws,
                                    self.tc, "--log", os.path.join(self.logdir, "build-confirm-b1"),
                                    "--require-modules", self.cc["solution_module"], "--threads",
                                    str(a.threads), "--lean-path-out", lp],
                                    os.path.join(self.logdir, "build_confirm_b1.log"))
        rec["build"] = {"mode": "fast", "option": "B1", "exit": rc, "seconds": sec, "stage": j}
        if rc not in (0, 1):
            # B1 declined / could not run (e.g. Lake 4.36 / 4.37 outside the sound fast
            # path): the official build B0 confirms instead (never 'the first REJECTED stands')
            rmtree_force(self.proj)
            copy_project(a.project, self.proj)
            if os.path.lexists(lp):
                os.unlink(lp)
            ob = self.stage_path("build_official")
            tg = []
            try:   # official-build.sh --targets (build the comparator's module, not the default targets)
                if ob and "--targets)" in open(ob, encoding="utf-8", errors="replace").read():
                    tg = ["--targets", self.cc["solution_module"]]
            except OSError:
                pass
            rc, sec0, j = self.run_stage("build_confirm_b0", [ob, self.proj, self.packages_ws, self.tc, "--log",
                                         os.path.join(self.logdir, "build-confirm-b0"), "--threads", str(a.threads),
                                         "--lean-path-out", lp] + tg, os.path.join(self.logdir, "build_confirm_b0.log"))
            rec["build_b1"] = rec["build"]
            rec["build"] = {"mode": "official", "option": "B0", "exit": rc, "seconds": sec0, "stage": j}
            sec += sec0
        if rc == 1:   # a confirmed failure of the exact build: the report must say so and no host / resource stop shows
            why = self.stage_report_problem(1, j) or resource_failure_evidence(
                [os.path.join(self.logdir, f) for f in (("build_confirm_b0.log", "build-confirm-b0/build.log")
                                                        if rec["build"]["option"] == "B0" else
                                                        ("build_confirm_b1.log", "build-confirm-b1/sched.out",
                                                         "build-confirm-b1/build.log"))])
            if why:
                rc = 2
                rec["build"]["host_failure"] = why
        if rc != 0:
            if rc == 1:
                rec["result"] = f"the exact build {rec['build']['option']} fails too -> REJECTED confirmed"
                self.res["verdict_basis"] = (self.res.get("verdict_basis") or "") + "; --confirm-reject: " + rec["result"]
            else:
                rec["result"] = (f"the exact build {rec['build']['option']} could not complete (exit {rc}): the rejection "
                                 "of the transformed build's export is unconfirmed -> no verdict")
                self.unconfirmed_reject(rec["result"])
            rec["seconds"] = round(time.time() - t0, 3)
            self.res["stage_seconds"]["confirm_reject"] = rec["seconds"]
            self.save()
            return
        self.lean_path = open(lp).read().strip()
        b2 = dict(b)
        b2["attempts"] = list(b.get("attempts") or []) + [dict(rec["build"], purpose="confirm-reject")]
        b2.update({"exit": 0, "mode": rec["build"]["mode"], "option": rec["build"]["option"],
                   "seconds": round(b.get("seconds", 0) + sec, 3)})
        self.res["build"] = b2
        erc = self.export()
        rec["export"] = self.res.get("export")
        if erc != 0:
            rec["result"] = f"the export of the exact build failed (exit {erc}): the rejection is unconfirmed -> no verdict"
            self.res["export"] = first["export"]
            self.res["build"] = b
            self.unconfirmed_reject(rec["result"])
            rec["seconds"] = round(time.time() - t0, 3)
            self.res["stage_seconds"]["confirm_reject"] = rec["seconds"]
            self.save()
            return
        export = self.res["export"]["path"]
        self.res["checks"] = {}
        ref = os.path.realpath(a.reference_export) if a.reference_export else None
        hth = self.hash_in_background(export, ref)
        self.hash_threads = hth
        self.checks(export)
        self.finish_hashes(hth)
        self.decide()
        rec["result"] = f"verdict on the exact build's export: {self.res.get('verdict')}"
        rec["seconds"] = round(time.time() - t0, 3)
        self.res["stage_seconds"]["confirm_reject"] = rec["seconds"]
        if self.res.get("verdict") == "ACCEPTED":
            self.warn("--confirm-reject: the transformed build's export was REJECTED, the exact build's export is ACCEPTED "
                      "by the trusted check (a build transform changed the build output)")
        self.save()

    def selected_not_accepted(self, decided_by):
        """the EXPLICITLY selected checks other than the deciding one that did not accept (ERROR,
        DECLINED, NOT_RUN, missing): an ACCEPTED needs every selected check to accept (a REJECTED of any still vetoes)"""
        ch = self.res.get("checks") or {}
        out = []
        for c in getattr(self.a, "checks", None) or []:
            nm = CHECK_OPTS.get(c, (c,))[0]
            if nm in decided_by:
                continue
            v = (ch.get(nm) or {}).get("verdict", "MISSING")
            if v not in ("ACCEPTED", "REJECTED"):
                out.append(f"{c}={v}")
        return out

    def unconfirmed_reject(self, why):
        """a REJECTED of the TRANSFORMED build's export that the exact build did not confirm is no
        verdict"""
        r = self.res
        r["verdict_unconfirmed"] = r.get("verdict")
        r["verdict"] = r["verdict_fast"] = "DECLINED"
        r["verdict_basis"] = ("SOUND: no verdict - the trusted check rejected the export of the transformed build B3, and "
                              "the rejection was not confirmed on an exact build: " + why)

    def mark_reject_unconfirmed_if_transformed(self):
        """--no-confirm-reject: a REJECTED that rests on the export of a successful transformed build B3 is reported
        unconfirmed (no verdict); exact builds (B0 / B1) and given exports are unaffected"""
        b = self.res.get("build") or {}
        if (self.a.sound or getattr(self.a, "notary", False)) and b.get("option") == "B3" and b.get("exit") == 0 and \
                self.res.get("verdict") == "REJECTED":   # notary too
            self.unconfirmed_reject("--no-confirm-reject")

    def decide_sound(self):
        """SOUND mode (check CS selected): the verdict rests ONLY on the trusted components of GOAL S1 - the given
        official challenge export, the official judge code, the official 4.36 kernel libraries and an independent second
        kernel (all inside CS). The build and the export are untrusted: they can only make CS reject / decline. Every
        other selected check can only veto (turn ACCEPTED into REJECTED)."""
        r = self.res
        ch = dict(r["checks"])
        cs = ch.get("sound") or {"verdict": "NOT_RUN"}
        others = {k: v for k, v in ch.items() if k != "sound"}
        rej = [k for k, v in others.items() if v.get("verdict") == "REJECTED"]
        incomplete = self.selected_not_accepted(("sound",))   # every selected check must accept
        if cs["verdict"] == "ACCEPTED" and not rej and not incomplete:
            v = "ACCEPTED"
        elif cs["verdict"] == "REJECTED" or rej:
            v = "REJECTED"
        else:
            v = "DECLINED"
        r["verdict_fast"] = v
        r["verdict_official"] = (ch.get("official") or {}).get("verdict", "NOT_RUN")
        r["verdict_fast_basis"] = {"policy": "sound", "accepted_by": ["sound"] if cs["verdict"] == "ACCEPTED" else [],
                                   "rejected_by": (["sound"] if cs["verdict"] == "REJECTED" else []) + rej,
                                   "declined_or_not_run": [k for k, x in ch.items()
                                                           if x.get("verdict") not in ("ACCEPTED", "REJECTED")]}
        r["verdict"] = v
        stage = cs.get("stage") if isinstance(cs.get("stage"), dict) else {}
        ce = (r.get("inputs") or {}).get("challenge_export") or {}
        e = r.get("export") or {}
        b = r.get("build") or {}
        r["trust"] = "sound"
        r["unsafe_reasons"] = []
        jrel = self.judge_release_label()   # the release of the SELECTED judge (pins), not always 4.36
        # how the challenge export was obtained: given (pinned by the caller) or built in this run
        built = ce.get("source") not in (None, "given")
        c1 = ("the challenge export was built in this run from the challenge sources by the official lake build and the "
              "official lean4export (B0 + E0)" if built else
              "the challenge is the given official challenge export (never re-elaborated)")
        r["soundness"] = {
            "claim": "ACCEPTED only if every check of GOAL S1 was established by trusted components: (1) " + c1 + "; "
                     "(2) statements equal and (3) only "
                     f"permitted axioms - official Lean {jrel} comparator judge code (ccmp compareAt/checkAxioms); (4) every "
                     f"declaration of the export accepted by the official Lean {jrel} kernel libraries (parallel "
                     "Lean.Replay walk) AND by an independent second kernel (gruszka)",
            "trusted": {"challenge_export": {"sha256": ce.get("sha256"), "source": ce.get("source"),
                                             "pinned_sha256": getattr(self.a, "challenge_sha256", None),
                                             "pin_ok": (None if not getattr(self.a, "challenge_sha256", None)
                                                        else ce.get("sha256") == self.a.challenge_sha256)},
                        "check": {"option": "CS", "verdict": cs.get("verdict"), "basis": stage.get("basis"),
                                  "binaries_sha256": stage.get("binaries_sha256"), "version": stage.get("version"),
                                  "reason": stage.get("reason"), "pins": stage.get("pins"),
                                  "pins_sha256": stage.get("pins_sha256"), "toolchain": stage.get("toolchain"),
                                  "extra_kernels": stage.get("extra_kernels"),
                                  "extra_kernels_summary": stage.get("extra_kernels_summary")}},
            "untrusted": {"build": {"option": b.get("option"), "mode": b.get("mode"),
                                    "transforms": (self.a.unsafe_build if b.get("option") == "B3" else []),
                                    "why_sound": {u: SOUND_TRANSFORMS.get(build_opt_base(u), "re-checked from the export")
                                                  for u in (self.a.unsafe_build if b.get("option") == "B3" else [])}},
                          "export": {"option": e.get("option"), "mode": e.get("mode"), "sha256": e.get("sha256"),
                                     "size": e.get("size"),
                                     "equals_reference": (e.get("reference") or {}).get("identical")}},
        }
        if stage.get("extra_kernels_summary"):   # check-sound v2.3-H: what each extra veto kernel said
            r["extra_kernels"] = stage.get("extra_kernels_summary")
        if v == "ACCEPTED":
            sb = stage.get("basis") or "trusted check CS accepted"
            if built:   # the judge's text assumes a caller-given export
                sb = sb.replace("challenge export as given (sha256 checked by the caller)",
                                "challenge export built officially in this run from the challenge sources (B0 + E0)")
            r["verdict_basis"] = ("SOUND: " + sb + "; build/export untrusted (re-checked from the export)")
        elif v == "REJECTED":
            r["verdict_basis"] = "SOUND: rejected by " + ", ".join(r["verdict_fast_basis"]["rejected_by"]) + (
                f" ({stage.get('reason')})" if stage.get("reason") else "")
        elif cs.get("verdict") == "ACCEPTED" and incomplete:   # a selected check gave no verdict
            r["verdict_basis"] = ("SOUND: no verdict - the trusted check CS accepted, but not every selected check did: "
                                  + ", ".join(incomplete))
        elif cs.get("verdict") in ("NOT_RUN", "ERROR"):   # the trusted check did not run / failed
            r["verdict"] = r["verdict_fast"] = "ERROR"
            r["verdict_basis"] = ("SOUND: no verdict - the trusted check CS did not run or failed: " +
                                  str(cs.get("detail") or cs.get("report_error") or stage.get("reason") or "no reason recorded"))
        else:
            r["verdict_basis"] = f"SOUND: no verdict (trusted check: {cs.get('verdict')}; {stage.get('reason')})"
        off = ch.get("official")
        if off and off.get("verdict") in ("ACCEPTED", "REJECTED") and v in ("ACCEPTED", "REJECTED"):
            r["agreement"] = off["verdict"] == v
            if v == "ACCEPTED" and off["verdict"] == "REJECTED":
                self.warn("official comparator REJECTED what the sound check ACCEPTED (an official limit or a soundness "
                          "bug: investigate)")

    def frontier_sources(self, lemmas):
        """--modulo-frontier, DISPLAY ONLY (untrusted, best effort): where each open lemma is stated in the project's
        sources - file, line and the declaration header as written (up to ':='), so humans and agents see the statement in
        their own notation. The authoritative statement is the frontier challenge's record."""
        import re
        out = {}
        proj = getattr(self, "proj", None)
        if not proj or not os.path.isdir(proj) or not lemmas:
            return out
        want = {}
        for n in lemmas:
            if not isinstance(n, str):
                continue
            pub = re.sub(r"^_private\.(?:[^.]+\.)*?0\.", "", n)   # _private.Mod.0.Ns.x -> Ns.x
            want.setdefault(pub.split(".")[-1], []).append((n, pub))
        pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\s+([^\s:({\[]+)")
        budget = 20000
        for root, dirs, files in os.walk(proj):
            dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
            for fn in files:
                if not fn.endswith(".lean"):
                    continue
                budget -= 1
                if budget < 0:
                    return out
                path = os.path.join(root, fn)
                try:
                    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
                except OSError:
                    continue
                for i, ln in enumerate(lines):
                    m = pat.match(ln)
                    if not m:
                        continue
                    decl = m.group(1)
                    for full, pub in want.get(decl.split(".")[-1], []):
                        if not (pub == decl or pub.endswith("." + decl)):
                            continue
                        head = []
                        for j in range(i, min(len(lines), i + 12)):
                            head.append(lines[j])
                            if ":=" in lines[j] or lines[j].rstrip().endswith(" where"):
                                break
                        text = "\n".join(head)
                        text = text.split(":=")[0].rstrip()
                        out.setdefault(full, []).append({"file": os.path.relpath(path, proj), "line": i + 1,
                                                         "statement_as_written": text[:2000]})
        return out

    def decide_frontier(self):
        """--modulo-frontier (additive): CS ran as check/frontier/check-frontier.sh (preparation + twice the UNCHANGED
        check-sound.sh). Its exit 0 = ACCEPTED (no sorryAx in the export; the unchanged CS accepted with the challenge's
        own configuration), 3 = CONDITIONAL (targets derivable from the permitted axioms + the reported frontier
        statements), 1 = REJECTED, else no verdict. Every other selected check can only veto. CONDITIONAL is never
        ACCEPTED (exit 3). Argument: check/frontier/README.md."""
        self.decide_sound()   # trust, soundness block, veto handling, official agreement - for ACCEPTED/REJECTED/none
        r = self.res
        cs = (r.get("checks") or {}).get("sound") or {}
        stage = cs.get("stage") if isinstance(cs.get("stage"), dict) else {}
        rej = [k for k, v in (r.get("checks") or {}).items() if k != "sound" and v.get("verdict") == "REJECTED"]
        r["frontier"] = {"mode": self.a.modulo_frontier, "pinned": getattr(self.a, "frontier_pin", None),
                         "verdict": cs.get("verdict"), "frontier": stage.get("frontier"),
                         "frontier_size": stage.get("frontier_size"), "frontier_closed": stage.get("frontier_closed"),
                         "outside_pinned_frontier": stage.get("outside_pinned_frontier"),
                         "frontier_challenge_sha256": stage.get("frontier_challenge_sha256"),
                         "blockers": stage.get("blockers"), "claim": stage.get("claim"), "basis": stage.get("basis"),
                         "base_status": stage.get("base_status"), "rewrite": stage.get("rewrite"),
                         "checks": {k: {kk: v.get(kk) for kk in ("verdict", "exit", "wall_s", "reason")}
                                    for k, v in (stage.get("checks") or {}).items() if isinstance(v, dict)}}
        try:
            fr = r["frontier"].get("frontier") or []
            src = self.frontier_sources([e.get("name") for e in fr if isinstance(e, dict)])
            for e in fr:
                if isinstance(e, dict) and src.get(e.get("name")):
                    e["source"] = src[e["name"]][:3]   # display only (untrusted): where the lemma is stated
        except Exception as ex:  # noqa: BLE001 - display only
            self.warn(f"frontier: source lookup failed ({ex})")
        if cs.get("verdict") == "CONDITIONAL" and cs.get("raw_exit") == 3 and not rej and \
                not self.selected_not_accepted(("sound",)):   # every other selected check must accept
            r["verdict"] = r["verdict_fast"] = "CONDITIONAL"
            r["trust"] = "sound-conditional"
            r["verdict_basis"] = ("SOUND-CONDITIONAL: " + str(stage.get("claim") or "targets derivable from the permitted "
                                  "axioms + the reported frontier") + "; build/export untrusted (re-checked from the export)")
            r["soundness"]["claim"] = stage.get("claim")
        sc = ((stage.get("checks") or {}).get("B") or {}) if isinstance(stage.get("checks"), dict) else {}
        if isinstance(r.get("soundness"), dict) and sc:
            r["soundness"]["trusted"]["check"].update({"option": "CS x2 (check/frontier/check-frontier.sh)",
                "basis": stage.get("basis") or sc.get("basis"), "binaries_sha256": sc.get("binaries_sha256"),
                "version": sc.get("version"), "frontier_challenge_sha256": stage.get("frontier_challenge_sha256")})
        if r.get("verdict") == "ACCEPTED" and cs.get("raw_exit") != 0:
            r["verdict"] = r["verdict_fast"] = "DECLINED"   # defensive: ACCEPTED only from check-frontier's exit 0
            r["verdict_basis"] = "inconsistent result of the conditional check: no verdict"

    def decide_notary(self):
        """NOTARY mode (check CN selected): identical trust posture to SOUND mode, strengthened with
        unmodified official Lean 4.36 release kernel libraries (zero PGO/ThinLTO), runtime 3-leg canonical env
        SHA-256 digest cross-check (ccmp-notary == pleanchecker-notary == gruszka-r7), and selectable vetted kernels."""
        r = self.res
        ch = dict(r["checks"])
        cn = ch.get("notary") or {"verdict": "NOT_RUN"}
        others = {k: v for k, v in ch.items() if k != "notary"}
        rej = [k for k, v in others.items() if v.get("verdict") == "REJECTED"]
        incomplete = self.selected_not_accepted(("notary",))   # every selected check must accept
        if cn["verdict"] == "ACCEPTED" and not rej and not incomplete:
            v = "ACCEPTED"
        elif cn["verdict"] == "REJECTED" or rej:
            v = "REJECTED"
        else:
            v = "DECLINED"
        r["verdict_fast"] = v
        r["verdict_official"] = (ch.get("official") or {}).get("verdict", "NOT_RUN")
        r["verdict_fast_basis"] = {"policy": "notary", "accepted_by": ["notary"] if cn["verdict"] == "ACCEPTED" else [],
                                   "rejected_by": (["notary"] if cn["verdict"] == "REJECTED" else []) + rej,
                                   "declined_or_not_run": [k for k, x in ch.items()
                                                           if x.get("verdict") not in ("ACCEPTED", "REJECTED")]}
        r["verdict"] = v
        stage = cn.get("stage") if isinstance(cn.get("stage"), dict) else {}
        ce = (r.get("inputs") or {}).get("challenge_export") or {}
        e = r.get("export") or {}
        b = r.get("build") or {}
        r["trust"] = "notary"
        r["unsafe_reasons"] = []
        r["soundness"] = {
            "claim": "ACCEPTED only if every check of GOAL S1 and of the notary design passed: unmodified official Lean 4.36 release "
                     "kernel libraries (ccmp-notary + pleanchecker-notary) + independent kernel(s) + runtime 3-leg "
                     "canonical environment SHA-256 digest equality across ccmp, Lean replay, and gruszka-r7",
            "trusted": {"challenge_export": {"sha256": ce.get("sha256"), "source": ce.get("source"),
                                             "pinned_sha256": getattr(self.a, "challenge_sha256", None),
                                             "pin_ok": (None if not getattr(self.a, "challenge_sha256", None)
                                                        else ce.get("sha256") == self.a.challenge_sha256)},
                        "check": {"option": "CN", "verdict": cn.get("verdict"), "basis": stage.get("basis"),
                                  "binaries_sha256": stage.get("binaries_sha256"), "version": stage.get("version"),
                                  "kernels": stage.get("kernels"), "r7_digest": stage.get("r7_digest"),
                                  "reason": stage.get("reason")}},
            "untrusted": {"build": {"option": b.get("option"), "mode": b.get("mode")},
                          "export": {"option": e.get("option"), "mode": e.get("mode"), "sha256": e.get("sha256"),
                                     "size": e.get("size")}},
        }
        if v == "ACCEPTED":
            r["verdict_basis"] = "NOTARY: " + (stage.get("basis") or "trusted check CN accepted")
        elif v == "REJECTED":
            r["verdict_basis"] = "NOTARY: rejected by " + ", ".join(r["verdict_fast_basis"]["rejected_by"]) + (
                f" ({stage.get('reason')})" if stage.get("reason") else "")
        elif cn.get("verdict") == "ACCEPTED" and incomplete:   # a selected check gave no verdict
            r["verdict_basis"] = ("NOTARY: no verdict - the trusted check CN accepted, but not every selected check did: "
                                  + ", ".join(incomplete))
        elif cn.get("verdict") in ("NOT_RUN", "ERROR"):   # the trusted check did not run / failed
            r["verdict"] = r["verdict_fast"] = "ERROR"
            r["verdict_basis"] = ("NOTARY: no verdict - the trusted check CN did not run or failed: " +
                                  str(cn.get("detail") or cn.get("report_error") or stage.get("reason") or "no reason recorded"))
        else:
            r["verdict_basis"] = f"NOTARY: no verdict (trusted check: {cn.get('verdict')}; {stage.get('reason')})"
        off = ch.get("official")
        if off and off.get("verdict") in ("ACCEPTED", "REJECTED") and v in ("ACCEPTED", "REJECTED"):
            r["agreement"] = off["verdict"] == v

    def decide_sound_and_notary(self):
        """CS and CN both selected: BOTH decision rules must hold (before: decide_notary alone decided,
        so a CS DECLINED - e.g. a missing --require-kernel kernel - was dropped and CN's ACCEPTED counted). ACCEPTED iff the
        sound decision AND the notary decision are ACCEPTED; REJECTED if either is (a trusted judge's own rejection);
        otherwise DECLINED."""
        self.decide_sound()
        keys = ("verdict", "trust", "verdict_basis", "soundness", "verdict_fast", "verdict_fast_basis", "unsafe_reasons")
        snd = {k: self.res.get(k) for k in keys}
        self.decide_notary()
        nty = {k: self.res.get(k) for k in keys}
        vs = {"sound": snd["verdict"], "notary": nty["verdict"]}
        if all(v == "ACCEPTED" for v in vs.values()):
            v = "ACCEPTED"
            basis = f"SOUND AND NOTARY: both decisions accepted ({snd['verdict_basis']} | {nty['verdict_basis']})"
        elif "REJECTED" in vs.values():
            v = "REJECTED"
            basis = "SOUND AND NOTARY: rejected by the " + " and ".join(k for k, x in vs.items() if x == "REJECTED") + \
                " decision (" + " | ".join(str(d["verdict_basis"]) for d in (snd, nty) if d["verdict"] == "REJECTED") + ")"
        else:
            v = "DECLINED"
            basis = "SOUND AND NOTARY: no verdict (" + ", ".join(f"{k}: {x}" for k, x in vs.items()) + ")"
        self.res.update(verdict=v, verdict_fast=v, trust="sound", verdict_basis=basis, soundness=snd["soundness"],
                        soundness_notary=nty["soundness"], unsafe_reasons=[],
                        decision_rules={"rule": "conjunction (every selected decision must accept)", **vs})

    def decide(self):
        if getattr(self.a, "notary", False) and getattr(self.a, "sound", False):
            return self.decide_sound_and_notary()
        if getattr(self.a, "notary", False):
            return self.decide_notary()
        if getattr(self.a, "modulo_frontier", None) and getattr(self.a, "sound", False):
            return self.decide_frontier()
        if getattr(self.a, "sound", False):
            return self.decide_sound()
        r = self.res
        ch = dict(r["checks"])
        off = ch.get("official")
        fast = {k: v for k, v in ch.items() if k != "official"}
        fv = None
        if fast:
            vs = [v["verdict"] for v in fast.values()]
            acc = [k for k, v in fast.items() if v["verdict"] == "ACCEPTED"]
            rej = [k for k, v in fast.items() if v["verdict"] == "REJECTED"]
            if self.a.fast_policy == "all":
                fv = "ACCEPTED" if all(v == "ACCEPTED" for v in vs) else (
                    "REJECTED" if all(v == "REJECTED" for v in vs) else "DECLINED")
            elif self.a.fast_policy == "any":  # >= 1 fast checker accepted and none rejected
                fv = "REJECTED" if rej and not acc else ("ACCEPTED" if acc and not rej else "DECLINED")
            else:  # primary (default): the strongest selected fast check (C3 > C4) decides, every other
                # selected fast check can only veto
                prim = next((CHECK_OPTS[c][0] for c in FAST_PRIORITY if c in self.a.checks), None)
                a_v = fast.get(prim, {}).get("verdict")
                if a_v == "ACCEPTED" and not rej:
                    fv = "ACCEPTED"
                elif a_v == "REJECTED" and not acc:
                    fv = "REJECTED"
                else:
                    fv = "DECLINED"
            r["verdict_fast_basis"] = {"policy": self.a.fast_policy, "accepted_by": acc, "rejected_by": rej,
                                       "declined_or_not_run": [k for k in fast if k not in acc and k not in rej]}
        r["verdict_fast"] = fv
        r["verdict_official"] = off["verdict"] if off else "NOT_RUN"
        if off:
            if off["verdict"] in ("ACCEPTED", "REJECTED"):
                r["verdict"] = off["verdict"]
                # name the comparator that actually judged: check/official/check.sh picks the challenge
                # release's own (4.37.0-rc1 -> the 4.37.0-rc1 lake comparator), never silently 4.36's
                st = off.get("stage") if isinstance(off.get("stage"), dict) else {}
                r["verdict_basis"] = "official comparator (%s)" % (st.get("tool") or "check/official/check.sh")
                if st.get("challenge_release"):
                    r["official_comparator"] = {"challenge_release": st.get("challenge_release"),
                                                "comparator_toolchain": st.get("comparator_toolchain"), "tool": st.get("tool")}
            else:
                r["verdict"] = "ERROR"
                r["verdict_basis"] = f"official comparator did not give a verdict ({off['verdict']})"
            decided = {k: v["verdict"] for k, v in fast.items() if v["verdict"] in ("ACCEPTED", "REJECTED")}
            if decided and off["verdict"] in ("ACCEPTED", "REJECTED"):
                diff = {k: v for k, v in decided.items() if v != off["verdict"]}
                r["agreement"] = not diff
                for k, v in diff.items():
                    if v == "ACCEPTED":
                        self.warn(f"ALARM: fast check {k} ACCEPTED what the official comparator REJECTED "
                                  "(fast-checker soundness bug or an official limit the pre-check missed)")
                    else:
                        self.warn(f"fast check {k} REJECTED what the official comparator ACCEPTED (false reject)")
        else:
            r["verdict"] = fv or "ERROR"
            r["verdict_basis"] = (f"fast checks only - UNOFFICIAL (policy '{self.a.fast_policy}'; the official "
                                  "comparator was not run)")
        # trust label: which options the verdict rests on
        reasons = []
        b = r.get("build") or {}
        if b.get("option") == "B3":
            reasons += [f"build option {u} (breaks: findings {UNSAFE_BUILD_OPTS[build_opt_base(u)]})"
                        for u in self.a.unsafe_build]
        bst = ((b.get("attempts") or [{}])[-1].get("stage") or {})
        if b.get("mode") == "fast" and isinstance(bst, dict) and bst.get("exact") is False:
            reasons.append(f"build stage reports exact=false (unsafe: {bst.get('unsafe')})")
        exp_r = r.get("export") or {}
        # the given-export path records mode 'given (private copy)': test the explicit flag / the
        # option itself, never an exact mode string (the exact '== "given"' test never matched, so the caveat was lost)
        if exp_r.get("given") is True or str(exp_r.get("mode") or "").startswith("given") or getattr(self.a, "export", None):
            reasons.append("export given by the caller (--from-export): its provenance is the caller's")
        if off and off["verdict"] in ("ACCEPTED", "REJECTED"):
            r["trust"] = "official" if not reasons else "UNSAFE"
        else:
            prim = next((c for c in FAST_PRIORITY if c in self.a.checks), None)
            pst = (fast.get(CHECK_OPTS[prim][0], {}).get("stage") or {}) if prim else {}
            for u in self.a.unsafe_check:
                if prim in UNSAFE_CHECK_OPTS[u][0]:
                    reasons.append(f"check modifier {u} on {prim} ({UNSAFE_CHECK_OPTS[u][2]})")
            if isinstance(pst, dict) and (pst.get("inexact") or pst.get("unsafe")):
                reasons.append(f"{prim} reports inexact/unsafe: {pst.get('inexact') or pst.get('unsafe')}")
            if prim == "C3":
                reasons.append("C3 decides: independent unofficial kernels (gruszka, nano-lean), not the official "
                               "kernel (finding 026 class)")
            elif prim == "C4":
                reasons.append("C4 decides: a single independent unofficial kernel (findings 026, 001, 071 class)")
            if self.a.fast_policy in ("any",):
                reasons.append("fast policy 'any': a secondary check alone may accept")
            r["trust"] = "exact-by-design (unofficial)" if not reasons else "UNSAFE"
        r["unsafe_reasons"] = reasons


def install_early_signal_handlers(a):
    """SIGTERM / SIGINT / SIGHUP (the ones not ignored) between argument parsing and Run(): planning
    (sound-auto's autotune) runs before OUT is validated and before main() installs its own handler, so a signal there
    ended the process without any record. Now it writes a minimal ERROR result.json - only into an OUT this run may use (not
    inside PROJECT / CHALLENGE, absent or an empty directory: the same rule main() applies, finding 067) - and exits 2
    (no verdict). main() replaces these handlers with its own once Run() exists."""
    import signal as _sg

    def early(signum, frame):
        with CHILDREN_LOCK:
            kids = list(CHILDREN)
        for k in kids:
            kill_tree(k)
        msg = f"interrupted by signal {signum} before the run started (planning): no verdict"
        try:
            out = os.path.realpath(a.out)
            ok = True
            for d in (a.project, a.challenge):
                d = os.path.realpath(d) if d and d not in ("", "-") else None
                if d and (out == d or out.startswith(d + os.sep) or d.startswith(out + os.sep)):
                    ok = False
            if ok and (not os.path.exists(out) or (os.path.isdir(out) and not os.listdir(out))):
                os.makedirs(out, exist_ok=True)
                with open(os.path.join(out, "result.json"), "w") as f:
                    json.dump({"fastverify": {"version": VERSION, "root": ROOT}, "verdict": "ERROR", "verdict_basis": msg,
                               "interrupted": f"signal {signum} at {now_iso()}", "finished": now_iso(), "exit": 2}, f,
                              indent=1)
                    f.write("\n")
        except Exception:  # noqa: BLE001 - never more than a best-effort record; the exit status is 2 regardless
            pass
        print(f"fastverify: {msg}", file=sys.stderr)
        os._exit(2)
    for sg in (_sg.SIGTERM, _sg.SIGINT, _sg.SIGHUP):
        if _sg.getsignal(sg) is not _sg.SIG_IGN:
            _sg.signal(sg, early)



class _StoreOnce(argparse.Action):
    """identity / mode options are given ONCE: a wrapper's pinned value (tools/rh-sound.sh,
    tools/claims.py, ...) can never be replaced by a later forwarded occurrence - also not through an abbreviation or the
    = spelling, which argparse maps to the same option"""
    def __call__(self, parser, namespace, values, option_string=None):
        seen = namespace.__dict__.setdefault("_store_once_seen", set())
        if self.dest in seen:
            parser.error(f"{option_string or self.dest} given more than once (identity / mode options are given once)")
        seen.add(self.dest)
        setattr(namespace, self.dest, values)

def main():
    ap = argparse.ArgumentParser(prog="fastverify", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("project", help="Lean 4 project directory (sources, lakefile, lake-manifest.json, lean-toolchain)")
    ap.add_argument("challenge", help="clean challenge directory (comparator.json, lean-toolchain, [challenge.export], "
                    "[export-targets.txt], [.lake/packages])")
    ap.add_argument("out", help="output directory (must not exist or be empty)")
    ap.add_argument("--threads", type=int, default=len(os.sched_getaffinity(0)))
    ap.add_argument("--preset", action=_StoreOnce, choices=sorted(PRESETS) + sorted(RETIRED_PRESETS), default=None,
                    metavar="{" + ",".join(sorted(PRESETS)) + "}",
                    help="sound = B3(untrusted transforms)+E1+CS; sound-auto = the same check CS, build items chosen per "
                    "project/host; notary = B0+E0+CN; reference = B0+E0+C0; fastest = B3(all unsafe)+E1+C4 (UNSAFE). "
                    "Explicit --build/--export/--check/--unsafe override the preset. Without --preset, --check is required "
                    "(build B1, export E1 unless given). Retired (refused): fast-exact, default.")
    ap.add_argument("--build", help="B0 official lake build | B1 Lake-planned direct scheduler (official binaries) | "
                    "B2 B1 + safe organization speedups | B3 B2 + the --unsafe options (UNSAFE); aliases: official=B0, "
                    "fast=B1")
    ap.add_argument("--unsafe", help="comma list of UNSAFE build options for B3: " + ", ".join(
                    f"{k} (breaks: {v})" for k, v in UNSAFE_BUILD_OPTS.items()) + "; 'all' = every one")
    ap.add_argument("--export", dest="export_arg", action=_StoreOnce, help="E0 official lean4export | E1 native exporter (fail-closed -> "
                    "E0); any other value = an existing export FILE to judge (same as --from-export)")
    ap.add_argument("--from-export", dest="export", action=_StoreOnce, help="judge this existing export instead of building/exporting")
    ap.add_argument("--check", action=_StoreOnce, help="comma list of CS sound check | CN notary check | C0 official comparator | C3 dual "
                    "independent kernels | C4 single independent kernel (UNSAFE); alias: official=C0. Retired "
                    "(refused): C1, C2 (check A) and the aliases fast, both")
    ap.add_argument("--fast-checks", help=argparse.SUPPRESS)   # retired (RETIRED_FAST_CHECKS): refused
    ap.add_argument("--fast-policy", choices=("primary", "checkA", "any", "all"), default="primary",
                    metavar="{primary,any,all}",
                    help="verdict_fast without CS/CN: primary (default) = the strongest selected fast check (C3>C4) "
                    "decides, the others can only veto; any = >=1 accepted, none rejected; all = every one accepted. "
                    "The alias checkA is retired (refused)")
    ap.add_argument("--packages", help="trusted Lake workspace with materialized dependencies (default: CHALLENGE if "
                    "CHALLENGE/.lake/packages exists)")
    ap.add_argument("--comparator-config", action=_StoreOnce, help="comparator config (default CHALLENGE/comparator.json)")
    ap.add_argument("--reference-export", help="compare the produced export byte-for-byte with this file")
    ap.add_argument("--official-timeout", type=int, default=0, help="seconds (0 = none); timeout = ERROR, not a verdict")
    ap.add_argument("--parallel-checks", action="store_true", help="run all checks concurrently (memory!); default: "
                    "the official comparator runs in the background while the fast checks run one after the other")
    ap.add_argument("--sequential-checks", action="store_true", help="run every check alone (clean per-check timing)")
    ap.add_argument("--no-confirm-build-failure", dest="confirm_build_failure", action="store_false",
                    help="do not re-run the official build when the fast build fails")
    ap.add_argument("--pins", action=_StoreOnce, default=None, metavar="FILE", help="SOUND mode: pins file of the trusted check CS, a "
                    "pins*.env inside check/sound/ (e.g. check/sound/pins-437.env = the check built from Lean 4.37.0-rc1); "
                    "default check/sound/pins.env; --preset sound-auto picks the pins file whose TC_VERSION equals the "
                    "challenge's lean-toolchain")
    ap.add_argument("--check-hints", default=None, metavar="FILE|none", help="SOUND mode: scheduling hints of the trusted "
                    "check's Lean-kernel replay (declaration names served first; order only, S03; default "
                    "check/sound/hints/default.txt = RH's slow declarations), e.g. refreshed for a compressed composite with "
                    "check/sound/hints/mkhints.sh from an earlier check log; 'none' disables them")
    ap.add_argument("--check-hide", default=None, metavar="FILE|none", help="SOUND mode with a selected pins file: the "
                    "trusted check's hide list (encapsulated replay; availability only), a file in check/sound/hide/; default the "
                    "release's check/sound/hide/lean-<version>-no-expose.txt if present; 'none' disables it")
    ap.add_argument("--no-integrity-cache", action="store_true", help="sound-auto: verify every pinned component and "
                    "toolchain tree in full in every run (default: a stamp comparison after one full verification, kept in "
                    "/tmp/fastverify-icache-UID/)")
    ap.add_argument("--confirm-build-failure-full", action="store_true", help="sound-auto: always confirm a failed "
                    "transformed build with the full exact build B1 (default: the failing modules' exact per-module "
                    "retry confirms it)")
    ap.add_argument("--keep-work", action="store_true", help="keep OUT/work (prepared/built project)")
    ap.add_argument("--no-build-fallback", action="store_true", help="if the fast build declines (or fails), stop "
                    "with ERROR instead of running the official lake build (time-boxed runs of huge projects)")
    ap.add_argument("--require-fast", action="store_true", help="refuse (exit 2) instead of falling back to the "
                    "official build/export when a fast component is not usable on this host")
    ap.add_argument("--export-dir", help="write the export into a fresh directory under this one (e.g. /dev/shm: "
                    "tmpfs is faster than one huge ext4 file); OUT/solution.export becomes a symlink; removed at the end "
                    "unless --keep-work. Needs >= 256 GB free, else the export goes to OUT as usual. Default of --preset sound: /dev/shm "
                    "('none' disables)")
    ap.add_argument("--overlap-targets", default=None, metavar="FILE", help="target list for --overlap-targeted "
                    "(implies it; relative to the package root), e.g. overlap/targets-top40.txt; default: overlap/targets-top40.txt if present, else the CS hint list")
    ap.add_argument("--overlap-targeted", action="store_true", help="SOUND mode: --overlap in TARGETED mode (only "
                    "the declarations of the CS kernel hint list are kernel-checked during the build; the final replay "
                    "skips those whose export version and closure equal the checked ones)")
    ap.add_argument("--overlap", action="store_true", help="SOUND mode: overlap the Lean-kernel leg with the build "
                    "(snapshot exports of built modules are kernel-checked while the build runs; PChk/Incr.lean)")
    ap.add_argument("--challenge-sha256", action=_StoreOnce, help="SOUND mode: the sha256 the challenge export MUST have (the official "
                    "challenge export, GOAL S1(1)); a different challenge export -> refuse")
    ap.add_argument("--comparator-sha256", action=_StoreOnce, help="the sha256 the comparator config MUST have (the other half of the "
                    "challenge identity); a different config -> refuse; the trusted judge verifies its private copy against "
                    "the same value. REQUIRED in sound / sound-auto / notary / frontier mode whenever --challenge-sha256 is "
                    "(a given challenge export)")
    ap.add_argument("--no-confirm-reject", action="store_true", help="turn off --confirm-reject, which the sound "
                    "presets enable by default")
    ap.add_argument("--extra-kernel", action="append", default=[], metavar="NAME", choices=["con-leche", "nanoda"],
                    help="SOUND mode (check CS, check-sound v2.3-H): enable a VETO-ONLY extra kernel (both are opt-in; "
                    "con-leche rejects some valid proofs that unfold a theorem body): its genuine rejection turns ACCEPTED "
                    "into REJECTED, anything it cannot decide is recorded and leaves the verdict (check-sound.sh --kernel; "
                    "waited for without a time limit: bin/fastverify passes no --timeout to CS)")
    ap.add_argument("--require-kernel", action="append", default=[], metavar="NAME", choices=["con-leche", "nanoda"],
                    help="SOUND mode: make an extra kernel MANDATORY (check-sound.sh --require-kernel): ACCEPTED then also "
                    "needs its acceptance; if it cannot decide there is no verdict. Uses the normal check (never the "
                    "low-memory one, which has no extra kernels); refused with --modulo-frontier")
    ap.add_argument("--skip-extra-kernel", action="append", default=[], metavar="NAME", choices=["con-leche", "nanoda"],
                    help="SOUND mode: do not run this extra veto kernel (check-sound.sh --skip-kernel; the verdict is then "
                    "the two-kernel verdict of check-sound v2.2)")
    ap.add_argument("--require-sorried-holes", action="store_true", help="SOUND / NOTARY: the trusted judge refuses (no verdict: ERROR / DECLINED, exit 2) a challenge whose definition holes are not sorried, for every Lean release (the official 4.37 comparator rule; default off = the official 4.36 semantics for releases before 4.37; 4.37 challenges always get the rule)")
    ap.add_argument("--experimental", action="store_true",
                    help="opt in to the EXPERIMENTAL features of v0.1: the notary check (--preset notary / --check CN); "
                         "without it they are refused (exit 2)")
    ap.add_argument("--notary-kernels", default=None, metavar="LIST",
                    help="with --preset notary / --check CN: comma-separated second kernels "
                         "(subset of gruszka,con-ron,con-leche,nanoda; default: gruszka)")
    ap.add_argument("--confirm-reject", action="store_true", help="SOUND mode only (default off): if the trusted check CS "
                    "REJECTS the export of a SUCCESSFUL transformed build (B3), rebuild once with the exact build B1 "
                    "(official lean, Lake's plan), export and run the selected checks again on that export; REJECTED only "
                    "if the exact path rejects (or cannot build) too. ACCEPTED still only from CS on the reported export. "
                    "Availability fix for transforms that silently change the build output ("
                    "skip-kernel-tc + Mathlib's @[to_dual])")
    ap.add_argument("--modulo-frontier", nargs="?", const="auto", default=None, metavar="auto|FILE",
                    help="SOUND mode only (default off): conditional verdict modulo an explicit sorry "
                    "frontier. The check runs check/frontier/check-frontier.sh (untrusted preparation + the unchanged sound "
                    "check, twice): exit 3 = CONDITIONAL (every target derivable from the permitted axioms + the statements "
                    "of the reported sorried theorems, result.json 'frontier'), 0 = ACCEPTED (no open lemma), "
                    "1 = REJECTED (incl. a sorry inside a definition or a target), 2 = no verdict. FILE = allowed "
                    "frontier (one declaration name per line): a frontier theorem outside FILE -> REJECTED")
    ap.add_argument("--frontier-base", default=None, metavar="RESULT", help="with --modulo-frontier (informational, "
                    "ledger): an earlier result.json; result.json 'frontier.base_status' then says for each of its open "
                    "lemmas whether it is still open, proved, or dropped (left the closure); see tools/frontier/ledger.py")
    ap.add_argument("--frontier-pin", default=None, metavar="DIR", help="with --modulo-frontier: judge against the "
                    "pinned frontier challenge in DIR (tools/frontier/frontier.py pin): the open lemmas' statements cannot "
                    "drift and no new open lemma is allowed")
    ap.add_argument("--build-cache", default=None, metavar="DIR|none", help="fast builds (B1-B3): private per-user cache "
                    "of untrusted build helpers (compiled planner, unofficial-toolchain verification stamps; build/bcache.py); "
                    "default: none, --preset sound-auto: /tmp/fastverify-build-cache-UID")
    ap.add_argument("--preflight-only", action="store_true", help="only check that every component is installed, "
                    "pinned and starts on this host; exit 0 iff all stages needed for the given options are usable")
    a = ap.parse_args()
    install_early_signal_handlers(a)   # a signal during planning (before Run exists) still writes ERROR
    # check A (C1/C2) and everything that selected it were retired: refuse, naming the replacement
    if a.preset in RETIRED_PRESETS:
        ap.error(RETIRED_PRESETS[a.preset])
    if a.fast_checks is not None:
        ap.error(RETIRED_FAST_CHECKS)
    if a.fast_policy == "checkA":
        ap.error(RETIRED_FAST_POLICY)
    for c in (a.check or "").split(","):
        if c in RETIRED_CHECKS:
            ap.error(RETIRED_CHECKS[c])
    for u in (a.unsafe or "").split(","):
        if u in RETIRED_UNSAFE:
            ap.error(RETIRED_UNSAFE[u])
    if a.preset is None and a.check is None:
        ap.error(NO_PRESET)
    # without --preset (explicit --check): build B1 and export E1 unless given, as before the retirement
    pre = PRESETS[a.preset] if a.preset is not None else {"build": "B1", "export": "E1", "check": [], "unsafe": []}
    a.autotune = None
    # the pin syntax and the pin-pair rule are checked BEFORE any planning: an invalid value is a
    # usage error here; an incomplete pair skips the tuner (the run is refused in read_inputs, which writes result.json)
    for opt, v in (("--challenge-sha256", a.challenge_sha256), ("--comparator-sha256", a.comparator_sha256)):
        if v is not None and not (len(v) == 64 and all(c in "0123456789abcdef" for c in v)):
            ap.error(f"{opt} must be 64 lowercase hex digits")
    fam = a.preset in ("sound", "sound-auto", "notary") or bool({"CS", "CN"} & set((a.check or "").split(",")))
    pair_incomplete = fam and not a.comparator_sha256 and bool(
        a.challenge_sha256 or (a.challenge and os.path.isfile(os.path.join(a.challenge, "challenge.export"))))
    if fam and a.comparator_sha256 and not pair_incomplete:   # a wrong digest: no planning either
        try:
            cfg0 = a.comparator_config or os.path.join(a.challenge or "", "comparator.json")
            pair_incomplete = sha256_file(cfg0) != a.comparator_sha256
        except OSError:
            pair_incomplete = True
    if pre.get("auto") and pair_incomplete:
        pre = dict(PRESETS["sound"])
        a.autotune = {"skipped": "the challenge pin pair is incomplete or does not match: the run is refused before any planning"}
    elif pre.get("auto"):
        exin = a.export or (a.export_arg and a.export_arg not in ("E0", "E1"))
        if not exin and (not a.project or a.project in ("", "-") or not os.path.isdir(a.project)):
            ap.error("--preset sound-auto needs a PROJECT directory (or --from-export)")
        try:
            pre, a.autotune = autotune_preset(a, pre)
        except Exception as e:   # noqa: BLE001 - the choice is untrusted: fall back to the measured sound preset
            print(f"fastverify: sound-auto: autotune failed ({e!r}) -> the sound preset's item list", file=sys.stderr)
            pre = dict(PRESETS["sound"])
            a.autotune = {"error": repr(e), "fallback": "sound"}
    # build option
    b = {"official": "B0", "fast": "B1", None: pre["build"]}.get(a.build, a.build)
    if b not in ("B0", "B1", "B2", "B3"):
        ap.error(f"--build {a.build}: expected B0|B1|B2|B3")
    a.build = b
    # unsafe options (B3 only)
    if a.unsafe is None:
        a.unsafe = list(pre["unsafe"])
    else:
        a.unsafe = (LEGACY_UNSAFE_BUILD + sorted(UNSAFE_CHECK_OPTS)) if a.unsafe == "all" else \
            [u for u in a.unsafe.split(",") if u]
    for u in a.unsafe:
        if build_opt_base(u) not in UNSAFE_BUILD_OPTS and u not in UNSAFE_CHECK_OPTS:
            ap.error(f"--unsafe {u}: expected one of {', '.join(list(UNSAFE_BUILD_OPTS) + list(UNSAFE_CHECK_OPTS))}")
    a.unsafe_build = [u for u in a.unsafe if build_opt_base(u) in UNSAFE_BUILD_OPTS]
    a.unsafe_check = [u for u in a.unsafe if u in UNSAFE_CHECK_OPTS]
    # export option / given export
    a.export_opt = pre["export"]
    if a.export_arg in ("E0", "E1"):
        a.export_opt = a.export_arg
    elif a.export_arg:
        if a.export:
            ap.error("--export FILE and --from-export FILE given")
        a.export = a.export_arg
    # checks
    if a.check is None:
        checks = list(pre["check"])
    else:
        checks = []
        for c in a.check.split(","):
            checks += {"official": ["C0"]}.get(c, [c])
    for c in checks:
        if c not in CHECK_OPTS:
            ap.error(f"--check {c}: expected one of {', '.join(CHECK_OPTS)} (or official)")
    a.checks = [c for c in FAST_PRIORITY if c in checks] + (["C0"] if "C0" in checks else [])
    if not a.checks:
        ap.error("no check selected")
    if getattr(a, "notary_kernels", None) is not None:   # a malformed selection is a usage error
        ks = a.notary_kernels.split(",")
        if a.notary_kernels != "all" and (not ks or any(k not in ("gruszka", "con-ron", "con-leche", "nanoda") for k in ks)):
            ap.error(f"--notary-kernels {a.notary_kernels}: expected 'all' or a comma list of gruszka, con-ron, con-leche, nanoda")
    a.sound = "CS" in a.checks   # SOUND mode: CS decides (decide_sound), build/export are untrusted
    a.notary = "CN" in a.checks  # NOTARY mode (additive): CN decides (decide_notary)
    # a trusted preset whose deciding check was overridden away is inconsistent: refused (it would
    # run with another trust basis than the preset recorded in result.json)
    if a.preset in ("sound", "sound-auto") and not a.sound:
        ap.error(f"--preset {a.preset} with --check {a.check}: the sound check CS must stay selected")
    if a.preset == "notary" and not a.notary:
        ap.error(f"--preset notary with --check {a.check}: the notary check CN must stay selected")
    # the notary preset ships EXPERIMENTAL in v0.1: the notary check
    # runs only with --experimental: its rejection classification still has known limitations (listed in
    # check/notary/README.md). Refused before anything runs (exit 2). check-notary.sh called directly
    # is unchanged (documented there).
    if (a.notary or a.preset == "notary") and not a.experimental:
        ap.error("the notary check (--preset notary / --check CN) is EXPERIMENTAL in v0.1: pass --experimental to run it "
                 "(known limitations: check/notary/README.md); otherwise use --preset sound or "
                 "--preset reference")
    # extra veto kernels of check-sound v2.3-H: a requirement is never dropped silently
    if set(a.require_kernel) & set(a.skip_extra_kernel):
        ap.error("--require-kernel and --skip-extra-kernel name the same kernel")
    if (a.require_kernel or a.extra_kernel or a.skip_extra_kernel) and "CS" not in a.checks:
        ap.error("--extra-kernel / --require-kernel / --skip-extra-kernel need the sound check (--preset sound* or --check CS); "
                 "the notary preset selects its kernels with --notary-kernels (every selected kernel is mandatory there)")
    if a.require_kernel and getattr(a, "modulo_frontier", None):
        ap.error("--require-kernel is not supported with --modulo-frontier (check-frontier.sh runs check-sound.sh with its "
                 "default extra kernels and passes no --require-kernel); a required kernel is never dropped")
    if a.modulo_frontier:
        if not a.sound:
            ap.error("--modulo-frontier needs the sound check (--preset sound or --check CS)")
        if a.notary:   # the notary decision would silently override the conditional one
            ap.error("--modulo-frontier cannot be combined with the notary check CN (a complete-proof judge): choose one")
        if a.modulo_frontier != "auto":
            if not os.path.isfile(a.modulo_frontier):
                ap.error(f"--modulo-frontier {a.modulo_frontier}: not a file")
            a.modulo_frontier = os.path.realpath(a.modulo_frontier)
    if a.frontier_base:
        if not a.modulo_frontier:
            ap.error("--frontier-base needs --modulo-frontier")
        if not os.path.isfile(a.frontier_base):
            ap.error(f"--frontier-base {a.frontier_base}: not a file")
        a.frontier_base = os.path.realpath(a.frontier_base)
    if a.frontier_pin:
        if not a.modulo_frontier:
            ap.error("--frontier-pin needs --modulo-frontier")
        if not os.path.isfile(os.path.join(a.frontier_pin, "challenge.export")):
            ap.error(f"--frontier-pin {a.frontier_pin}: no pinned frontier challenge there")
        a.frontier_pin = os.path.realpath(a.frontier_pin)
    # a GIVEN value is validated even when empty: a malformed option is a usage error (exit 2),
    # never "no pin" (an empty pin used to be ignored in modes that do not require one)
    if a.challenge_sha256 is not None and not (len(a.challenge_sha256) == 64 and all(c in "0123456789abcdef" for c in
                                                                                      a.challenge_sha256)):
        ap.error("--challenge-sha256 must be 64 lowercase hex digits")
    if a.comparator_sha256 is not None and not (len(a.comparator_sha256) == 64 and all(c in "0123456789abcdef" for c in
                                                                                        a.comparator_sha256)):
        ap.error("--comparator-sha256 must be 64 lowercase hex digits")
    # the sound presets confirm a REJECTED of a transformed build's export
    # with the exact build B1 (costs time only on such a rejection); --no-confirm-reject turns it off
    if a.preset in ("sound", "sound-auto") and not a.no_confirm_reject:
        a.confirm_reject = True
    if a.no_confirm_reject:
        a.confirm_reject = False
    if a.unsafe_build and a.build != "B3":
        if a.preset is not None and a.build != PRESETS[a.preset]["build"]:
            a.unsafe_build = []   # an explicit safe --build overrides the preset's unsafe build options
        else:
            ap.error("unsafe build options (" + ",".join(a.unsafe_build) + ") need --build B3")
    for u in list(a.unsafe_check):
        if not any(c in a.checks for c in UNSAFE_CHECK_OPTS[u][0]):
            a.unsafe_check.remove(u)   # modifier of a check that is not selected: nothing to modify
    a.unsafe = a.unsafe_build + a.unsafe_check
    for k, v in pre.get("options", {}).items():   # preset-level orchestrator defaults (explicit flags win)
        if getattr(a, k, None) in (None, False):
            setattr(a, k, v)
    if a.export_dir == "none":   # explicit opt-out of the preset's tmpfs export
        a.export_dir = None
    if getattr(a, "overlap_targets", None) == "none":   # explicit opt-out of the preset's targeted overlap
        a.overlap_targets = None
    if getattr(a, "build_cache", None) == "none":
        a.build_cache = None
    if a.export_dir:
        a.export_dir = os.path.realpath(a.export_dir)
    if a.export:
        a.export = os.path.realpath(a.export)
    a.project = os.path.realpath(a.project) if a.project not in ("", "-") else None
    a.challenge = os.path.realpath(a.challenge)
    out_real = os.path.realpath(a.out)
    for d, what in ((a.project, "PROJECT"), (a.challenge, "CHALLENGE")):
        if d and (out_real == d or out_real.startswith(d + os.sep) or d.startswith(out_real + os.sep)):
            print(f"fastverify: OUT {out_real} must not be inside {what} {d} (or contain it)", file=sys.stderr)
            return 2
    if os.path.exists(a.out) and (not os.path.isdir(a.out) or os.listdir(a.out)):
        print(f"fastverify: OUT {a.out} exists and is not empty (never reuse state: finding 067)", file=sys.stderr)
        return 2
    os.makedirs(a.out, exist_ok=True)
    a.out = os.path.realpath(a.out)
    try:   # OUT is ours and not group / other writable BEFORE anything is created in it
        st = os.stat(a.out)
        if st.st_uid != os.getuid():
            print(f"fastverify: OUT {a.out} is not owned by this user: refused", file=sys.stderr)
            return 2
        os.chmod(a.out, (st.st_mode & 0o7777) & ~0o022)
        if os.stat(a.out).st_mode & 0o022:
            print(f"fastverify: OUT {a.out} keeps group / other write: refused", file=sys.stderr)
            return 2
    except OSError as e:
        print(f"fastverify: OUT {a.out}: {e}", file=sys.stderr)
        return 2
    run = Run(a)
    if a.autotune is not None:
        run.res["autotune"] = a.autotune

    def on_signal(signum, frame):   # stop every running stage tree, record the interruption, no verdict
        if getattr(run, "committing", False):   # the final document is being written: finish it, then exit
            run.deferred_signal = signum
            return
        if getattr(run, "final", False):   # after the final save the process exit equals the recorded one
            if getattr(run, "export_tmpdir", None) and not a.keep_work:
                shutil.rmtree(run.export_tmpdir, ignore_errors=True)
            os._exit(run.res.get("exit") if type(run.res.get("exit")) is int else 2)
        with CHILDREN_LOCK:
            kids = list(CHILDREN)
        for k in kids:
            kill_tree(k)
        try:
            # before the run is final (end-of-run integrity check done + final save) a signal is ERROR,
            # whatever was decided (before: an ACCEPTED decided before the end check was kept although the check never
            # completed); after the final save result.json is left as it is
            if not getattr(run, "final", False):
                # the lock may be held by the interrupted frame (inside save()): never wait forever for it; without it
                # result.json keeps its last, non-final content (PENDING / not finished = no verdict) and the exit is 2
                got = run.lock.acquire(timeout=2)
                try:
                    run.res["interrupted"] = f"signal {signum} at {now_iso()}"
                    if run.res.get("verdict") in ("ACCEPTED", "REJECTED", "CONDITIONAL"):
                        run.res["verdict_interrupted"] = run.res.get("verdict")
                    run.res["verdict"] = "ERROR"
                    run.res["verdict_basis"] = f"interrupted by signal {signum} before the run was final (no verdict)"
                    run.res["exit"] = 2
                finally:
                    if got:
                        run.lock.release()
                run.final = True
                if got:
                    run.save()
        finally:
            if getattr(run, "export_tmpdir", None) and not a.keep_work:   # tmpfs = RAM: never leak it
                shutil.rmtree(run.export_tmpdir, ignore_errors=True)
            os._exit(2)
    import signal as _signal
    for sg in (_signal.SIGTERM, _signal.SIGINT, _signal.SIGHUP):
        if _signal.getsignal(sg) is not _signal.SIG_IGN:   # keep nohup's / the shell's ignores
            _signal.signal(sg, on_signal)
    for d in (run.work, run.logdir, run.tmp, os.path.join(run.tmp, "home")):
        os.makedirs(d, mode=0o700, exist_ok=True)
        os.chmod(d, 0o700)   # private run directories (verified by the snapshot check for tmp)
    rc = 2
    try:
        run.read_inputs()
        run.preflight()
        run.save()
        if a.preflight_only:
            bad = {k: v for k, v in run.available.items() if not v[0]}
            for k, v in sorted(run.available.items()):
                print(f"preflight {k}: {v[1]}")
            run.res["verdict"] = "PREFLIGHT_OK" if not bad else "PREFLIGHT_INCOMPLETE"
            run.res["verdict_basis"] = "preflight only"
            run.res["finished"] = now_iso()
            run.res["exit"] = 0 if not bad else 2   # the process status, as on every other path
            run.save()
            shutil.rmtree(run.tmp, ignore_errors=True)
            print(f"fastverify: preflight {'OK' if not bad else 'INCOMPLETE: ' + ', '.join(sorted(bad))}")
            return 0 if not bad else 2
        run.prepare()
        export = a.export
        if a.notary:   # whenever CN is selected, also with CS: the notary's v0.1
            # kernel scope before the cross-version gate and the build
            run.notary_scope_gate()
        xv = run.xversion_gate() if (a.sound or a.notary) else 0   # veto-only cross-version gate for sound AND notary
        if xv == 1:
            export = None
            run.res["verdict"] = "REJECTED"
            run.res["verdict_fast"] = "REJECTED"
            mode_label = "NOTARY" if (a.notary and not a.sound) else "SOUND"
            run.res["trust"] = "notary" if (a.notary and not a.sound) else "sound"
            run.res["verdict_basis"] = (f"{mode_label}: rejected by the challenge release's own comparator rule (cross-version "
                                        "gate, check/xversion): "
                                        + str((run.res["inputs"]["challenge_export"].get("xversion") or {}).get("reason")))
        elif export:
            if not os.path.isfile(export):
                raise Refuse(f"--export {export} is not a regular file")
            # the checks read the export several times (comparison, each kernel leg); a file the submitter can still
            # write (shared upload dir, NFS, FUSE) could change between those reads. Judge a private copy made ONCE into OUT
            # (reflink where the filesystem supports it), never the caller's file itself.
            given = export
            export = os.path.join(run.out, "solution.export")
            t_cp = time.time()
            cp = subprocess.run(["cp", "--reflink=auto", "--", given, export], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            if cp.returncode != 0 or not os.path.isfile(export):
                raise Refuse(f"--export {given}: cannot make a private copy in OUT ({cp.stderr.decode('utf-8', 'replace').strip()[:200]})")
            os.chmod(export, 0o444)
            run.res["export"] = {"path": export, "given_path": given, "mode": "given (private copy)", "given": True, "exit": 0,
                                 "size": os.path.getsize(export), "copy_seconds": round(time.time() - t_cp, 3)}
        if xv != 1 and not a.export:
            brc = run.build()
            if brc == 1:
                run.res["verdict"] = "REJECTED"
                bl = run.res.get("build") or {}
                run.res["verdict_basis"] = ("build failed (the exact build B1 - official lean, Lake's plan - fails, so the "
                                            "official build fails too)" if bl.get("option") == "B1"
                                            else ("build failed: " + ", ".join(f["module"] for f in bl.get("failed_modules")
                                                                                 or [])[:300]
                                                  + " also fail(s) with the exact official invocation (official lean, "
                                                  "Lake's argv) on the transformed build's imports (sound-auto: no full "
                                                  "exact rebuild; --confirm-build-failure-full forces one)")
                                            if bl.get("confirmed_by") == "exact-retry"
                                            else "build failed in the transformed build B3 (not confirmed: "
                                                 "--no-confirm-build-failure)" if bl.get("option") == "B3"
                                            else "build failed (the official lake build fails)")
            elif brc != 0:
                bl = (run.res.get("build") or {}).get("attempts") or [{}]
                why = ("the transformed build B3 failed and no exact build confirmed it (--no-confirm-build-failure)"
                       if bl[-1].get("unconfirmed") else bl[-1].get("host_failure") or bl[-1].get("report_error"))
                raise Refuse(f"build could not run (exit {brc})" + (f": {why}" if why else ""))   # say why
            else:
                erc = run.export()
                if erc == 1:
                    # the official exporter failing (EFBIG under ulimit -f, I/O error, a crash) is a
                    # TOOL failure, never a judgement of the proof: no verdict. (official_export maps every exporter failure
                    # except 137 / 143 / host errors to 1, incl. the panic 134 of a target the project does not declare; live
                    # reported all of them REJECTED 'export failed'; now all are no verdict, which counts like REJECTED for
                    # rewards)
                    ex_why = resource_failure_evidence([os.path.join(run.logdir, "export_official.log")])
                    absent = None if ex_why else run.export_absence()
                    if absent:
                        # after a successful EXACT build (official lean, Lake's plan)
                        # the official exporter reports that the solution module or a target is ABSENT: the official
                        # comparator fails the same way -> REJECTED (the submission's answer, not a tool failure)
                        run.res["verdict"] = "REJECTED"
                        run.res["verdict_fast"] = "REJECTED"
                        run.res["verdict_basis"] = "export failed: " + absent
                    else:
                        raise Refuse("the official exporter failed (exit 1): a tool / host failure, not a judgement of the "
                                     "proof" + (f" ({ex_why})" if ex_why else ""))
                if erc == 1:   # REJECTED by export_absence above (otherwise refused there)
                    pass
                elif False:
                    run.res["verdict"] = "REJECTED"
                    # (display only) the native exporter's decline reason is the actionable
                    # part, e.g. 'target constant T not found in environment' = the project does not declare theorem T
                    why = ""
                    for at in (run.res.get("export") or {}).get("attempts") or []:
                        st = at.get("stage") if isinstance(at, dict) else None
                        nat = st.get("native") if isinstance(st, dict) else None
                        if isinstance(nat, dict) and nat.get("decline_reason"):
                            why = str(nat["decline_reason"])[:300]
                            break
                    run.res["verdict_basis"] = "export failed (the official lean4export fails)" + (
                        f"; native exporter: {why}" if why else "")
                elif erc != 0:
                    raise Refuse(f"export could not run (exit {erc})")
                else:
                    export = run.res["export"]["path"]
        if export:
            ref = os.path.realpath(a.reference_export) if a.reference_export else None
            if ref and not os.path.isfile(ref):
                raise Refuse(f"--reference-export {ref} is not a regular file")
            hth = run.hash_in_background(export, ref)
            run.hash_threads = hth
            run.save()
            run.checks(export)
            run.finish_hashes(hth)
            run.decide()
            if getattr(a, "confirm_reject", False) and a.sound and not a.export and run.res.get("verdict") == "REJECTED":
                run.confirm_reject()
            elif (a.sound or a.notary) and not a.export and run.res.get("verdict") == "REJECTED":   # unconfirmed
                run.mark_reject_unconfirmed_if_transformed()
            changed = run.verify_components_end()
            if changed:
                run.res["verdict"] = "ERROR"
                run.res["verdict_basis"] = "components changed during the run: " + "; ".join(changed)
                log("ERROR: " + run.res["verdict_basis"])
        rc = {"ACCEPTED": 0, "REJECTED": 1}.get(run.res["verdict"], 2)
        if run.res["verdict"] == "CONDITIONAL" and getattr(a, "modulo_frontier", None):
            rc = 3   # conditional verdict modulo the reported sorry frontier (never 0)
    except Refuse as e:
        run.res["verdict"] = "ERROR"
        run.res["verdict_basis"] = f"refused: {e}"
        log(f"REFUSED: {e}")
        rc = 2
    except Exception as e:  # noqa: BLE001  - any internal error is a non-verdict
        import traceback
        traceback.print_exc()
        run.res["verdict"] = "ERROR"
        run.res["verdict_basis"] = f"internal error: {e!r}"
        rc = 2
    run.overlap_kill()
    try:
        run.await_cs_preflight()   # never leave the deferred preflight running past the run
    except Exception:  # noqa: BLE001
        pass
    if getattr(run, "digest_thread", None) is not None:
        run.digest_thread.join()
    run.res["finished"] = now_iso()
    run.res["exit"] = rc
    run.committing = True   # a signal now is deferred until the final document is on disk
    run.final = True   # the verdict is written as final only now (after decide AND the end-of-run check)
    run.save()
    run.committing = False
    if getattr(run, "deferred_signal", None) is not None:   # exit with the status the final document records
        if getattr(run, "export_tmpdir", None) and not a.keep_work:
            shutil.rmtree(run.export_tmpdir, ignore_errors=True)
        os._exit(rc)
    if not a.keep_work:
        shutil.rmtree(run.work, ignore_errors=True)
        if getattr(run, "export_tmpdir", None):
            shutil.rmtree(run.export_tmpdir, ignore_errors=True)
    shutil.rmtree(run.tmp, ignore_errors=True)
    print(f"fastverify: verdict {run.res['verdict']} ({run.res['verdict_basis']}); official={run.res.get('verdict_official')}"
          f" fast={run.res.get('verdict_fast')}; result {os.path.join(a.out, 'result.json')}")
    return rc


def reset_inherited_signals():
    """bin/fastverify can be started with SIGCHLD ignored (env -i
    keeps dispositions): then every child's exit status reads as 0 (a failing lib/toolchain.py verify passed) and stages
    hang. Reset ONLY what breaks correctness, before anything runs: SIGCHLD -> default and the inherited signal mask
    cleared; SIGTERM -> default so that main() installs its handler (a SIGTERM always ends the run as ERROR). SIGHUP and
    SIGINT keep their inherited disposition (nohup / background jobs behave as before); SIGPIPE / SIGXFSZ stay as the
    interpreter sets them (children get the defaults back through subprocess's restore_signals)."""
    import signal as _sg
    for nm in ("SIGCHLD", "SIGTERM"):
        if hasattr(_sg, nm):
            _sg.signal(getattr(_sg, nm), _sg.SIG_DFL)
    try:
        _sg.pthread_sigmask(_sg.SIG_SETMASK, set())
    except (AttributeError, OSError, ValueError):
        pass


if __name__ == "__main__":
    reset_inherited_signals()
    try:
        sys.exit(main())
    except SystemExit:
        raise
    except Refuse as e:   # refusal before the run could start (e.g. an unconfigured package): no verdict
        print(f"fastverify: REFUSED: {e}", file=sys.stderr)
        sys.exit(2)
    except BaseException:  # noqa: BLE001 - an internal error is never a verdict (exit 1 would read as REJECTED)
        import traceback
        traceback.print_exc()
        sys.exit(2)

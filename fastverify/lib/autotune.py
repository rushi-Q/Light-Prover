#!/usr/bin/env python3
"""fastverify lib/autotune.py - project-shape- and host-tuned choice of the UNTRUSTED build items for
`--preset sound-auto`.

    python3 -I lib/autotune.py PROJECT [--packages WS] [--threads N] [--json]     # what sound-auto would do, and why

Why. `--preset sound` carries the item list measured on the RH proof (175k modules, every module `import Mathlib`). On
other projects several of its items cost time or availability (measured on other projects):
  * the prefix zygote misses on every module that does not start with `import Mathlib` (8-23 % slower on all five real
    projects measured; ~7 s per one-module run);
  * `skip-kernel-tc` breaks Mathlib's translation attributes (`@[to_additive]` / `@[to_dual]` use kernel errors as control
    flow): failed builds -> B1 fallback or a FALSE REJECT of a valid project;
  * module-system projects pay the planner's up-front transitive importArts walk (whole Mathlib 104-135 s, formal-conjectures
    485 s + a 10.8 GB plan) unless `sound-fast-path=importarts-empty` is used;
  * for few-module projects the B3 machinery (unofficial toolchain verification, planner compile, plugins, zygote) costs
    more than the whole official `lake build` (one-theorem proofs: 25 s vs 15 s with `--build B0`; failed attempts 52 s vs 9 s);
  * the RH cost hints, check-tail priorities and the targeted overlap (RH declaration names) only apply to RH;
  * `native-pkg` compiles every C file of the trusted packages with all threads on every run (no cache): CPU stolen from
    the build on small hosts; it gave no measurable gain at 1.6k modules;
  * unofficial toolchain trees that need a newer glibc than the host are verified file by file and then fail to start
    (~6-8 s per run wasted).
This module reads the project's sources as TEXT (headers, a few markers; no project code runs, nothing is built) and the
host's limits, and returns a preset dictionary (build option, B3 item list, orchestrator options, threads) plus every
feature and the reason of every choice; `bin/fastverify --preset sound-auto` records it in result.json ("autotune").

Soundness. Nothing here is trusted. sound-auto always decides with the unchanged trusted check CS (check/sound/
check-sound.sh) against the pinned official challenge export; every item chosen here is an item of `--preset sound`
whose why-sound text is in lib/fastverify.py SOUND_TRANSFORMS, or `--build B0` (the official lake build). A wrong choice
can only make the run slower, make it fall back (B3 -> B1 -> REJECTED as in `--preset sound`) or cause a false reject;
it can never produce an ACCEPT, because the trusted check reads only the export and the official challenge export.
"""
import json
import os
import re
import stat
import sys
import time

T1DIR = "/scratch/fastverify-next/tc"
T1_ORDER = ["lean4-s01zy-3cf5641cbd-pgo", "lean4-d5e35ef223-pgo", "lean4-7586a50cec-nopgo"]   # = --preset sound's order
ZYGOTE_TREE = "lean4-s01zy-3cf5641cbd-pgo"
SOUND_ITEMS = ["skip-kernel-tc", "linter-off", "retries", "premise-off", "fast-exact", "zygote", "zygote-prefix",
               "j1-saturated", "sound-fast-path", "cost-hints", "native-pkg", "merge", "check-tail"]

# thresholds (calibrated on measured runs)
SMALL_MODULES = 4            # <= this many project modules (and no kernel-heavy marker): official lake build (B0) ...
TINY_MODULES, TINY_BYTES = 32, 64 << 10   # ... or <= 32 modules with <= 64 KiB of source in total (calibration)
ZYGOTE_MIN_PREFIX = 256      # zygote only if at least this many modules start with `import Mathlib` ...
ZYGOTE_MIN_SHARE = 0.5       # ... and they are at least this share of all modules (RH: 100 %, real projects: 0-13 %)
MERGE_MIN_MODULES = 2000     # module merging only on large plain-header projects (RH: -229 s at 175k modules) ...
MERGE_CHAIN_MAX_BYTES = 4096  # ... or on long chains of cheap modules (V08 advise.py rule + a size bound for "cheap")
NATIVE_MIN_MODULES = 5000    # native package code only for very long builds with many threads (no gain at 1.6k modules)
NATIVE_MIN_THREADS = 128
ZYGOTE_MIN_MEM = 96 << 30    # zygote / native-pkg only with >= 96 GB: the zygote needs 60-75 GB whatever the thread count
                             # (two zygotes with native-pkg; D09: 32 GB cap -> 26 OOM kills, B3 declined, 3.5x slower)
EXPORT_LOWMEM_PREFER = 16 << 30   # below this budget the low-memory exporter (D15) goes first
COSTHINT_MIN_COVER = 0.5     # RH cost hints / check-tail / targeted overlap only if they name most of the project's modules
GB = 1 << 30

TRANSLATE_RE = re.compile(rb"\bto_(?:additive|dual)\b")
UNFOLD_EXACT_RE = re.compile(rb"with_unfolding_all\s*\(?\s*exact|with_unfolding_all\s+exact")
KERNEL_HEAVY_RE = re.compile(rb"decide\s*\+kernel|\bdecide!|Nat\.decEq|by\s+rfl\b")


# ------------------------------------------------------------------------------------------------------------ host
def _read(path):
    try:
        with open(path) as f:
            return f.read()
    except OSError:
        return None


def cgroup_limits():
    """(cpu_quota_cores or None, memory_max_bytes or None) of this process's cgroup (v2; v1 best effort)."""
    cpu = mem = None
    cg = _read("/proc/self/cgroup") or ""
    for ln in cg.splitlines():
        parts = ln.split(":", 2)
        if len(parts) != 3:
            continue
        hid, ctrl, path = parts
        if hid == "0" and ctrl == "":   # cgroup v2: walk up the hierarchy, the tightest limit wins
            p = "/sys/fs/cgroup" + path
            while p.startswith("/sys/fs/cgroup"):
                m = _read(os.path.join(p, "memory.max"))
                if m and m.strip() not in ("", "max"):
                    v = int(m.strip())
                    mem = v if mem is None else min(mem, v)
                c = _read(os.path.join(p, "cpu.max"))
                if c:
                    q = c.split()
                    if len(q) == 2 and q[0] != "max":
                        v = int(q[0]) / int(q[1])
                        cpu = v if cpu is None else min(cpu, v)
                if p == "/sys/fs/cgroup":
                    break
                p = os.path.dirname(p)
        elif "memory" in ctrl.split(","):
            m = _read("/sys/fs/cgroup/memory" + path + "/memory.limit_in_bytes")
            if m and int(m) < (1 << 60):
                mem = int(m)
    return cpu, mem


def glibc_version():
    try:
        v = os.confstr("CS_GNU_LIBC_VERSION") or ""
        m = re.search(r"(\d+)\.(\d+)", v)
        return (int(m.group(1)), int(m.group(2))) if m else None
    except (ValueError, OSError):
        return None


def _max_version(paths, pat):
    best = None
    for p in paths:
        try:
            with open(p, "rb") as f:
                data = f.read()
        except OSError:
            return None
        for m in re.finditer(pat, data):
            v = int(m.group(1))
            best = v if best is None or v > best else best
    return best


def required_glibc(tree):
    """Highest GLIBC_2.x symbol version named in the tree's lean + libleanshared (read as bytes; nothing is executed)."""
    v = _max_version([os.path.join(tree, r) for r in ("bin/lean", "lib/lean/libleanshared.so")], rb"GLIBC_2\.(\d+)")
    return (2, v) if v is not None else None


def required_glibcxx(tree):
    """Highest GLIBCXX_3.4.N the tree references (dynamic libstdc++; None = none referenced, e.g. static like the release)."""
    v = _max_version([os.path.join(tree, r) for r in ("bin/lean", "lib/lean/libleanshared.so")], rb"GLIBCXX_3\.4\.(\d+)")
    return v


def elf_needed(path):
    """DT_NEEDED entries of an ELF64 little-endian file (parsed from the bytes; nothing is executed). None if unreadable."""
    import struct
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError:
        return None
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        return None
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum = struct.unpack_from("<HH", data, 0x3A)
    secs = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize) for i in range(shnum)]
    out = []
    for name, typ, flags, addr, off, size, link, info, align, entsize in secs:
        if typ != 6:   # SHT_DYNAMIC
            continue
        stroff = secs[link][4]
        for k in range(0, size, 16):
            tag, val = struct.unpack_from("<qQ", data, off + k)
            if tag == 0:
                break
            if tag == 1:   # DT_NEEDED
                end = data.index(b"\0", stroff + val)
                out.append(data[stroff + val:end].decode("ascii", "replace"))
    return out


_HOST_LIBS = None


def host_has_lib(name, extra_dirs=()):
    """The dynamic loader would find `name`: in the tree's own lib dirs, the ld.so cache or the standard directories."""
    global _HOST_LIBS
    for d in extra_dirs:
        if os.path.exists(os.path.join(d, name)):
            return True
    if _HOST_LIBS is None:
        import subprocess
        _HOST_LIBS = set()
        try:
            r = subprocess.run(["/sbin/ldconfig", "-p"], capture_output=True, text=True, timeout=10)
            for ln in r.stdout.splitlines():
                t = ln.strip().split(" ", 1)
                if t and t[0]:
                    _HOST_LIBS.add(t[0])
        except (OSError, subprocess.SubprocessError):
            pass
    if name in _HOST_LIBS:
        return True
    return any(os.path.exists(os.path.join(d, name)) for d in (
        "/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu", "/lib64", "/usr/lib64", "/lib", "/usr/lib", "/usr/local/lib"))


def missing_libs(tree):
    """Shared libraries the tree's lean / libleanshared need that this host cannot provide (D21: libuv, OpenSSL 3, GMP...)."""
    own = [os.path.join(tree, "lib", "lean"), os.path.join(tree, "lib")]
    miss = set()
    for rel in ("bin/lean", "lib/lean/libleanshared.so"):
        for n in elf_needed(os.path.join(tree, rel)) or []:
            if not host_has_lib(n, own):
                miss.add(n)
    return sorted(miss)


def host_glibcxx():
    """Highest GLIBCXX_3.4.N the host's libstdc++.so.6 provides (None if no libstdc++ is found)."""
    for p in ("/usr/lib/x86_64-linux-gnu/libstdc++.so.6", "/usr/lib64/libstdc++.so.6", "/lib/x86_64-linux-gnu/libstdc++.so.6",
              "/usr/lib/libstdc++.so.6"):
        if os.path.exists(p):
            return _max_version([os.path.realpath(p)], rb"GLIBCXX_3\.4\.(\d+)")
    return None


def t1_candidates(pkgroot=None):
    """Unofficial build toolchain trees to consider, best first: the sound preset's measured order, then any other pinned
    manifest in toolchains/unofficial/ (e.g. future portable rebuilds) by class: zygote PGO, PGO, non-PGO."""
    names = list(T1_ORDER)
    if pkgroot:
        try:
            names += sorted(f[:-5] for f in os.listdir(os.path.join(pkgroot, "toolchains", "unofficial"))
                            if f.endswith(".json") and f[:-5] not in names)
        except OSError:
            pass
    # class first (zygote PGO > PGO > non-PGO: a startable faster tree wins over a slower measured one, e.g. D21's portable
    # rebuilds on glibc-2.35 hosts), then the sound preset's measured trees before other pinned ones, then by name
    cls = lambda n: 0 if "-s01zy-" in n else 1 if ("-pgo" in n and "nopgo" not in n) else 2
    return sorted(names, key=lambda n: (cls(n), 0 if n in T1_ORDER else 1, n))


# T1 tree probe cache (untrusted: only steers the choice; build.sh verifies every tree and its start itself). Reading the
# tree binaries for their GLIBC versions costs ~1-2 s per run; the result only changes when those files or the host's
# libraries change, so it is kept per user in a private directory, keyed by the files' stamps and the host's libc / libstdc++
# / ld.so.cache. An unusable directory (not ours, not 0700, a symlink) or file -> no cache, the probe runs as before.
PROBE_VERSION = 1
_PROBED = ("bin/lean", "lib/lean/libleanshared.so")


def _stamp(p):
    try:
        st = os.stat(p)
        return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]
    except OSError:
        return None


def _probe_cache_dir():
    import stat as _st
    d = os.path.join("/tmp", "fastverify-autotune-%d" % os.getuid())
    try:
        os.mkdir(d, 0o700)
    except FileExistsError:
        pass
    except OSError:
        return None
    try:
        st = os.lstat(d)
    except OSError:
        return None
    if not _st.S_ISDIR(st.st_mode) or st.st_uid != os.getuid() or (st.st_mode & 0o077):
        return None
    return d


def _probe_cache_load():
    d = _probe_cache_dir()
    if not d:
        return {"dir": None}
    try:
        fd = os.open(os.path.join(d, "t1probe.json"), os.O_RDONLY | os.O_NOFOLLOW)
        with os.fdopen(fd, encoding="utf-8") as f:
            if os.fstat(f.fileno()).st_uid != os.getuid():
                return {"dir": d}
            data = json.load(f)
        if isinstance(data, dict) and isinstance(data.get("trees"), dict):
            return {"dir": d, "trees": {k: v for k, v in data["trees"].items() if isinstance(v, dict)}}
    except (OSError, ValueError):
        pass
    return {"dir": d}


def _probe_cache_save(cache):
    if not cache.get("dir") or not cache.get("dirty"):
        return
    import tempfile
    try:
        fd, tmp = tempfile.mkstemp(prefix=".t1probe.", dir=cache["dir"])
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump({"trees": dict(list(cache["trees"].items())[-64:])}, f)
        os.replace(tmp, os.path.join(cache["dir"], "t1probe.json"))
    except OSError:
        pass


def host_info(pkgroot=None):
    cpus = len(os.sched_getaffinity(0))
    quota, cg_mem = cgroup_limits()
    if quota:
        cpus = max(1, min(cpus, int(quota)))
    mem_total = mem_avail = None
    for ln in (_read("/proc/meminfo") or "").splitlines():
        k, _, v = ln.partition(":")
        if k == "MemTotal":
            mem_total = int(v.split()[0]) * 1024
        elif k == "MemAvailable":
            mem_avail = int(v.split()[0]) * 1024
    mem_budget = min(x for x in (mem_avail, cg_mem) if x) if (mem_avail or cg_mem) else None
    try:
        st = os.statvfs("/dev/shm")
        shm_free = st.f_bavail * st.f_frsize
    except OSError:
        shm_free = 0
    g = glibc_version()
    hx = host_glibcxx()
    trees = {}
    cache = _probe_cache_load()
    for n in t1_candidates(pkgroot):
        d = os.path.join(T1DIR, n)
        if not os.path.isdir(d):
            trees[n] = {"present": False}
            continue
        key = json.dumps([d, [_stamp(os.path.join(d, r)) for r in _PROBED], g, hx, _stamp("/etc/ld.so.cache"),
                          PROBE_VERSION])
        if key in cache.get("trees", {}):   # same files (dev, inode, size, mtime, ctime) on the same host libraries
            trees[n] = dict(cache["trees"][key], cached=True)
            continue
        req = required_glibc(d)
        rx = required_glibcxx(d)
        ok_cxx = rx is None or (hx is not None and hx >= rx)
        miss = missing_libs(d)
        trees[n] = {"present": True, "glibc_required": "%d.%d" % req if req else None,
                    "glibcxx_required": "3.4.%d" % rx if rx is not None else None, "missing_libs": miss,
                    "starts": bool(g and req and g >= req and ok_cxx and not miss)}
        cache.setdefault("trees", {})[key] = trees[n]
        cache["dirty"] = True
    _probe_cache_save(cache)
    try:
        load1 = os.getloadavg()[0]
    except OSError:
        load1 = None
    return {"cpus": cpus, "load1": load1, "online_cpus": os.cpu_count(), "cpu_quota": quota, "mem_total": mem_total,
            "mem_available": mem_avail, "cgroup_mem_max": cg_mem,
            "mem_budget": mem_budget, "shm_free": shm_free, "glibc": "%d.%d" % g if g else None,
            "glibcxx": "3.4.%d" % hx if hx is not None else None, "t1_trees": trees}


# ------------------------------------------------------------------------------------------------------------ project
def _tokens(text):
    """Header tokens of a Lean file (comments skipped), stopping after the import block."""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if text.startswith("/-", i):
            depth = 0
            while i < n:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            continue
        if c == "«":   # escaped identifier part: read to the closing guillemet, then the rest of the name
            j = i
            while j < n and not text[j].isspace():
                if text[j] == "«":
                    k = text.find("»", j)
                    j = n if k < 0 else k + 1
                else:
                    j += 1
            yield text[i:j]
            i = j
            continue
        j = i
        while j < n and not text[j].isspace() and not text.startswith("--", j) and not text.startswith("/-", j):
            j += 1
        yield text[i:j]
        i = j


def parse_header(text):
    """-> (module_system, prelude, [imports]) for the header of a Lean 4 file."""
    toks = _tokens(text)
    mod = pre = False
    imports = []
    pending_import = False
    for t in toks:
        if pending_import:
            if t == "all":
                continue
            imports.append(t)
            pending_import = False
            continue
        if t == "module" and not imports and not pre and not mod:
            mod = True
        elif t == "prelude" and not imports:
            pre = True
        elif t in ("public", "meta", "private"):
            continue
        elif t == "import":
            pending_import = True
        else:
            break
    return mod, pre, imports


# ---- project confinement ---------------------------------------------------------------------------------------------
# This module runs on the HOST before any sandbox (bin/fastverify --preset sound-auto at CLI parse time, MCP fv_doctor /
# fv_verify_project, bin/fv verify, fv-ci.sh), on an UNTRUSTED project. It must never read outside the project: every path
# taken from the project's files (lakefile.toml srcDir) must be relative without '..' (else ValueError: the caller falls
# back to the sound preset / reports no plan), every directory it walks and every file it reads must BE inside the project
# (realpath under the project root; files checked on the opened descriptor via /proc/self/fd), and only regular files are
# read (FIFOs/devices/sockets are skipped and opened O_NONBLOCK, grep runs with -D skip: nothing can block the host).
class ProjectEscape(ValueError):
    pass


def _has_ctl(s):
    return any(ord(c) < 0x20 or 0x7f <= ord(c) <= 0x9f for c in s)


def _inside(path, rroot):
    """path (after resolving every symlink) is the project root or strictly inside it"""
    rp = os.path.realpath(path)
    return rp == rroot or rp.startswith(rroot + os.sep)


def _clean_srcdir(src):
    if not isinstance(src, str) or _has_ctl(src) or os.path.isabs(src) or src.startswith("~") \
            or ".." in src.replace("\\", "/").split("/"):
        raise ProjectEscape(f"lakefile.toml srcDir {src!r} is not a relative path inside the project")
    return src


def _open_inside(path, rroot):
    """fd of the regular file `path` if the opened file IS inside rroot (race-free: checked on the descriptor), else None"""
    # (r2, review L4) O_PATH first: nothing is opened for reading before the descriptor is known to be a regular file
    # inside the project; then re-opened through that descriptor (race-free)
    try:
        pfd = os.open(path, os.O_PATH | os.O_CLOEXEC)
    except OSError:
        return None
    try:
        if stat.S_ISREG(os.fstat(pfd).st_mode) and os.readlink(f"/proc/self/fd/{pfd}").startswith(rroot + os.sep):
            return os.open(f"/proc/self/fd/{pfd}", os.O_RDONLY | os.O_NONBLOCK | os.O_NOCTTY | os.O_CLOEXEC)
    except OSError:
        pass
    finally:
        os.close(pfd)
    return None


def _read_proj(proj, name, limit=1 << 22):
    """text of the regular file PROJECT/name, or None (missing, not a regular file, or resolving outside the project)"""
    fd = _open_inside(os.path.join(proj, name), os.path.realpath(proj))
    if fd is None:
        return None
    with os.fdopen(fd, "rb") as f:
        return f.read(limit).decode("utf-8", "replace")


def _lakefile_libs(proj):
    """[(name, srcDir, roots, globs)] of [[lean_lib]] tables of a lakefile.toml (tiny parser: strings and string arrays).
    Every srcDir must be a relative path without '..' (ProjectEscape otherwise)."""
    text = _read_proj(proj, "lakefile.toml")
    if text is None:
        return None
    libs, cur, key, buf = [], {"_t": None}, None, None
    top = cur
    for raw in text.splitlines():
        ln = raw.split("#", 1)[0].strip() if '"' not in raw else raw.strip()
        if buf is not None:
            buf += " " + ln
            if "]" in ln:
                cur[key] = re.findall(r'"([^"]*)"', buf)
                buf = None
            continue
        if not ln:
            continue
        if ln.startswith("[["):
            cur = {"_t": ln.strip("[] ")}
            libs.append(cur)
            continue
        if ln.startswith("["):
            cur = {"_t": ln.strip("[] ")}
            continue
        if "=" not in ln:
            continue
        key, _, val = ln.partition("=")
        key, val = key.strip(), val.strip()
        if val.startswith("[") and "]" not in val:
            buf = val
            continue
        if val.startswith("["):
            cur[key] = re.findall(r'"([^"]*)"', val)
        elif val.startswith('"'):
            m = re.match(r'"([^"]*)"', val)
            cur[key] = m.group(1) if m else val
        else:
            cur[key] = val
    out = []
    pkg_src = _clean_srcdir(top.get("srcDir", "."))
    for t in libs:
        if t.get("_t") == "lean_lib" and t.get("name"):
            src = os.path.join(pkg_src, _clean_srcdir(t["srcDir"])) if t.get("srcDir") else pkg_src
            out.append((t["name"], src, t.get("roots") or [t["name"]], t.get("globs") or []))
    return out


def _walk_lean(base, skip_root_lakefile=False, root=None):
    """.lean files below base (hidden dirs and dir symlinks skipped) -> {module: path}. Confined: base must resolve
    inside the project root (else nothing), the walk runs over the RESOLVED base (so every directory visited is a real
    directory inside the project: os.walk never descends a directory symlink), a file symlink is taken only if it resolves
    inside the project root (its resolved path is recorded), and only regular files are taken (no FIFO/device/socket)."""
    out = {}
    rroot = os.path.realpath(root or base)
    if not _inside(base, rroot):
        return out
    rbase = os.path.realpath(base)
    for dp, dns, fns in os.walk(rbase):
        dns[:] = [x for x in dns if not x.startswith(".") and x not in ("lake-packages",)]
        for fn in fns:
            if fn.endswith(".lean") and not (skip_root_lakefile and dp == rbase and fn == "lakefile.lean"):
                full = os.path.join(dp, fn)
                try:
                    st = os.lstat(full)
                    path = full
                    if stat.S_ISLNK(st.st_mode):
                        path = os.path.realpath(full)
                        if not path.startswith(rroot + os.sep):
                            continue
                        st = os.lstat(path)
                except OSError:
                    continue
                if not stat.S_ISREG(st.st_mode):
                    continue
                out.setdefault(os.path.relpath(full, rbase)[:-5].replace(os.sep, "."), path)
    return out


def _module_files(proj):
    """-> (universe {module: path}, start modules or None, how). universe = every .lean file under the srcDirs of the
    lakefile.toml libraries; start = the modules `lake build` starts from (the default targets' roots / glob matches);
    the build set is their import closure inside the universe (computed by the caller from the headers)."""
    libs = _lakefile_libs(proj)
    if not libs:
        return _walk_lean(proj, True, proj), None, "walk"
    text = _read_proj(proj, "lakefile.toml") or ""
    m = re.search(r"(?m)^\s*defaultTargets\s*=\s*\[([^\]]*)\]", text)
    default = re.findall(r'"([^"]*)"', m.group(1)) if m else None
    universe, start = {}, []
    rroot = os.path.realpath(proj)
    for name, src, roots, globs in libs:
        base = os.path.normpath(os.path.join(proj, src))
        if not _inside(base, rroot):   # a srcDir that is (or runs through) a symlink leaving the project
            raise ProjectEscape(f"lakefile.toml srcDir {src!r} resolves outside the project")
        files = _walk_lean(base, base == os.path.normpath(proj), proj)
        for k, v in files.items():
            universe.setdefault(k, v)
        if default is not None and name not in default:
            continue
        for r in roots:
            if r in files:
                start.append(r)
        for g in globs:
            if g.endswith(".*") or g.endswith(".+"):
                pre = g[:-2]
                start += [k for k in files if k.startswith(pre + ".") or (g.endswith(".*") and k == pre)]
            elif g in files:
                start.append(g)
    return universe, sorted(set(start)), "lakefile.toml"


def _grep_marks(files, only=None):
    """{path: set(marker)} for the translate / unfold-exact / kernel-heavy markers, via grep -l (C speed). The file list is
    passed in a temporary file (xargs -a), so no pipe is written while another is read (no deadlock on huge trees)."""
    import subprocess, tempfile
    pats = {"translate": ["-E", r"\bto_(additive|dual)\b"], "unfold_exact": ["-F", "with_unfolding_all"],
            "kernel_heavy": ["-E", r"decide[[:space:]]*\+kernel|decide!"],
            # premise selection at elaboration: `grind +suggestions` / library suggestions read the very
            # metadata premise-off removes (such builds fail under premise-off)
            # any occurrence of the word, so `(suggestions :=` + `true)` on
            # two lines counts too: over-inclusive, it only drops premise-off
            "suggestions": ["-E", r"[Ss]uggestions"],
            "adddecl": ["-E", r"\baddDecl\b|\baddAndCompile\b"]}
    if only is not None:
        pats = {k: v for k, v in pats.items() if k in only}
    out = {}
    if not files:
        return out
    with tempfile.NamedTemporaryFile("wb", prefix="fv-autotune.", delete=False) as tf:
        tf.write("\0".join(files).encode("utf-8", "surrogateescape") + b"\0")
        lst = tf.name
    try:
        for k, p in pats.items():
            r = subprocess.run(["xargs", "-0", "-a", lst, "-n", "2000", "-P", "8", "grep", "-l", "-s", "-D", "skip"] + p + ["--"],
                               stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            for ln in r.stdout.decode("utf-8", "surrogateescape").splitlines():
                out.setdefault(ln, set()).add(k)
    finally:
        os.unlink(lst)
    return out


def _header_of(f, max_header, rroot=None):
    try:
        if rroot is not None:   # only a regular file that IS inside the project (checked on the descriptor)
            fd = _open_inside(f, rroot)
            if fd is None:
                return None
        else:
            fd = os.open(f, os.O_RDONLY | os.O_NONBLOCK)
        try:
            size = os.fstat(fd).st_size
            data = os.read(fd, max_header)
        finally:
            os.close(fd)
    except OSError:
        return None
    ms, pre, imps = parse_header(data.decode("utf-8", errors="replace"))
    return size, ms, pre, imps


def scan_project(proj, max_header=16384):
    t0 = time.time()
    rroot = os.path.realpath(proj)
    universe, start, how = _module_files(proj)
    from concurrent.futures import ThreadPoolExecutor
    if start is not None:   # the build set = import closure of the default targets' start modules inside the project
        heads = {}
        frontier = [m for m in start if m in universe]
        with ThreadPoolExecutor(max_workers=min(32, (os.cpu_count() or 4))) as ex:
            while frontier:
                new = [m for m in frontier if m not in heads]
                for m, h in zip(new, ex.map(lambda x: _header_of(universe[x], max_header, rroot), new)):
                    heads[m] = h
                frontier = sorted({i for m in new if heads[m] for i in heads[m][3] if i in universe and i not in heads})
        files = {m: universe[m] for m in heads if heads[m] is not None}
        how += f" (default-target closure of {len(start)} start modules; {len(universe)} files in the srcDirs)"
    else:
        files = universe
    marks = _grep_marks(list(files.values()))

    if start is None:
        with ThreadPoolExecutor(max_workers=min(32, (os.cpu_count() or 4))) as ex:
            heads = dict(zip(files, ex.map(lambda x: _header_of(files[x], max_header, rroot), list(files))))

    def one(item):
        mod, f = item
        h = heads.get(mod)
        if h is None:
            return mod, None
        size, ms, pre, imps = h
        m = marks.get(f, ())
        return mod, {"bytes": size, "module_system": ms, "prelude": pre, "imports": imps,
                     "translate": "translate" in m, "unfold_exact": "unfold_exact" in m, "kernel_heavy": "kernel_heavy" in m,
                     "suggestions": "suggestions" in m,
                     "adddecl": "adddecl" in m}

    info = {m: r for m, r in map(one, sorted(files.items())) if r is not None}
    n = len(info)
    first_mathlib = sum(1 for r in info.values() if r["imports"][:1] == ["Mathlib"] and not r["module_system"])
    any_mathlib = sum(1 for r in info.values() if any(i == "Mathlib" or i.startswith("Mathlib.") for i in r["imports"]))
    # import depth over project-internal edges (longest chain, iterative)
    internal = {m: [i for i in r["imports"] if i in info] for m, r in info.items()}
    depth = {}
    for m in internal:
        if m in depth:
            continue
        stack = [(m, iter(internal[m]))]
        onstack = {m}
        while stack:
            node, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                stack.pop()
                onstack.discard(node)
                depth[node] = 1 + max((depth.get(d, 0) for d in internal[node]), default=0)
                continue
            if nxt in depth or nxt in onstack:
                continue
            onstack.add(nxt)
            stack.append((nxt, iter(internal[nxt])))
    # (D04, E34; D17 15:20Z) modules whose import CLOSURE holds the whole of Mathlib: compressed trees (import reduction) keep
    # Mathlib only transitively, so 'starts with import Mathlib' undercounts them; the zygote serves them all the same
    full = {m: r["imports"][:1] == ["Mathlib"] or "Mathlib" in r["imports"] for m, r in info.items()}
    order = sorted(info, key=lambda m: depth.get(m, 0))   # dependencies first (depth = longest internal chain)
    for m in order:
        if not full[m] and any(full.get(d_, False) for d_ in internal[m]):
            full[m] = True
    closure_mathlib = sum(1 for m, r in info.items() if full[m] and not r["module_system"])
    # ... and those the PREFIX zygote serves: the import walk starts with Mathlib's closure exactly when the first import is
    # Mathlib or an internal module whose walk starts with it (build/README.md: any other import is a prefix miss)
    pre = {}
    for m in order:
        f0 = info[m]["imports"][:1]
        pre[m] = bool(f0) and (f0[0] == "Mathlib" or pre.get(f0[0], False))
    prefix_mathlib = sum(1 for m, r in info.items() if pre[m] and not r["module_system"])
    translate = sorted(m for m, r in info.items() if r["translate"])
    nimp = {m: 0 for m in info}
    for m, deps in internal.items():
        for d_ in deps:
            nimp[d_] += 1
    single = sum(1 for m in info if nimp[m] == 1)
    sizes = sorted(r["bytes"] for r in info.values())
    median_bytes = sizes[len(sizes) // 2] if sizes else 0
    lakefile = "toml" if _read_proj(proj, "lakefile.toml", 0) is not None else (
        "lean" if _read_proj(proj, "lakefile.lean", 0) is not None else None)
    tc = (_read_proj(proj, "lean-toolchain", 4096) or "").strip()
    return {
        "modules": n, "module_files_from": how, "bytes": sum(r["bytes"] for r in info.values()),
        "module_system": sum(1 for r in info.values() if r["module_system"]),
        "first_import_Mathlib": first_mathlib, "imports_Mathlib": any_mathlib, "closure_Mathlib": closure_mathlib,
        "prefix_Mathlib": prefix_mathlib,
        "import_depth": max(depth.values(), default=0), "single_importer_modules": single, "median_module_bytes": median_bytes,
        "translate_modules": len(translate), "translate_examples": translate[:5],
        "unfold_exact_modules": sum(1 for r in info.values() if r["unfold_exact"]),
        "kernel_heavy_modules": sum(1 for r in info.values() if r["kernel_heavy"]),
        "adddecl_modules": sum(1 for r in info.values() if r["adddecl"]),
        # counted over EVERY .lean file of the project, not only the
        # default-target closure scanned above: the B3 build may build another closure (the configured module's)
        # plus the configured srcDirs' files (universe), which the project walk
        # skips when a srcDir is a dot directory (srcDir = ".proofs")
        "suggestions_modules": len(_grep_marks(sorted(set(_walk_lean(proj, False, proj).values()) | set(universe.values())),
                                               only=("suggestions",))),
        "lakefile": lakefile, "toolchain": tc, "scan_seconds": round(time.time() - t0, 3),
        "_names": set(info),
    }


def hint_cover(names, hints_path):
    """Share of the project's modules that a cost-hint file (gzip JSON {module: cost}) names."""
    if not names:
        return 0.0
    try:
        import gzip
        with gzip.open(hints_path, "rt") as f:
            d = json.load(f)
    except (OSError, ValueError):
        return 0.0
    keys = d.keys() if isinstance(d, dict) else []
    hit = sum(1 for k in keys if k in names)
    return hit / len(names)


# ------------------------------------------------------------------------------------------------------------ decide
def _commit_of_release(tc, pkgroot):
    """The commit hash of an official release from its pinned manifest's version line (no execution)."""
    if not (tc and pkgroot):
        return None
    d = tc.split(":", 1)[-1] if ":" in tc else tc
    man = os.path.join(pkgroot, "toolchains", tc.replace("/", "--").replace(":", "---") + ".json")
    try:
        with open(man) as f:
            v = json.load(f).get("lean_version") or ""
    except (OSError, ValueError):
        return None
    m = re.search(r"commit ([0-9a-f]{40})", v)
    return m.group(1) if m else None


def fast_build_release_ok(tc, pkgroot):
    """True iff build/build.sh lists the release's Lake commit among the ones its planner was validated against
    (VALIDATED_LAKE / SOUND_LAKE* lines); without a package root: only v4.33.1 (the original planner port)."""
    if not pkgroot:
        return tc == "leanprover/lean4:v4.33.1"
    commit = _commit_of_release(tc, pkgroot)
    if not commit:
        return False
    try:
        with open(os.path.join(pkgroot, "build", "build.sh")) as f:
            txt = f.read()
    except OSError:
        return tc == "leanprover/lean4:v4.33.1"
    ok = set()
    for ln in txt.splitlines():
        if re.match(r"\s*(VALIDATED_LAKE|SOUND_LAKE)\w*=", ln):
            ok.update(re.findall(r"\b[0-9a-f]{40}\b", ln.split("#", 1)[0]))
    return commit in ok


def tree_base(name, pkgroot):
    """The official release an unofficial T1 tree was built from (its manifest's 'base'; unknown -> v4.33.1, the release
    of every tree measured so far)."""
    if pkgroot:
        try:
            with open(os.path.join(pkgroot, "toolchains", "unofficial", name + ".json")) as f:
                b = json.load(f).get("base")
            if b:
                return b
        except (OSError, ValueError):
            pass
    return "leanprover/lean4:v4.33.1"


def decide(feat, host, threads_given=None, pkgroot=None):
    """-> {"build", "unsafe", "options", "threads", "reasons": {item: why}, "dropped": {item: why}}"""
    reasons, dropped = {}, {}
    n = feat["modules"]
    cpus = host["cpus"]
    threads = threads_given or cpus
    load, online = host.get("load1"), host.get("online_cpus") or cpus
    if not threads_given and load is not None and load > 0.25 * online:
        # a shared host (other jobs): leave the busy cores to them - thread counts never change a verdict
        free = int(min(cpus, online - load))
        cap = max(min(cpus, 8), free)
        if cap < threads:
            reasons["threads_load"] = f"node busy (load {load:.0f} on {online} CPUs): {threads} -> {cap} threads"
            threads = cap
    whole = max(feat["first_import_Mathlib"], feat.get("closure_Mathlib", 0)) >= 0.5 * max(n, 1)   # (D04, E34)
    if not threads_given and host.get("mem_budget"):
        # memory per concurrent lean (cgroup memory.peak, page cache of the shared .olean maps counted once): ~1 GB for
        # selective Mathlib imports (PNT, 8 CPUs + 16 GB: peak 5.2 GB at 6 leans, D04), ~2 GB when most modules import all of
        # Mathlib (rh-miniF plain leans, D09); keep 4 GB for the rest (scheduler, exporter, page cache)
        per = 2 if whole else 1
        cap = max(1, int((host["mem_budget"] - 4 * GB) // (per * GB)))
        if cap < threads:
            reasons["threads"] = f"{threads} CPUs but memory budget {host['mem_budget'] / GB:.0f} GB -> {cap} threads (~{per} GB per lean)"
            threads = cap
    opts = {"export_dir": "none", "overlap_targets": "none", "build_cache": "/tmp/fastverify-build-cache-%d" % os.getuid()}
    tc = feat.get("toolchain", "")
    build, why_b0 = "B3", None
    if tc and not fast_build_release_ok(tc, pkgroot):
        why_b0 = (f"toolchain {tc}: build/build.sh's planner is not validated for this release's Lake -> official lake "
                  "build (B0) directly")
    elif feat.get("lakefile") == "lean":
        why_b0 = "root lakefile.lean: the Lake-planned builds decline it (072) -> official lake build (B0) directly"
    elif feat["kernel_heavy_modules"] == 0 and (n <= SMALL_MODULES or (n <= TINY_MODULES and feat["bytes"] <= TINY_BYTES)):
        why_b0 = (f"{n} module(s), {feat['bytes'] // 1024} KiB of source: the B3 machinery's fixed cost (toolchain "
                  "verification, planner, plugins, zygote) exceeds what it saves (one-theorem proofs 25 s vs 15 s, failed "
                  "attempts 52 s vs 9 s, V01; 17/33 tiny modules at 16 threads: B0 29/33 s vs B3 36/43 s, D04) -> official "
                  "lake build B0 + E1 + the trusted check")
    if why_b0:
        build = "B0"
        reasons["build"] = why_b0 + " (the B3 item list below applies only with an explicit --build B3)"
    items = []
    # unofficial toolchain: only trees whose glibc requirement the host meets (others are verified, then fail to start)
    order = list(host["t1_trees"]) if host.get("t1_trees") else list(T1_ORDER)
    rel = tc or "leanprover/lean4:v4.33.1"
    other = [t for t in order if tree_base(t, pkgroot) != rel]   # a tree of another release would build other .oleans
    order = [t for t in order if t not in other]
    startable = [t for t in order if host["t1_trees"].get(t, {}).get("starts")]
    if startable:
        items.append("toolchain-T1=" + " ".join(startable))
        reasons["toolchain-T1"] = "trees that can start on this host (glibc %s): %s" % (host.get("glibc"), ", ".join(startable))
        skipped = [t for t in order if t not in startable and host["t1_trees"].get(t, {}).get("present")]
        if skipped:
            reasons["toolchain-T1"] += "; not tried (glibc/GLIBCXX too old or shared libraries missing): " + ", ".join(skipped)
    else:
        dropped["toolchain-T1"] = ("no pinned unofficial tree of %s can start here -> official lean" % rel
                                   + (" (trees of other releases: %s)" % ", ".join(other) if other else ""))
    ktc_gate = False
    if pkgroot:
        try:
            with open(os.path.join(pkgroot, "build", "build.sh")) as f:
                ktc_gate = "skip-kernel-tc=except-translate" in f.read()
        except OSError:
            pass
    if feat["translate_modules"] and ktc_gate:
        items.append("skip-kernel-tc=except-translate")
        reasons["skip-kernel-tc"] = (f"per module: the {feat['translate_modules']} module(s) that use @[to_additive]/@[to_dual] "
                                     f"(e.g. {', '.join(feat['translate_examples'][:3])}) keep the build-time kernel check "
                                     "(Mathlib's translation uses kernel errors as control flow: G1-ML-1/2), all others skip it")
    elif feat["translate_modules"]:
        dropped["skip-kernel-tc"] = (f"{feat['translate_modules']} module(s) use @[to_additive]/@[to_dual] (e.g. "
                                     f"{', '.join(feat['translate_examples'][:3])}): Mathlib's translation uses kernel errors "
                                     "as control flow -> skipping the build-time kernel check gives failed builds or a false "
                                     "reject (G1-ML-1/2); this package has no per-module gate")
    else:
        items.append("skip-kernel-tc")
        reasons["skip-kernel-tc"] = "no translation attributes in the project; the trusted kernels re-check every declaration"
    items += ["linter-off", "retries"]
    reasons["linter-off"] = "linters only produce messages (~1/3 of heavy-module CPU)"
    reasons["retries"] = "a module failing under the transforms is rebuilt once with the exact invocation"
    if feat.get("suggestions_modules"):   # premise selection is used: keep its metadata
        dropped["premise-off"] = (f"{feat['suggestions_modules']} module(s) use library suggestions (e.g. grind "
                                  "+suggestions), which need the premise-selection metadata premise-off removes")
    else:
        items.append("premise-off")
        reasons["premise-off"] = "no premise-selection metadata at .olean write (RH chain modules -50..-90 %)"
    if feat["unfold_exact_modules"]:
        items.append("fast-exact")
        reasons["fast-exact"] = f"{feat['unfold_exact_modules']} module(s) use with_unfolding_all exact"
    else:
        dropped["fast-exact"] = "no `with_unfolding_all exact` in the project: the plugin compile (~2 s) buys nothing"
    zy_tree = any(v.get("starts") for k, v in host["t1_trees"].items() if "-s01zy-" in k and k in order)
    f1 = feat["first_import_Mathlib"]
    fm = max(f1, feat.get("prefix_Mathlib", 0))   # (D04, E34) walk starts with Mathlib's closure (compressed trees too)
    mem = host.get("mem_budget") or 0
    if zy_tree and fm >= ZYGOTE_MIN_PREFIX and fm >= ZYGOTE_MIN_SHARE * n and mem >= ZYGOTE_MIN_MEM:
        items += ["zygote", "zygote-prefix"]
        reasons["zygote"] = (f"{fm} of {n} modules reach `import Mathlib` first ({f1} directly, the rest through their "
                             "first import; RH-like): the forked prefix zygote pays (compressed C3c: --preset sound with the "
                             "zygote 1,703 s vs 2,471.6 s without, AMD, D17)")
    else:
        dropped["zygote"] = (f"{fm} of {n} modules reach `import Mathlib` first ({f1} directly)" + ("" if zy_tree else
                             "; no zygote-capable toolchain on this host") + (f"; memory budget {mem / GB:.0f} GB < "
                             f"{ZYGOTE_MIN_MEM // GB} GB (the zygote's materialized Mathlib: 60-75 GB, D09)" if mem < ZYGOTE_MIN_MEM else "")
                             + ": prefix misses cost 8-23 % on real projects (V02), ~7 s on one-module runs (V01)")
    items.append("j1-saturated")
    reasons["j1-saturated"] = "-j1 for a module only while every slot is busy (harmless since G1-ML-3's fix)"
    closure_ok = False
    if pkgroot:
        try:
            with open(os.path.join(pkgroot, "build", "build.sh")) as f:
                closure_ok = "closure-only=" in f.read()
        except OSError:
            pass
    if closure_ok:
        items.append("closure-only")
        reasons["closure-only"] = ("only the import closure of the comparator's solution module is built (A05/A03, D22): "
                                   "what the export and the trusted check read; modules the solution never imports are "
                                   "skipped and cannot fail the build (the community RH main: 2,334 such files)")
    else:
        dropped["closure-only"] = "this package's build.sh has no closure-only item"
    if feat["module_system"]:
        items.append("sound-fast-path=importarts-empty")
        reasons["sound-fast-path"] = (f"{feat['module_system']} module-system file(s): no up-front transitive importArts walk "
                                      "(whole Mathlib planner 104-135 s -> <1 s; formal-conjectures 485 s; G1-ML-4)")
    else:
        items.append("sound-fast-path")
        reasons["sound-fast-path"] = "skips exactness-only guards (plancheck, Lake dependency check, source digests)"
    cover = 0.0
    if pkgroot:
        cover = hint_cover(feat.get("_names", set()), os.path.join(pkgroot, "build", "hints", "rh-build-costs.json.gz"))
    if cover >= COSTHINT_MIN_COVER:
        items += ["cost-hints", "check-tail"]
        reasons["cost-hints"] = f"the RH cost hints name {cover:.0%} of the modules"
        # targeted overlap NOT auto-selected (measured gain ~0 s on RH)
        dropped["overlap"] = "targeted overlap disabled by default ('--overlap-targets FILE' enables it)"
    else:
        dropped["cost-hints"] = f"the packaged cost hints (RH) name {cover:.0%} of the modules: no data for this project"
        dropped["check-tail"] = "RH-only priorities"
        dropped["overlap"] = "the targeted overlap list names RH declarations only"
    plain = n - feat["module_system"]
    dep, single, med = feat["import_depth"], feat.get("single_importer_modules", 0), feat.get("median_module_bytes", 0)
    if plain >= 0.5 * n and n >= MERGE_MIN_MODULES:
        items.append("merge")
        reasons["merge"] = f"{n} modules, {plain} with plain headers: module merging cuts the process count (RH -229 s)"
    elif plain >= 0.5 * n and dep >= 16 and single >= dep // 2 and med <= MERGE_CHAIN_MAX_BYTES:
        items.append("merge")
        reasons["merge"] = (f"import chain of {dep} modules, {single} single-importer modules, median module {med} B: chains of "
                            "cheap modules collapse into groups (V08: 3.6-8.3x on 512-2,048-module chains)")
    else:
        dropped["merge"] = (f"{n} modules ({plain} plain headers, depth {dep}, {single} single-importer, median {med} B): merging "
                            "pays only on thousands of plain-header modules or on long chains of cheap modules (module-system "
                            "files are never merged)")
    if n >= NATIVE_MIN_MODULES and threads >= NATIVE_MIN_THREADS and plain >= 0.5 * n and mem >= ZYGOTE_MIN_MEM:
        items.append("native-pkg")
        reasons["native-pkg"] = "very long build on many threads: native package code amortizes its compile"
    else:
        dropped["native-pkg"] = ("compiles every C file of the trusted packages with all threads on every run (no cache): "
                                 "CPU taken from a build of this size (no measurable gain at 1.6k modules); never for "
                                 "module-system files (finding 057: SIGSEGV + retry per module)")
    if host.get("shm_free", 0) >= 256 * GB and n >= MERGE_MIN_MODULES and mem >= 512 * GB:
        opts["export_dir"] = "/dev/shm"
        reasons["export_dir"] = ("big project, >= 256 GB free on /dev/shm and >= 512 GB memory budget (tmpfs pages are "
                                 "charged to the run's memory cgroup, D09): untrusted export on tmpfs")
    # the export stage: D15's byte-identical low-memory exporter first on small memory budgets (E1 needs ~6.5 x the
    # export: 7.1 GB for a 1.1 GB export, D09; export-lowmem passes rh-mid in 4 GB at ~1.3x E1's time, D15), else only as
    # the fallback of a failed E1 before the official exporter (5-27x slower than either)
    if mem and mem < EXPORT_LOWMEM_PREFER:
        opts["export_lowmem"] = "prefer"
        reasons["export_lowmem"] = (f"memory budget {mem / GB:.0f} GB < {EXPORT_LOWMEM_PREFER // GB} GB: the low-memory exporter "
                                    "first (byte-identical to E1, ~1.3x its time), E1 then the official exporter as fallbacks")
    else:
        opts["export_lowmem"] = "fallback"
    if feat.get("adddecl_modules"):
        opts["confirm_failure"] = "full"
        reasons["confirm_failure"] = (f"{feat['adddecl_modules']} module(s) define metaprograms that call addDecl: their results "
                                      "may depend on the build-time kernel check (like Mathlib's translation attributes), so a "
                                      "failed transformed build is confirmed by the full exact build B1")
    elif "retries" in items and "merge" not in items:
        opts["confirm_failure"] = "exact-retry"
        reasons["confirm_failure"] = ("a failed transformed build is confirmed by the failing modules' exact official invocation "
                                      "(retries) instead of a full exact rebuild: a failed attempt costs one build (PNT+ with a "
                                      "broken proof: 48 s instead of 94 s; official flow 74 s); --confirm-build-failure-full "
                                      "restores the full B1 confirmation")
    else:
        opts["confirm_failure"] = "full"
    return {"build": build, "unsafe": items, "options": opts, "threads": threads, "reasons": reasons, "dropped": dropped}


def check_threads(export_bytes, threads):
    """Threads for the trusted check by export size (D09, spot node, rh-mid 1.1 GB: T16 28 s, T32 24 s, T64 30 s, T128 33 s
    with 9x the CPU; RH 61.6 GB keeps gaining up to 384; D04 spot c4, PNT 0.57 GB: 21 threads 16.6 s vs 48 threads 12.1 s):
    ~48 per GB^0.75, at least 32, at most the run's budget.
    Thread counts never change a verdict (gate: thread matrix 1..384)."""
    gb = max(export_bytes, 1) / GB
    t = max(1, min(threads, max(32, int(48 * gb ** 0.75))))
    # memory: the three legs run concurrently, peak ~ 4.2 x export + ~87 MB per thread (D09's leg models: ccmp 1.9x,
    # pleanchecker 1.8x + 33 MB/thread, gruszka 0.5x + 54 MB/thread); keep 1 GB for the rest
    mb = mem_budget()
    if mb:
        t = max(1, min(t, int((mb - 4.2 * export_bytes - GB) // (87 << 20))))
    return t


LOWMEM_SCRIPT = "check/lowmem/check-sound-lowmem.sh"


def _pins_present(pins):
    """Every 'PIN name sha256 path' file of a pins.env exists (the script itself verifies the sha256 at start and end)."""
    try:
        lines = open(pins).read().splitlines()
    except OSError:
        return False
    paths = [ln.split()[3] for ln in lines if ln.startswith("PIN ") and len(ln.split()) >= 4]
    return bool(paths) and all(os.path.isfile(p) for p in paths)


def check_plan(export_bytes, threads, pkgroot=None):
    """Which TRUSTED check fits the memory budget (both are reviewed trusted checks with the same verdict semantics):
    the normal check-sound.sh runs its three legs concurrently (peak ~ 4.2 x export + 87 MB/thread, D09); the low-memory
    check/lowmem/check-sound-lowmem.sh (D15) runs them one after the other (peak ~ max(0.5 x export + 250 MB,
    2.4 x export + 35 MB/thread, 1.5 x export)) and is slower. Low memory only when the normal one would not fit."""
    mb = mem_budget()
    plan = {"script": "check/sound/check-sound.sh", "threads": threads, "lowmem": False,
            "mem_budget_mb": (mb >> 20) if mb else None, "export_bytes": export_bytes}
    if not mb:
        plan["why"] = "no memory budget known"
        return plan
    e = float(export_bytes)
    normal = 4.2 * e + (87 << 20) * threads + GB
    plan["normal_peak_mb"] = int(normal) >> 20
    if normal <= mb:
        plan["why"] = "the normal check fits the memory budget"
        # check-sound.sh v2.3-H can run the veto-only extra kernel con-leche next to the judge (opt-in;
        # when its default switch is 'auto', only if its own memory guard allows: judge + 0.85 x export + 2 GiB; measured
        # 0.79 x on the 61.6 GB RH export); informational here - the trusted script decides and records it itself
        cl = normal + 0.85 * e + (2 << 30)
        plan["con_leche_peak_mb"] = int(0.85 * e + (2 << 30)) >> 20
        plan["con_leche"] = "fits if enabled (judge + con-leche ~%d MB <= budget)" % (int(cl) >> 20) if cl <= mb else \
            "would not fit (judge + con-leche ~%d MB > budget %d MB): skipped (memory) in default-on mode" % (int(cl) >> 20, mb >> 20)
        return plan
    lt = max(1, min(threads, int((mb - 2.4 * e - GB) // (35 << 20))))
    low = max(0.5 * e + (250 << 20), 2.4 * e + (35 << 20) * lt, 1.5 * e) + GB // 2
    plan["lowmem_peak_mb"] = int(low) >> 20
    ok = bool(pkgroot) and os.path.isfile(os.path.join(pkgroot, LOWMEM_SCRIPT)) and \
        _pins_present(os.path.join(pkgroot, "check", "lowmem", "pins.env"))
    if ok:   # whenever the normal check does not fit, the sequential one is the better bet (D15: rh-mid ACCEPTED at 3 GB,
        # whole Mathlib at 12 GB, where the linear estimate said ~3.2 / ~15 GB and check-sound.sh needs 6 / 24 GB)
        plan["con_leche"] = "not available: the low-memory check has no extra kernels"
        plan.update(script=LOWMEM_SCRIPT, lowmem=True, threads=lt,
                    why=f"normal check ~{plan['normal_peak_mb']} MB > budget {plan['mem_budget_mb']} MB: sequential "
                        f"low-memory check (estimate ~{plan['lowmem_peak_mb']} MB, {lt} threads)")
    else:
        plan["why"] = "the normal check would not fit and the low-memory check is not installed here"
    return plan


def mem_budget():
    """Bytes this process may still use: min(MemAvailable, memory.max - memory.current over the cgroup chain)."""
    v = None
    for ln in (_read("/proc/meminfo") or "").splitlines():
        if ln.startswith("MemAvailable:"):
            v = int(ln.split()[1]) * 1024
    cg = _read("/proc/self/cgroup") or ""
    for ln in cg.splitlines():
        parts = ln.split(":", 2)
        if len(parts) == 3 and parts[0] == "0":
            d = "/sys/fs/cgroup" + parts[2].rstrip("/")
            while d.startswith("/sys/fs/cgroup") and d != "/sys/fs/cgroup":
                mx, cur = _read(os.path.join(d, "memory.max")), _read(os.path.join(d, "memory.current"))
                if mx and cur and mx.strip() != "max":
                    free = int(mx) - int(cur)
                    v = free if v is None else min(v, free)
                d = os.path.dirname(d)
    return v


def plan(project, packages=None, threads_given=None, pkgroot=None):
    t0 = time.time()
    host = host_info(pkgroot)
    if project and os.path.isdir(project):
        feat = scan_project(project)
    else:   # export-in without a project (bin/fastverify - CHALLENGE OUT --from-export X): threads / check choice only
        feat = {"modules": 0, "module_files_from": "none (export-in)", "bytes": 0, "module_system": 0,
                "first_import_Mathlib": 0, "imports_Mathlib": 0, "closure_Mathlib": 0, "prefix_Mathlib": 0, "import_depth": 0, "single_importer_modules": 0,
                "median_module_bytes": 0, "translate_modules": 0, "translate_examples": [], "unfold_exact_modules": 0,
                "kernel_heavy_modules": 0, "adddecl_modules": 0, "suggestions_modules": 0, "lakefile": None, "toolchain": "", "scan_seconds": 0.0, "_names": set()}
    d = decide(feat, host, threads_given=threads_given, pkgroot=pkgroot)
    feat = {k: v for k, v in feat.items() if not k.startswith("_")}
    d.update({"features": feat, "host": host, "seconds": round(time.time() - t0, 3), "version": "d04-1"})
    return d


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(description="what --preset sound-auto would choose for PROJECT on this host, and why")
    ap.add_argument("project")
    ap.add_argument("--packages")
    ap.add_argument("--threads", type=int)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    try:
        d = plan(a.project, a.packages, a.threads, root)
    except ProjectEscape as e:   # no plan for a project whose lakefile points outside it
        print(f"autotune: refused: {e}", file=sys.stderr)
        return 2
    if a.json:
        print(json.dumps(d, indent=1, default=str))
        return 0
    f, h = d["features"], d["host"]
    print(f"project: {f['modules']} modules ({f['module_files_from']}), {f['bytes'] >> 20} MiB source, depth {f['import_depth']}, "
          f"{f['module_system']} module-system, {f['first_import_Mathlib']} start with `import Mathlib` ({f.get('closure_Mathlib', 0)} hold it in their import closure), "
          f"{f['translate_modules']} use to_additive/to_dual, toolchain {f['toolchain']}")
    print(f"host: {h['cpus']} CPUs, memory budget {(h['mem_budget'] or 0) / GB:.0f} GB, /dev/shm free {h['shm_free'] / GB:.0f} GB, glibc {h['glibc']}")
    b3 = f" --unsafe '{','.join(d['unsafe'])}'" if d["unsafe"] else ""
    print(f"=> --build {d['build']} --threads {d['threads']}" + (b3 if d["build"] == "B3" else "")
          + "".join(f" --{k.replace('_', '-')} {v}" for k, v in d["options"].items() if k not in ("confirm_failure", "export_lowmem"))
          + (" --confirm-build-failure-full" if d["options"].get("confirm_failure") == "full" and d["build"] == "B3" else ""))
    if d["build"] != "B3" and b3:
        print(f"   (with an explicit --build B3:{b3})")
    for k, v in d["reasons"].items():
        print(f"  + {k}: {v}")
    for k, v in d["dropped"].items():
        print(f"  - {k}: {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

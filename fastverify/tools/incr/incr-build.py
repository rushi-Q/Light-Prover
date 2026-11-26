#!/usr/bin/python3 -I
"""tools/incr/incr-build.py — UNTRUSTED incremental build for re-verification after small edits.

usage: incr-build.py --base BASE_PROJ --base-plan BASE_PLAN --src NEW_SOURCES --work WORKDIR --packages WS --tc TC
                     [--lean LEAN] [--threads N] [--extra-arg ARG]... [--plugin SO] [--planner BIN] [--json FILE]

  BASE_PROJ   a project tree that an earlier fastverify run built (OUT/work/proj of a run with --keep-work; its
              .lake/build holds the .olean files). It is NOT modified: the new tree is a reflink copy (XFS/btrfs) or a full
              copy (`cp -a --reflink=auto`); with --hardlink a hard-linked copy (rebuilt modules get their outputs unlinked
              first, but the project's own elaboration-time code could rewrite shared inodes: trusted edits only).
  BASE_PLAN   the plan.jsonl of that build (OUT/log/build-fast/plan.jsonl; the unmerged plan).
  NEW_SOURCES the edited project (sources, lakefile.toml, manifest; its .lake is ignored like fastverify does).
  WORKDIR     fresh directory: WORKDIR/proj = the new tree, WORKDIR/log = plan, filtered plan, scheduler records.

What it does (no project code outside bwrap; nothing here is trusted):
  1. WORKDIR/proj = cp -a --reflink=auto BASE_PROJ (or cp -al with --hardlink); every source file that differs from NEW_SOURCES is replaced (unlink + copy), files
     absent from NEW_SOURCES are removed (outside .lake).
  2. Lake's plan for the new tree: the package's planner (build/planner, Lake 4.33.1's own code) in the build sandbox.
  3. dirty = modules whose source changed, whose plan record (argv, setup, deps, outputs) differs from the base plan,
     that are new, or whose outputs are missing; closed under importers (every module that imports a dirty one).
  4. sched.py (the package's scheduler) runs only the dirty modules' lean invocations, in exactly build.sh's sandbox,
     with the given extra args (e.g. the sound preset's -Ddebug.skipKernelTC=true -Dlinter.all=false and the
     fast-exact plugin) and the given lean (e.g. the T1 toolchain); clean modules keep the base outputs.
  5. WORKDIR/log/lean_path.txt = the plan's LEAN_PATH + TC/lib/lean (what the exporter needs).

Why this cannot cause a false ACCEPT: the build is untrusted in sound mode (soundness rule S3, README 1b). Stale or
wrong .olean files can only yield an export that the trusted check (official challenge export, ccmp, official-kernel
replay of EVERY exported declaration + gruszka) rejects, or a failed build. The verdict must come from
`bin/fastverify ... --from-export EXPORT --preset sound` (or check/sound/check-sound.sh) on the export of this tree.
Stale outputs fail closed: paths are normalized before matching (a lakefile `srcDir = "./src"` makes Lake
write './src/...' source paths - the raw match rebuilt nothing); any change to a file that is not a module source (data
read with include_str, non-module .lean, lakefile, lake-manifest.json - also a dropped one -, ...) rebuilds every module;
when anything changed and ANY module of the plan contains elaboration-time code (elab / macro / syntax / notation /
run_cmd / initialize / #eval / unsafe / implemented_by / extern / include_str / IO / Lean / Meta / ... - a broad word
list: a false hit only costs a full build) every module is rebuilt and the work tree's .lake is cleaned of everything a
fresh build would not have (base-build leftovers); module sources under .lake (outside the dependency packages' bind
points) and symlinked directories in the trees are refused; `--hardlink` copies the sources (only build outputs stay
shared); after the build every module's source in the work tree must be byte-identical to the submitted file and every
module that kept the base's output must have the base's source - else exit 2 (no verdict). `"exact": true` in the report
iff every reverse dependency of every changed module was rebuilt (what a fresh build would rebuild); --optimistic /
--interface (EXPERIMENTAL) builds report exact false when they kept importers: callers never count their ACCEPTED.
Exit: 0 built, 1 a module failed (lean error), 2 could not run / declined / stale outputs. One JSON line on stdout (and
--json FILE).
"""
import argparse, filecmp, hashlib, json, os, re, shutil, subprocess, sys, time

ROOT = os.environ.get("FASTVERIFY") or os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
PY = "/usr/bin/python3"
T0 = time.time()
RES = {"tool": "incr-build", "trusted": False}
JSONF = [None]   # --json FILE (set in main), for refusals raised inside sandbox_argv


def safe_w(path):
    """open a host-side output in WORK/log for writing without ever following a
    symlink planted there: the name is unlinked first and recreated O_EXCL | O_NOFOLLOW"""
    try:
        os.unlink(path)
    except FileNotFoundError:
        pass
    return os.fdopen(os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o644), "w")


def read_nofollow(path):
    """the contents of a regular file, without following a symlink"""
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    import stat as _st
    if not _st.S_ISREG(os.fstat(fd).st_mode):
        os.close(fd)
        raise OSError(f"{path} is not a regular file")
    with os.fdopen(fd, "rb") as f:
        return f.read()


def emit(rc, detail, jf=None):
    RES.update({"exit": rc, "detail": detail, "seconds": round(time.time() - T0, 3)})
    line = json.dumps(RES)
    print(line)
    if jf:
        with open(jf, "w") as f:
            f.write(line + "\n")
    sys.exit(rc)


# top-level directories the untrusted build still sees (as build/build.sh sandbox()); every
# other one (/scratch with fvwork's STATE/sock and other runs, /data, /mnt, /opt, ...) is hidden behind an empty tmpfs,
# read-only again after the binds
SBX_KEEP = frozenset(("bin", "sbin", "lib", "lib32", "lib64", "libx32", "usr", "etc", "dev", "proc", "sys", "nix", "gnu",
                      "home", "root", "tmp", "run", "var"))


def plain_abs(p):
    return isinstance(p, str) and p.startswith("/") and not any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in p) \
        and all(c not in ("", ".", "..") for c in p[1:].split("/"))


def read_regular_inside(path, roots):
    """bytes of the regular file `path` only if the opened file IS inside one of
    `roots` (realpaths): O_PATH first (a FIFO / device is never opened), checked on the descriptor, then re-opened through it;
    OSError otherwise"""
    import stat as _st
    pfd = os.open(path, os.O_PATH | os.O_CLOEXEC)
    try:
        real = os.readlink(f"/proc/self/fd/{pfd}")
        if not _st.S_ISREG(os.fstat(pfd).st_mode) or not any(real.startswith(r + "/") for r in roots):
            raise OSError(f"{path}: not a regular file inside the project")
        with open(f"/proc/self/fd/{pfd}", "rb") as f:
            return f.read()
    finally:
        os.close(pfd)


def sandbox_argv(proj, tc, binds, logd=None, extra_ro=()):
    """= build/build.sh sandbox(): read-only /, home/tmp/run/var and every other non-system top-level dir hidden, no
    network, clean env, PROJ writable; dependency binds (lib/manifest.py: DST strictly inside PROJ) and self-binds (SRC = DST:
    the T1 lean tree, the plugin dir, extra_ro = the planner dir / the farm base) read-only. A bind destination
    is created only as a plain directory inside PROJ that is reached through no symlink (realpath = path, before and after
    the mkdir); anything else -> no sandbox (emit 2), never a host-side mkdir elsewhere."""
    masks = ["/" + d for d in sorted(os.listdir("/"))
             if d not in SBX_KEEP and os.path.isdir("/" + d) and not os.path.islink("/" + d)]
    a = ["env", "-i", "/usr/bin/bwrap", "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", 
         "--tmpfs", "/tmp", "--dir", "/tmp/home", "--tmpfs", "/run", "--tmpfs", "/var"]
    for d in masks:
        a += ["--tmpfs", d]
    a += ["--dev", "/dev", "--proc", "/proc", "--clearenv", "--ro-bind", tc, tc, "--bind", proj, proj]
    for src, dst in list(binds) + [(x, x) for x in extra_ro]:
        if not (plain_abs(src) and plain_abs(dst)):
            emit(2, f"bind {src!r} -> {dst!r} is not a plain absolute path", JSONF[0])
        if src != dst:
            if not dst.startswith(proj + "/") or os.path.realpath(dst) != dst:
                emit(2, f"bind destination {dst!r} is not a plain path inside the project", JSONF[0])
            os.makedirs(dst, exist_ok=True)
            if os.path.realpath(dst) != dst:
                emit(2, f"bind destination {dst!r} is reached through a symlink", JSONF[0])
        a += ["--ro-bind", src, dst]
    if logd:
        a += ["--bind", logd, logd]
    for d in masks:
        a += ["--remount-ro", d]
    a += ["--setenv", "PATH", f"{tc}/bin:/usr/bin:/bin", "--setenv", "HOME", "/tmp/home", "--setenv", "LANG", "C.UTF-8",
          "--unshare-all", "--die-with-parent", "--new-session", "--chdir", proj, "--"]
    return a


# a module whose source contains one of these may run code at elaboration time (and so read files, run programs,
# inspect the tree): when anything in the tree changed and any module of the plan matches, EVERY module is rebuilt. A broad
# word list on purpose (also in comments / strings): a false hit only costs a full build; a miss could keep stale outputs
ELAB_TOKENS = re.compile(
    rb"\belab(_rules)?\b|\bmacro(_rules)?\b|\bsyntax\b|\bnotation\d*\b|\binfix[lr]?\b|\bprefix\b|\bpostfix\b|"
    rb"\bbinder_predicate\b|\bdeclare_syntax_cat\b|\brun_(cmd|elab|meta|tac)\b|\b(builtin_)?initialize\b|#eval|#exit|#run|"
    rb"#reduce|\bunsafe\w*|\bimplemented_by\b|\bextern\b|\binclude_(str|bytes)\b|\bIO\b|\bEIO\b|\bBaseIO\b|\bST\b|"
    rb"\bFS\b|\bProcess\b|\bFilePath\b|\bSystem\b|\bLean\b|\bElab\b|\bMeta\b|\bMacro\w*|\bTactic\b|\bSyntax\b|"
    rb"\w+ElabM\b|\bMetaM\b|\bCoreM\b|\bTacticM\b|\bCommandElabM\b|readFile|readBinFile|\bopen\b[^\n]*\bIO\b|"
    rb"@\[\s*(command_elab|term_elab|tactic|macro|builtin_\w+|init|env_linter|attr_parser|code_action)\b|\bnative_decide\b|"
    rb"\bdecide\s*\+native|ofReduceBool|\bDynlib\b|\bplugin\b|--load-dynlib|\bimport\s+all\b|"
    rb"\bLake\b|\bStd\b|\b(d)?simproc\b|\battribute\s*\[")   # (Lake: e.g. Lake.computeFileHash in a simproc)


def header_region(data):
    """Conservative: the bytes of a Lean file up to the first line that is not blank, a comment or a header command
    (module / prelude / [public] [meta] import ...). Two files whose header regions are byte-identical have the same
    imports, so Lake's plan for them is the same. None if the file is not UTF-8."""
    try:
        t = data.decode("utf-8")
    except UnicodeDecodeError:
        return None
    out, depth = [], 0
    for ln in t.split("\n"):
        st = ln.strip()
        if depth > 0 or st.startswith("/-"):
            depth += st.count("/-") - st.count("-/")
            out.append(ln); continue
        if not st or st.startswith("--") or st.split(" ")[0] in ("module", "prelude", "import", "public", "meta"):
            out.append(ln); continue
        break
    return "\n".join(out)


def dir_links(top):
    """symlinked directories under TOP (outside its .lake): their retargeting is invisible to the sync"""
    out = []
    for root, dirs, files in os.walk(top):
        if os.path.realpath(root) == os.path.realpath(top) and ".lake" in dirs:
            dirs.remove(".lake")
        out += [os.path.relpath(os.path.join(root, d), top) for d in dirs if os.path.islink(os.path.join(root, d))]
    return out


def manifest_has_packages(p):
    """a dropped lake-manifest.json changes what a fresh build sees unless it lists no packages (then Lake
    writes an equivalent one while planning, as it did for the base: a manifest-less project without dependencies)"""
    try:
        return bool(json.load(open(p)).get("packages"))
    except (OSError, ValueError, AttributeError):
        return True


def walk_files(top):
    out = {}
    for root, dirs, files in os.walk(top):
        if os.path.realpath(root) == os.path.realpath(top) and ".lake" in dirs:
            dirs.remove(".lake")
        for n in files:
            p = os.path.join(root, n)
            out[os.path.relpath(p, top)] = p
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True); ap.add_argument("--base-plan", required=True)
    ap.add_argument("--src", required=True); ap.add_argument("--work", required=True)
    ap.add_argument("--packages", required=True); ap.add_argument("--tc", required=True)
    ap.add_argument("--lean"); ap.add_argument("--threads", type=int, default=os.cpu_count())
    ap.add_argument("--extra-arg", action="append", default=[]); ap.add_argument("--plugin")
    ap.add_argument("--ktc-exempt-translate", action="store_true",
                    help="with --extra-arg -Ddebug.skipKernelTC=true: modules whose source mentions to_additive / to_dual keep "
                         "the build-time kernel check (build/sched.py, the base run's skip-kernel-tc=except-translate)")
    ap.add_argument("--planner"); ap.add_argument("--json")
    ap.add_argument("--no-early-release", action="store_true")
    ap.add_argument("--interface", action="store_true",
                    help="Lake-like waves: rebuild the edited modules, then only the importers of modules whose PUBLIC "
                         "artifacts changed (module-system files: .olean/.ir/.ir.sig byte-identical to the base -> plain "
                         "importers keep their outputs; `import all` importers and every importer of a non-module file "
                         "are rebuilt), repeated until nothing changes")
    ap.add_argument("--hardlink", action="store_true",
                    help="hard-link the base tree instead of copying it (faster on file systems without reflinks, but a "
                         "hostile edit can then rewrite base files in place: only for trusted edits)")
    ap.add_argument("--optimistic", action="store_true",
                    help="proof-edit fast path: rebuild only the edited modules, keep their importers' outputs (sound: the "
                         "trusted check re-checks every importer against the new declarations; a stale importer can only "
                         "cause a reject, after which the caller re-runs without --optimistic)")
    ap.add_argument("--import-arts-empty", action="store_true",
                    help="run Lake's planner with --import-arts-empty, as the base build did with the sound item "
                         "sound-fast-path=importarts-empty: no up-front transitive importArts walk")
    ap.add_argument("--closure-of", action="append", default=[], metavar="MODULE",
                    help="consider only the import closure of MODULE (repeatable; e.g. the comparator's solution "
                         "module): modules outside it are neither rebuilt nor required, as the official 4.36 `lake "
                         "comparator` builds only the solution module; untrusted like everything here")
    ap.add_argument("--changed", metavar="FILE",
                    help="JSON {\"write\": [REL...], \"delete\": [REL...]} = the ONLY paths in which the new sources differ "
                         "from --base; --src then needs to hold just the written files (sparse). Skips the whole-tree "
                         "source comparison (fvwork knows the change set of a --files request exactly). Paths are "
                         "confined to the project: no absolute paths, '..', .lake/.git, or writes through symlinks")
    ap.add_argument("--farm", action="store_true",
                    help="(with --changed) WORKDIR/proj = a SYMLINK FARM over BASE instead of a tree copy (RH-size trees "
                         "have ~2.4M build files): every directory on the path of a written file becomes a real directory "
                         "of symlinks (copy-on-write), written files and the rebuilt modules' outputs are real; BASE must "
                         "stay unchanged while proj is in use (fvwork: the fixed base of --no-advance candidates)")
    ap.add_argument("--reuse-plan", action="store_true",
                    help="skip Lake's planner when only .lean files changed and every changed file keeps its import "
                         "header (the plan records do not depend on module bodies); otherwise the planner runs")
    a = ap.parse_args()
    JSONF[0] = a.json
    base, src, tc = os.path.realpath(a.base), os.path.realpath(a.src), os.path.realpath(a.tc)
    work = os.path.realpath(a.work)
    if os.path.exists(work) and os.listdir(work):
        emit(2, f"work dir {work} not empty", a.json)
    proj, logd = os.path.join(work, "proj"), os.path.join(work, "log")
    os.makedirs(logd, exist_ok=True)
    # 1. hard-linked copy + source sync
    t = time.time()
    # a HARD-LINKED tree shares inodes with the base, and the new project's elaboration-time code (inside the build
    # sandbox, where the new tree is writable) can rewrite them in place -> it poisons the base tree for every later
    # re-verification (availability / cache integrity; never soundness). Default: a reflink copy (XFS/btrfs: copy-on-write,
    # ~2 s for rh-mid's 9 GB tree) or a full copy elsewhere; --hardlink only for trusted edits.
    rbase = os.path.realpath(base)
    if a.farm:
        if not a.changed:
            emit(2, "--farm needs --changed (a sparse change set)", a.json)
        os.makedirs(proj)
        for e in os.listdir(base):
            os.symlink(os.path.join(rbase, e), os.path.join(proj, e))
        RES["copy_mode"] = "farm"
    else:
        cmd = ["cp", "-al", base, proj] if a.hardlink else ["cp", "-a", "--reflink=auto", base, proj]
        r = subprocess.run(cmd, capture_output=True, text=True)
        RES["copy_mode"] = "hardlink" if a.hardlink else "reflink-or-copy"
        if r.returncode != 0:
            emit(2, f"{' '.join(cmd[:3])} failed: {r.stderr.strip()}", a.json)
        if a.hardlink:   # the SOURCES are private copies (a build cannot rewrite the base's sources);
            for rel, q in walk_files(proj).items():   # only build outputs under .lake stay shared
                if os.path.isfile(q) and not os.path.islink(q):
                    shutil.copy2(q, q + ".incr1cp", follow_symlinks=False)
                    os.replace(q + ".incr1cp", q)
    FARM_N = [0]
    # the farm's links point into the (fixed) base project, which the sandbox masks hide: bound read-only (only it)
    FARM_RO = [rbase] if a.farm else []

    def farm_own(rel):
        """(--farm) make every directory on the path of REL a real directory (its entries: symlinks to the base's), remove
        a symlink at REL itself; returns the absolute path, or None if REL leaves the project or crosses a symlink that is
        not a farm link into an existing base directory (e.g. a symlink of the project itself)"""
        parts = [c for c in rel.split("/") if c not in ("", ".")]
        if not parts or ".." in parts:
            return None
        cur = proj
        for comp in parts[:-1]:
            nxt = os.path.join(cur, comp)
            if os.path.islink(nxt):
                tgt = os.readlink(nxt)
                if not tgt.startswith(rbase + "/") or os.path.islink(tgt) or not os.path.isdir(tgt):
                    return None
                os.unlink(nxt)
                os.mkdir(nxt)
                for e in os.listdir(tgt):
                    os.symlink(os.path.join(tgt, e), os.path.join(nxt, e))
                FARM_N[0] += 1
            elif not os.path.lexists(nxt):
                os.mkdir(nxt)
            elif not os.path.isdir(nxt):
                return None
            cur = nxt
        leaf = os.path.join(cur, parts[-1])
        if os.path.islink(leaf):
            os.unlink(leaf)
        return leaf
    if a.farm:   # bind points of the dependency packages must be real directories (bwrap mounts onto them)
        pk = os.path.join(rbase, ".lake", "packages")
        for e in (sorted(os.listdir(pk)) if os.path.isdir(pk) else []):
            if farm_own(os.path.join(".lake", "packages", e, ".bindpoint")) is None:
                emit(2, f"--farm: cannot own .lake/packages/{e}", a.json)
    RES["copy_s"] = round(time.time() - t, 3)
    t = time.time()
    changed, added, removed = [], [], []
    MANIFEST_DROPPED = [False]   # a dropped manifest that listed packages
    if a.changed:   # sparse: only the listed paths (the caller's exact change set)
        try:
            spec = json.load(open(a.changed))
            writes, deletes = list(spec.get("write") or []), list(spec.get("delete") or [])
        except (OSError, ValueError, AttributeError, TypeError) as e:
            emit(2, f"--changed: unreadable ({e})", a.json)
        rproj = os.path.realpath(proj)

        def confined(rel):
            if not isinstance(rel, str) or not rel or "\0" in rel or os.path.isabs(rel):
                return None
            q = os.path.normpath(os.path.join(proj, rel))
            if not q.startswith(proj + "/") or "/.lake/" in q + "/" or q.endswith("/.lake") or "/.git/" in q + "/":
                return None
            if a.farm:   # copy-on-write the directory chain; the leaf is then a real path inside proj (or absent)
                was = os.path.lexists(os.path.join(rbase, os.path.relpath(q, proj)))
                q2 = farm_own(os.path.relpath(q, proj))
                if q2 is None:
                    return None
                if was and not os.path.lexists(q2):   # the farm link was removed: restore a real copy for comparison
                    shutil.copy2(os.path.join(rbase, os.path.relpath(q, proj)), q2, follow_symlinks=False)
                return q2 if not os.path.islink(q2) and (not os.path.lexists(q2) or os.path.isfile(q2)) else None
            par = os.path.dirname(q)
            while not os.path.lexists(par):
                par = os.path.dirname(par)
            if not (os.path.realpath(par) + "/").startswith(rproj + "/") or os.path.islink(q) \
                    or (os.path.lexists(q) and not os.path.isfile(q)):
                return None
            return q
        for rel in writes:
            q, p = confined(rel), os.path.join(src, rel) if isinstance(rel, str) else ""
            if q is None or os.path.islink(p) or not os.path.isfile(p):
                emit(2, f"--changed: bad path {rel!r}", a.json)
            if os.path.lexists(q):
                if filecmp.cmp(p, q, shallow=False):
                    continue
                changed.append(rel)
                os.unlink(q)
            else:
                added.append(rel)
            os.makedirs(os.path.dirname(q), exist_ok=True)
            shutil.copy2(p, q, follow_symlinks=False)
        for rel in deletes:
            q = confined(rel)
            if q is None:
                emit(2, f"--changed: bad path {rel!r}", a.json)
            if os.path.lexists(q) and rel != "lake-manifest.json":
                removed.append(rel)
                os.unlink(q)
            elif rel == "lake-manifest.json" and os.path.lexists(q):
                MANIFEST_DROPPED[0] = manifest_has_packages(q)
        new, cur = {}, {}
    else:
        dl = [("submitted tree", x) for x in dir_links(src)] + [("base tree", x) for x in dir_links(proj)]
        if dl:   # a retargeted directory link is invisible to the file sync
            emit(2, f"symlinked directory {dl[0][1]!r} in the {dl[0][0]} (refused, no verdict)", a.json)
        new, cur = walk_files(src), walk_files(proj)
    RES["sparse_sync"] = bool(a.changed)
    for rel, p in new.items():
        q = os.path.join(proj, rel)
        if rel not in cur:
            added.append(rel)
        elif (os.path.islink(p) != os.path.islink(q)) or (os.readlink(p) != os.readlink(q) if os.path.islink(p)
                                                          else not filecmp.cmp(p, q, shallow=False)):
            changed.append(rel)
            os.unlink(q)
        else:
            continue
        os.makedirs(os.path.dirname(q), exist_ok=True)
        shutil.copy2(p, q, follow_symlinks=False)
    for rel, q in cur.items():
        if rel not in new and rel != "lake-manifest.json":   # a manifest-less project: Lake wrote it while planning
            removed.append(rel)
            os.unlink(q)
        elif rel == "lake-manifest.json" and rel not in new:
            MANIFEST_DROPPED[0] = manifest_has_packages(q)   # kept for Lake, counted as a change (full build)
    RES.update({"sync_s": round(time.time() - t, 3), "changed": changed[:50], "added": added[:50],
                "removed": removed[:50], "n_changed": len(changed), "n_added": len(added), "n_removed": len(removed)})
    # 2. binds + Lake's plan (planner in the build sandbox; the root config must be lakefile.toml, like build.sh)
    if os.path.lexists(os.path.join(proj, "lakefile.lean")) or not os.path.isfile(os.path.join(proj, "lakefile.toml")):
        emit(2, "only lakefile.toml projects (as build.sh)", a.json)
    # a lakefile.lean anywhere in the tree (a local path dependency's) is code
    # Lake would run in the planner's sandbox, which binds logd writable -> only pure-TOML workspaces (as build.sh)
    _seen, _rp0 = set(), os.path.realpath(proj)
    for _dp, _dns, _fns in os.walk(_rp0, followlinks=True):
        _rp = os.path.realpath(_dp)
        if _rp in _seen or not (_rp == _rp0 or _rp.startswith(_rp0 + os.sep)):
            _dns[:] = []
            continue
        _seen.add(_rp)
        _dns[:] = [d for d in _dns if d != ".lake"]
        if "lakefile.lean" in _fns or os.path.islink(os.path.join(_dp, "lakefile.lean")):
            emit(2, f"the project contains {os.path.relpath(os.path.join(_dp, 'lakefile.lean'), _rp0)} (as build.sh)", a.json)
    # a dependency's config file is its manifest entry's configFile, its language decided by the extension
    # alone (Lake/Load/Package.lean resolveConfigFile): every untrusted (non-git) entry must name a .toml file (as build.sh)
    # Lean's FilePath.extension is none for a last component that starts with its only dot
    # (".toml" -> Lake loads ".toml.lean"); without a root manifest Lake resolves path requires itself and honours THEIR
    # manifests; every lake-manifest.json of the tree is checked; a malformed one is a refusal (exit 2), never exit 1
    def _toml(cf):
        if not isinstance(cf, str):
            return False
        bn = cf.rsplit("/", 1)[-1]
        return bn.endswith(".toml") and len(bn) > len(".toml")
    def _check(mp, is_root):
        try:
            m = json.loads(read_nofollow(mp).decode("utf-8"))
        except (OSError, ValueError, UnicodeDecodeError):
            emit(2, f"{os.path.relpath(mp, _rp0)} unreadable (as build.sh)", a.json)
        pk = m.get("packages", []) if isinstance(m, dict) else None
        if not isinstance(pk, list):
            emit(2, f"{os.path.relpath(mp, _rp0)}: packages is not a list (as build.sh)", a.json)
        for e in pk:
            if is_root and isinstance(e, dict) and e.get("type") == "git":
                continue
            cf = e.get("configFile", "lakefile") if isinstance(e, dict) else None
            if not _toml(cf):
                emit(2, f"package configuration {cf!r} is not a .toml file (as build.sh)", a.json)
    _mp = os.path.join(_rp0, "lake-manifest.json")
    if os.path.lexists(_mp):
        _check(_mp, True)
    else:
        try:
            _lt = read_nofollow(os.path.join(_rp0, "lakefile.toml")).decode("utf-8")
        except (OSError, UnicodeDecodeError):
            _lt = "require"
        if re.search(r"(?m)^\s*(\[\[?\s*require\b|require\s*[=.])", _lt):
            emit(2, "no lake-manifest.json but the lakefile requires packages (as build.sh)", a.json)
    for _dp2 in sorted(_seen):
        if _dp2 != _rp0 and os.path.lexists(os.path.join(_dp2, "lake-manifest.json")):
            _check(os.path.join(_dp2, "lake-manifest.json"), False)
    r = subprocess.run([PY, "-I", os.path.join(ROOT, "lib", "manifest.py"), proj, a.packages], capture_output=True, text=True)
    if r.returncode != 0:
        emit(2, f"manifest: {r.stderr.strip()}", a.json)
    binds = [tuple(l.split("\t")) for l in r.stdout.splitlines() if l]
    with safe_w(os.path.join(logd, "binds.tsv")) as f:
        f.write(r.stdout)
    t = time.time()
    plan = os.path.join(logd, "plan.jsonl")
    reuse = False
    if a.reuse_plan and not added and not removed and all(c.endswith(".lean") for c in changed):
        import importlib.util
        spec = importlib.util.spec_from_file_location("fvsched", os.path.join(ROOT, "build", "sched.py"))
        fvs = importlib.util.module_from_spec(spec); spec.loader.exec_module(fvs)
        reuse = True
        for c in changed:
            try:   # only regular files inside the base / new trees (no FIFO, no symlink out)
                d1 = read_regular_inside(os.path.join(base, c), [os.path.realpath(base)])
                d2 = read_regular_inside(os.path.join(src, c), [os.path.realpath(src)])
            except OSError:
                reuse = False; break
            h1, h2 = fvs.header_imports(d1), fvs.header_imports(d2)
            if h1 is None or h2 is None:   # module-system / unusual header: compare the raw header region instead
                h1, h2 = header_region(d1), header_region(d2)
            if h1 is None or h1 != h2:
                reuse = False; break
    RES["plan_reused"] = reuse
    RES["import_arts_empty"] = bool(a.import_arts_empty)
    if reuse:
        with open(a.base_plan) as f:
            bl0 = f.read().splitlines()
        bcwd0 = json.loads(bl0[0])["cwd"]
        with safe_w(plan) as f:
            for l in bl0:
                f.write(l.replace(bcwd0 + "/", proj + "/").replace('"' + bcwd0 + '"', '"' + proj + '"') + "\n")
    planner = a.planner
    if not planner and not reuse:
        pd = os.path.join(logd, "planner"); os.makedirs(pd, exist_ok=True)
        src_pl = os.path.join(ROOT, "build", "planner", "Planner.lean")
        env = {"PATH": "/usr/bin:/bin", "LEAN_PATH": f"{tc}/lib/lean"}
        r1 = subprocess.run([f"{tc}/bin/lean", "-R", os.path.dirname(src_pl), "-c", f"{pd}/planner.c", src_pl], env=env,
                            capture_output=True)
        r2 = r1.returncode == 0 and subprocess.run([f"{tc}/bin/leanc", "-O1", f"{pd}/planner.c", "-o", f"{pd}/planner",
                                                    f"-L{tc}/lib/lean", "-lLake", "-rdynamic"], env=env, capture_output=True)
        if not r2 or r2.returncode != 0:
            emit(2, "planner does not compile", a.json)
        planner = f"{pd}/planner"
    if not reuse and a.farm:   # Lake's planner may write under .lake (config) and the root manifest: real copies there
        for e in (os.listdir(os.path.join(rbase, ".lake")) if os.path.isdir(os.path.join(rbase, ".lake")) else []):
            if e != "build" and os.path.islink(os.path.join(proj, ".lake", e)):   # (packages: real bind points already)
                q = farm_own(os.path.join(".lake", e))
                if q is None:
                    emit(2, f"--farm: cannot own .lake/{e}", a.json)
                b = os.path.join(rbase, ".lake", e)
                (shutil.copytree(b, q, symlinks=True) if os.path.isdir(b) and not os.path.islink(b)
                 else shutil.copy2(b, q, follow_symlinks=False))
        if os.path.islink(os.path.join(proj, "lake-manifest.json")):
            q = farm_own("lake-manifest.json")
            shutil.copy2(os.path.join(rbase, "lake-manifest.json"), q, follow_symlinks=False)
    if not reuse:
        # the planner sees WORK/log READ-ONLY and writes its plan into a fresh
        # private directory; the plan is copied out as a regular file (no symlink followed), so no planted name in
        # WORK/log can redirect a later host-side write
        pq = os.path.join(logd, "planq")
        shutil.rmtree(pq, ignore_errors=True)
        if os.path.lexists(pq):
            emit(2, f"cannot reset {pq}", a.json)
        os.mkdir(pq, 0o700)
        with safe_w(os.path.join(logd, "plan.out")) as fo, safe_w(os.path.join(logd, "plan.err")) as fe:
            r = subprocess.run(sandbox_argv(proj, tc, binds, pq, extra_ro=[logd] + ([os.path.dirname(os.path.realpath(planner))]
                                                                         if a.planner else []) + FARM_RO)
                               + [planner, tc, os.path.join(pq, "plan.jsonl")]
                               + (["--import-arts-empty"] if a.import_arts_empty else []), stdout=fo, stderr=fe)
        if r.returncode != 0:
            emit(2, f"planner exit {r.returncode} (see {logd}/plan.err)", a.json)
        try:
            data = read_nofollow(os.path.join(pq, "plan.jsonl"))
        except OSError as e:
            emit(2, f"the planner's plan is not a regular file ({e})", a.json)
        with safe_w(plan) as f:
            f.write(data.decode("utf-8", "surrogateescape"))
    RES["plan_s"] = round(time.time() - t, 3)
    # 3. dirty set
    with open(plan) as f:
        lines = f.read().splitlines()
    header, recs = lines[0], [json.loads(l) for l in lines[1:] if l.strip()]
    recs = [x for x in recs if "end" not in x]
    allrecs = list(recs)
    if a.closure_of:   # restrict to the import closure of the given module(s)
        by = {x["name"]: x for x in recs}
        missing = [m for m in a.closure_of if m not in by]
        if missing:
            emit(2, f"--closure-of: {missing[:3]} not in the plan", a.json)
        keep, st = set(a.closure_of), list(a.closure_of)
        while st:
            for d in by[st.pop()]["deps"]:
                if d in by and d not in keep:
                    keep.add(d); st.append(d)
        RES["closure_of"] = {"roots": a.closure_of, "modules": len(keep), "of": len(recs)}
        recs = [x for x in recs if x["name"] in keep]
    if reuse:   # the plan IS the base plan with the paths rewritten: same records, no second parse (~10 s on RH)
        brec = {x["name"]: x for x in recs if "name" in x}
    else:
        with open(a.base_plan) as f:
            bl = f.read().splitlines()
        bhead = json.loads(bl[0])
        bcwd = bhead["cwd"]
        brec = {}
        for l in bl[1:]:
            if l.strip():
                x = json.loads(l.replace(bcwd + "/", proj + "/").replace('"' + bcwd + '"', '"' + proj + '"'))
                if "name" in x:
                    brec[x["name"]] = x
    def npath(p):   # normalized absolute path (Lake writes './src/...' for srcDir = "./src")
        return os.path.normpath(p if os.path.isabs(p) else os.path.join(proj, p))
    chg = set(npath(os.path.join(proj, c)) for c in changed + added)
    mods = {x["name"]: x for x in recs}
    seed = set()
    why = {"source": 0, "record": 0, "new": 0, "missing-output": 0, "non-module": 0, "elab-code": 0}
    # only the dependency packages' bind points may hold module sources under .lake (a fresh build of the
    # submitted tree has nothing else there: a srcDir / root under .lake would compile base-build leftovers)
    bind_dsts = [os.path.normpath(d) for _, d in binds]

    def in_bind(p):
        return any(p == d or p.startswith(d + "/") for d in bind_dsts)
    lake = os.path.join(proj, ".lake")
    for x in allrecs:
        sp = npath(x.get("src") or "")
        if (sp == lake or sp.startswith(lake + "/")) and not in_bind(sp):
            emit(2, f"module {x.get('name')}: source {os.path.relpath(sp, proj)} lies under .lake outside the dependency "
                    "packages (refused, no verdict)", a.json)
    # every changed / added / removed path that is not a module source (of the new plan or of the base plan)
    all_srcs = set(npath(x["src"]) for x in allrecs if x.get("src")) | set(npath(x["src"]) for x in brec.values() if x.get("src"))
    non_module = sorted(c for c in changed + added + removed if npath(os.path.join(proj, c)) not in all_srcs)
    if MANIFEST_DROPPED[0]:
        non_module.append("lake-manifest.json (dropped)")
    tree_changed = bool(changed or added or removed or MANIFEST_DROPPED[0])

    def elab_code(m):
        try:
            with open(mods[m]["src"], "rb") as f:
                return ELAB_TOKENS.search(f.read()) is not None
        except OSError:
            return True
    elab_mods = sorted(m for m in mods if elab_code(m)) if tree_changed and not non_module else []
    full = bool(non_module or elab_mods)   # a full build (every module of the plan)
    RES["non_module_changed"] = non_module[:20]
    RES["elab_modules"] = elab_mods[:20]
    RES["full_build_why"] = ("non-module change: " + non_module[0]) if non_module else \
        (f"elaboration-time code in {elab_mods[0]} (and {len(elab_mods) - 1} more)" if elab_mods else None)
    for m, x in mods.items():
        b = brec.get(m)
        if non_module:   # a non-module file changed: nothing is known about who reads it -> full build
            seed.add(m); why["non-module"] += 1
        elif elab_mods:   # elaboration-time code anywhere in the plan may read anything -> full build
            seed.add(m); why["elab-code"] += 1
        elif npath(x["src"]) in chg:
            seed.add(m); why["source"] += 1
        elif b is None:
            seed.add(m); why["new"] += 1
        elif any(x.get(k) != b.get(k) for k in ("argv", "setup", "deps", "outputs", "setupFile", "isModule")):
            seed.add(m); why["record"] += 1
        elif not all(os.path.exists(o) for o in x["outputs"]):
            seed.add(m); why["missing-output"] += 1
    dependents = {m: [] for m in mods}
    for m, x in mods.items():
        for d in x["deps"]:
            if d in dependents:
                dependents[d].append(m)
    def closure(start):
        out, st = set(start), list(start)
        while st:
            for d in dependents[st.pop()]:
                if d not in out:
                    out.add(d); st.append(d)
        return out
    dirty = closure(seed)
    exact_set = set(dirty)   # what a fresh build would rebuild (every reverse dependency of every change)
    forced = set(mods) if full else set()
    RES["dirty_full"] = len(dirty)
    RES["optimistic"] = False
    if a.optimistic and why["record"] == 0 and why["new"] == 0 and not full:
        dirty = set(seed); RES["optimistic"] = True
    if full:   # nothing a fresh build would not have stays readable under .lake (base-build leftovers)
        keep = set()
        for x in allrecs:
            for o in list(x.get("outputs") or []) + ([x["setupFile"]] if x.get("setupFile") else []):
                keep.add(npath(o))
        lib = os.path.join(lake, "build", "lib", "lean")
        left = []
        top = os.path.join(rbase, ".lake") if a.farm else lake
        for root, dirs, files in os.walk(top):
            pr = os.path.normpath(os.path.join(lake, os.path.relpath(root, top)))
            dirs[:] = [d for d in dirs if not in_bind(os.path.join(pr, d))]
            for n in files + [d for d in dirs if os.path.islink(os.path.join(root, d))]:
                pq = os.path.join(pr, n)
                if pq in keep or (pr == lib and n.startswith("FastverifyPremiseOff.")):
                    continue
                left.append(pq)
        if left and a.farm:
            emit(2, f"--farm: the base tree holds {os.path.relpath(left[0], proj)} under .lake, which a fresh build would not "
                    "have (refused for a full build, no verdict)", a.json)
        for pq in left:
            os.unlink(pq)
        RES["lake_leftovers_removed"] = len(left)
    RES.update({"modules": len(mods), "seed": len(seed), "seed_why": why, "dirty": len(dirty),
                "seed_modules": sorted(seed)[:20]})
    lp = json.loads(header)["leanPath"] + ":" + f"{tc}/lib/lean"
    # (as build.sh lpconfined) LEAN_PATH comes from the UNTRUSTED lakefile and the export
    # stage acts on its directories on the host: every entry must be a plain path inside the project (or TC/lib/lean); in
    # --farm mode a not-yet-owned directory resolves into the (fixed) base project, which is allowed
    for e in lp.split(":"):
        if not e or e == f"{tc}/lib/lean":
            continue
        n = os.path.normpath(e)
        rn = os.path.realpath(n)
        if not plain_abs(e) or not n.startswith(proj + "/") or not (rn == n or (a.farm and rn.startswith(rbase + "/"))):
            emit(2, f"LEAN_PATH entry {e!r} is not a plain path inside the project", a.json)
    with safe_w(os.path.join(logd, "lean_path.txt")) as f:
        f.write(lp)
    # 4. build the dirty modules (one wave; --interface: Lake-like waves)
    t = time.time()
    opts = [str(a.threads), "--no-src-check"] + ([] if a.no_early_release else ["--early-release"])
    for e in a.extra_arg:
        opts += ["--extra-arg", e]
    if a.ktc_exempt_translate:
        opts += ["--ktc-exempt-translate"]
    sb = list(binds)
    if a.plugin:
        pdir = os.path.dirname(os.path.realpath(a.plugin))
        sb.append((pdir, pdir)); opts += ["--extra-arg", f"--plugin={os.path.realpath(a.plugin)}"]
    if a.lean:
        ld = os.path.dirname(os.path.dirname(os.path.realpath(a.lean)))
        sb.append((ld, ld)); opts += ["--lean", os.path.realpath(a.lean)]
    with open(os.path.join(ROOT, "build", "sched.py")) as f:
        sched = f.read()

    def wave_deps(names):
        """for every module of `names`: the modules of `names` it depends on, DIRECTLY OR THROUGH MODULES OUTSIDE `names`
        (with --optimistic / --interface a clean module can sit between two rebuilt ones - e.g. Solution (edited)
        imports Tiny.B (clean) imports Tiny.A (edited) - and restricting the direct deps to `names` let the scheduler start
        Solution while Tiny.A's outputs were being rewritten: 'failed to open .../Tiny/A.olean' -> a false build failure).
        Iterative memoized walk over the clean modules (each visited once)."""
        memo = {}

        def via(m):   # modules of `names` reachable from module m through clean modules (m itself excluded)
            if m in memo:
                return memo[m]
            stack, onstack = [(m, iter(mods[m]["deps"]))], {m}
            while stack:   # iterative post-order DFS over the clean modules not yet memoized (imports form a DAG)
                u, it = stack[-1]
                for d in it:
                    if d in mods and d not in names and d not in memo and d not in onstack:
                        stack.append((d, iter(mods[d]["deps"]))); onstack.add(d)
                        break
                else:
                    stack.pop(); onstack.discard(u)
                    r = set()
                    for d in mods[u]["deps"]:
                        if d not in mods:
                            continue
                        if d in names:
                            r.add(d)
                        else:
                            r |= memo.get(d, set())
                    memo[u] = r
            return memo[m]
        out = {}
        for x in names:
            r = set()
            for d in mods[x]["deps"]:
                if d not in mods:
                    continue
                if d in names:
                    r.add(d)
                else:
                    r |= via(d)
            r.discard(x)
            out[x] = r
        return out

    def run_wave(names, k):
        """filtered plan of `names` (deps = the modules of `names` reachable directly or through clean modules) ->
        sched.py in the build sandbox; (rc, walls)"""
        fplan = os.path.join(logd, f"plan-incr{k if k else ''}.jsonl")
        if a.farm:   # the modules about to be built write real files: own their output dirs, drop links of the same stem
            for x in recs:
                if x["name"] not in names:
                    continue
                for o in x["outputs"] + [x["setupFile"]]:
                    rel = os.path.relpath(o, proj)
                    q = farm_own(rel)
                    if q is None:
                        emit(2, f"--farm: output {rel} is outside the project or behind a foreign symlink", a.json)
                    d, stem = os.path.dirname(q), os.path.basename(q).split(".")[0] + "."
                    for e in os.listdir(d):
                        if e.startswith(stem) and os.path.islink(os.path.join(d, e)):
                            os.unlink(os.path.join(d, e))
            RES["farm_dirs"] = FARM_N[0]
        hd = json.loads(header); hd["nmods"] = len(names)
        wd = wave_deps(names)
        with safe_w(fplan) as f:
            f.write(json.dumps(hd) + "\n")
            for x in recs:
                if x["name"] in names:
                    y = dict(x); y["deps"] = [d for d in x["deps"] if d in wd[x["name"]]] + \
                        sorted(d for d in wd[x["name"]] if d not in x["deps"])
                    f.write(json.dumps(y) + "\n")
            f.write(json.dumps({"end": len(names)}) + "\n")
        out = os.path.join(logd, f"sched{k if k else ''}.out")
        with open(fplan) as fi, safe_w(out) as fo:
            rc_ = subprocess.run(sandbox_argv(proj, tc, sb, extra_ro=FARM_RO) + ["/usr/bin/python3", "-I", "-c", sched] + opts,
                                 stdin=fi, stdout=fo, stderr=subprocess.STDOUT).returncode
        w_ = []
        with open(out) as f:
            for l in f:
                if l.startswith('{"event": "module"'):
                    try:
                        w_.append(json.loads(l)["wall"])
                    except Exception:  # noqa: BLE001
                        pass
        return rc_, w_

    def same_as_base(path):
        bp = os.path.join(base, os.path.relpath(path, proj))
        try:
            return filecmp.cmp(path, bp, shallow=False)
        except OSError:
            return False

    def imports_all(importer, m):
        try:
            h = header_region(read_regular_inside(mods[importer]["src"], [proj, rbase])) or ""   # confined read
        except OSError:
            return True
        return re.search(r"\bimport\s+all\s+" + re.escape(m) + r"(\s|$)", h) is not None

    sparse_w = set(writes) if a.changed else set()
    sparse_d = set(deletes) if a.changed else set()

    def submitted(rel):
        """the submitted tree's file REL (tree mode: NEW_SOURCES/REL; --changed: the written file, else the base's)"""
        if not a.changed:
            return os.path.join(src, rel)
        if rel in sparse_w:
            return os.path.join(src, rel)
        return None if rel in sparse_d else os.path.join(base, rel)

    def same(p, q):
        try:
            if os.path.realpath(p) == os.path.realpath(q):
                return os.path.isfile(p)
            return os.path.isfile(p) and os.path.isfile(q) and filecmp.cmp(p, q, shallow=False)
        except OSError:
            return False

    def stale_check(built):
        """after a successful build: [] if the outputs belong to the submitted tree, else the reasons. Every module
        source (outside .lake) in the work tree is byte-identical to the submitted file; a module that kept the base's
        output has the base's source; a non-module change rebuilt every module; every possible file reader (and importer
        of one) was rebuilt when anything changed."""
        out = []
        for m, x in sorted(mods.items()):
            sp = npath(x["src"])
            rel = os.path.relpath(sp, proj)
            if in_bind(sp):   # a dependency package's module (the trusted workspace); only the bind points
                continue
            if rel == ".." or rel.startswith("../"):
                out.append(f"module {m}: source {x['src']} lies outside the project"); continue
            sub = submitted(rel)
            if sub is None or not os.path.isfile(sub) or os.path.islink(sub):
                out.append(f"module {m}: no submitted file {rel}"); continue
            if not same(sp, sub):
                out.append(f"module {m}: the compiled source {rel} differs from the submitted file"); continue
            if m not in built and not (a.changed and rel not in sparse_w) and not same(os.path.join(base, rel), sub):
                out.append(f"module {m} kept the base's output although its source {rel} changed")
        if non_module and set(mods) - set(built):
            out.append(f"non-module file(s) changed ({non_module[0]}, ...) but not every module was rebuilt")
        missed = sorted(forced - set(built))
        if missed:
            out.append(f"module {missed[0]} was not rebuilt although a full build was required ({RES.get('full_build_why')})")
        return out

    rc, walls = 0, []
    if not a.interface:
        if dirty:
            rc, walls = run_wave(dirty, 0)
    else:
        built_at, wave, k = {}, set(seed) | forced, 0
        while wave and rc == 0:
            rc, w_ = run_wave(wave, k + 1); walls += w_
            for m in wave:
                built_at[m] = k
            if rc != 0:
                break
            nxt = set()
            for m in wave:
                x = mods[m]
                pub = [o for o in x["outputs"] if o.endswith((".olean", ".ir", ".ir.sig"))]
                iface_same = bool(x.get("isModule")) and pub and all(same_as_base(o) for o in pub)
                priv_same = iface_same and all(same_as_base(o) for o in x["outputs"] if o.endswith(".olean.private"))
                for d in dependents[m]:
                    if iface_same and (priv_same or not imports_all(d, m)):
                        continue
                    if built_at.get(d, -1) < k:
                        nxt.add(d)
            wave, k = nxt, k + 1
        dirty = set(built_at)
        RES.update({"interface_waves": k, "dirty": len(dirty)})
    RES["build_s"] = round(time.time() - t, 3)
    RES.update({"modules_built": len(walls), "sum_module_wall_s": round(sum(walls), 3),
                "max_module_wall_s": round(max(walls), 3) if walls else 0})
    RES["exact"] = exact_set <= set(dirty)   # False = importers of a changed module kept (EXPERIMENTAL modes)
    if rc == 0:
        bad = stale_check(dirty)
        if bad:
            RES["stale"] = bad[:20]
            emit(2, f"stale outputs: {bad[0]} (no verdict: the build's outputs are not the submitted tree's)", a.json)
        emit(0, f"built {len(dirty)} of {len(mods)} modules", a.json)
    emit(1 if rc == 1 else 2, f"scheduler exit {rc} (see {logd}/sched.out)", a.json)


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except BaseException as e:  # noqa: BLE001 - an internal error is never a verdict: exit 2 (exit 1 = a module failed)
        RES["traceback"] = repr(e)[:500]
        emit(2, f"internal error: {e!r}"[:300])

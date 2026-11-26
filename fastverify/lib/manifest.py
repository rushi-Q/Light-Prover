#!/usr/bin/python3 -I
"""manifest.py PROJECT_DIR PACKAGES_WS  ->  prints one 'SRC<TAB>DST' line per dependency to bind read-only.

Resolves the dependencies of a Lake project WITHOUT network and without trusting anything the project ships:
every package in PROJECT_DIR/lake-manifest.json must be present in the trusted workspace PACKAGES_WS (a directory with
its own lake-manifest.json and materialized packages, e.g. the clean challenge after `lake exe cache get`) with the SAME
name, type, url, rev, subDir, configFile and manifestFile, and the materialized git checkout's HEAD must be that rev.
Anything else (path dependencies outside the project, missing packages, different revisions, unknown manifest
versions or package types) is refused: exit 2 with the reason on stderr (the caller fails closed).
A non-inherited `path` entry whose dir is a real directory strictly inside PROJECT_DIR is accepted with nothing to
bind (Lake loads it from the project inside the sandbox).
A project without lake-manifest.json is accepted only if it has no dependencies to bind (nothing is printed); Lake then
resolves it itself inside the sandbox (no network) exactly as the official `lake build` would.
DST (the only path derived from the untrusted project: packagesDir) is CONFINED strictly inside
PROJECT_DIR, without '.'/'..'/empty components and without a symlink component (realpath = the printed path); both
packagesDir values must be clean relative strings; no printed path contains a control character (no TAB/newline can add
a binds.tsv field or line). SRC comes from the trusted workspace (its own packagesDir + a package name it lists).
The callers (build/official-build.sh, build/build.sh, build/native.sh, export/export.sh, bin/fastverify) run host-side
`mkdir -p DST` and `bwrap --ro-bind SRC DST` per line, so anything else is refused (exit 2, fail closed).
"""
import json, os, subprocess, sys

FIELDS = ("type", "url", "rev", "subDir", "configFile", "manifestFile")
VERSIONS = ("1.1.0", "1.2.0", "1.3.0")   # 1.3.0 (Lake 4.36) only adds the path-dependency "copy" field; path deps are refused


def die(msg):
    print(f"manifest: {msg}", file=sys.stderr)
    sys.exit(2)


def has_ctl(s):
    """any non-printable character: C0 controls (incl. TAB, LF, CR, NUL), DEL, C1 controls (incl. NEL), and every other
    character Python does not print (line/paragraph separators U+2028/U+2029 that str.splitlines() breaks at, format and
    unassigned characters): never part of a path this module prints (r2, review L1). A space is printable and allowed."""
    return any(not c.isprintable() for c in s)


def clean_rel(rel, what):
    """a relative path inside the workspace: str, no control characters, not absolute, no empty/'.'/'..' component"""
    if not isinstance(rel, str) or not rel or has_ctl(rel) or os.path.isabs(rel) \
            or any(c in ("", ".", "..") for c in rel.split("/")):
        die(f"{what} {rel!r} must be a clean relative path inside the workspace (no control characters, no empty, "
            "'.' or '..' component)")
    return rel


def confined(path, root, what):
    """path (absolute, built by this module) must lie strictly inside root (a realpath) and resolve to itself"""
    if has_ctl(path) or os.path.normpath(path) != path or not path.startswith(root + os.sep) \
            or os.path.realpath(path) != path:
        die(f"{what} {path!r} is not a plain path strictly inside {root} (symlink, control character or traversal)")
    return path


def load(path):
    try:
        with open(path, encoding="utf-8") as f:
            m = json.load(f)
    except Exception as e:  # noqa: BLE001
        die(f"cannot read {path}: {e}")
    if not isinstance(m, dict) or not isinstance(m.get("packages", []), list):
        die(f"{path}: not a Lake manifest")
    if str(m.get("version")) not in VERSIONS:
        die(f"{path}: unsupported manifest version {m.get('version')!r} (supported: {', '.join(VERSIONS)})")
    return m


def lake_dir_name(name):
    """The directory Lake materializes a package in: `PackageEntry.dirName = entry.name.toString (escape := false)`
    (Lake 4.33 `Lake/Load/Manifest.lean`), while the manifest stores `toJson entry.name`, i.e. the ESCAPED name
    (`«doc-gen4»`). Unescape the «...» components (using the escaped string as the directory bound the package
    where Lake never looks, so every build of such a project failed)."""
    comps, cur, i = [], "", 0
    while i < len(name):
        c = name[i]
        if c == "«":
            j = name.find("»", i + 1)
            if j < 0:
                die(f"bad package name {name!r}")
            cur += name[i + 1:j]
            i = j + 1
        elif c == ".":
            comps.append(cur)
            cur = ""
            i += 1
        else:
            cur += c
            i += 1
    comps.append(cur)
    d = ".".join(comps)
    if not d or "/" in d or d in (".", "..") or has_ctl(d):
        die(f"bad package directory {d!r} for package name {name!r}")
    return d


def git_head(d):
    try:
        out = subprocess.run(["git", "-c", f"safe.directory={d}", "-C", d, "rev-parse", "HEAD"], capture_output=True,
                             text=True, env={"PATH": "/usr/bin:/bin", "HOME": "/nonexistent", "GIT_CONFIG_NOSYSTEM": "1"},
                             timeout=60)
    except Exception as e:  # noqa: BLE001
        die(f"git rev-parse failed in {d}: {e}")
    if out.returncode != 0:
        die(f"git rev-parse failed in {d}: {out.stderr.strip()}")
    return out.stdout.strip()


def main():
    if len(sys.argv) != 3:
        die("usage: manifest.py PROJECT_DIR PACKAGES_WS")
    proj, ws = (os.path.realpath(a) for a in sys.argv[1:])
    pm_path = os.path.join(proj, "lake-manifest.json")
    if not os.path.exists(pm_path):
        # Lake will treat the project as having no resolved dependencies; a `require` then needs the network and fails
        # inside the sandbox exactly like the official offline build.
        return
    pm = load(pm_path)
    pkgs = pm.get("packages", [])
    if not pkgs:
        return
    local = [p for p in pkgs if isinstance(p, dict) and p.get("type") == "path" and p.get("inherited") is False]
    if len(local) == len(pkgs):   # only project-local path dependencies: no packages workspace needed
        wm = {"packages": []}
    elif not os.path.isdir(ws):
        die(f"project has {len(pkgs)} dependencies but the packages workspace {ws} does not exist")
    else:
        wm = load(os.path.join(ws, "lake-manifest.json"))
    wpk = {}
    for p in wm.get("packages", []):
        wpk[p.get("name")] = p
    if not pm.get("packagesDir"):
        # Lake uses `manifest.packagesDir?.getD ws.relPkgsDir`: without the field it
        # looks in the LAKEFILE's packagesDir, not in the .lake/packages this module binds -> refuse when the lakefile
        # may set one (a regular-file read inside the project; anything unreadable counts as "may")
        for cf in ("lakefile.toml", "lakefile.lean"):
            cp = os.path.join(proj, cf)
            if not os.path.lexists(cp):
                continue
            try:
                fd = os.open(cp, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
                try:
                    import stat as _st
                    txt = os.read(fd, 1 << 22).decode("utf-8", "replace") if _st.S_ISREG(os.fstat(fd).st_mode) else None
                finally:
                    os.close(fd)
            except OSError:
                txt = None
            if txt is None or "packagesDir" in txt:
                die(f"lake-manifest.json has no packagesDir and {cf} may set one (Lake would look there, not in the "
                    "bound .lake/packages)")
    p_dir = clean_rel(pm.get("packagesDir") or ".lake/packages", "packagesDir")
    w_dir = clean_rel(wm.get("packagesDir") or ".lake/packages", "workspace packagesDir")
    if has_ctl(proj) or has_ctl(ws):
        die("project / workspace path contains a control character")
    seen = set()
    seen_dirs = {}
    for p in pkgs:
        name = p.get("name")
        if not isinstance(name, str) or not name or "/" in name or name in (".", "..") or has_ctl(name):
            die(f"bad package name {name!r}")
        if name in seen:
            die(f"duplicate package {name!r}")
        seen.add(name)
        if p.get("type") == "path" and p.get("inherited") is False:
            # a project-local path dependency (e.g. vendor/utilities): nothing to
            # bind - Lake loads it from the project inside the sandbox, as the official build does. Its dir must be a
            # clean relative path to a real directory strictly inside the project (no symlink component). The fast
            # build hands such a project to the official build (build.sh lake_target_modules: path require).
            d = clean_rel(p.get("dir"), f"package {name}: path dir")
            dd = confined(os.path.join(proj, os.path.normpath(d)), proj, f"package {name}: path dir")
            if not os.path.isdir(dd):
                die(f"package {name}: path dir {d!r} is not a directory inside the project")
            continue
        if p.get("type") != "git":
            die(f"package {name}: type {p.get('type')!r} is not supported (only git dependencies materialized in the "
                "packages workspace)")
        w = wpk.get(name)
        if w is None:
            die(f"package {name} is not materialized in the packages workspace {ws}")
        for k in FIELDS:
            if p.get(k) != w.get(k):
                die(f"package {name}: {k} differs: project {p.get(k)!r} vs workspace {w.get(k)!r}")
        dname = lake_dir_name(name)
        if dname in seen_dirs:
            die(f"packages {name!r} and {seen_dirs[dname]!r} share the directory {dname!r}")
        seen_dirs[dname] = name
        src = os.path.realpath(os.path.join(ws, w_dir, dname))
        if not os.path.isdir(src):
            die(f"package {name}: {src} missing")
        if has_ctl(src):   # SRC comes from the TRUSTED workspace (w_dir + a name it lists); no control character either
            die(f"package {name}: workspace checkout path {src!r} contains a control character")
        head = git_head(src)
        if head != p.get("rev"):
            die(f"package {name}: checkout {src} is at {head}, manifest wants {p.get('rev')}")
        dst = confined(os.path.join(proj, os.path.normpath(p_dir), dname), proj, f"package {name}: bind destination")
        print(f"{src}\t{dst}")


if __name__ == "__main__":
    main()

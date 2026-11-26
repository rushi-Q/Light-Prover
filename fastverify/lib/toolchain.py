#!/usr/bin/env python3
# fastverify/lib/toolchain.py -- resolve and verify the OFFICIAL Lean toolchain a project pins.
#
# Policy (findings 004 014 020 031 037 040 046 048 050 052 061): the fast flow builds, exports and checks ONLY with the
# unmodified official Lean release binaries that the project's own `lean-toolchain` names -- the same binaries the official
# `lake build` uses. No patched, PGO-rebuilt or differently configured toolchain is ever used (a differently compiled binary
# has different native stack frames -> different stack-overflow band, finding 050; it cannot be proven output-identical per
# run). A toolchain is accepted only if its whole installed tree matches a manifest pinned in fastverify/toolchains/
# (sha256 + mode of every file, every symlink target, no extra/missing entries) and its `lean`/`lake` start and print the
# pinned version lines. Anything else -> exit 2 (DECLINE, fail closed): the caller must not build with it.
#
# usage:
#   toolchain.py resolve PROJECT [--search DIR]... [--json FILE]   -> prints the verified toolchain root; exit 0 / 2
#   toolchain.py verify ROOT ID [--json FILE]                      -> exit 0 / 2
#   toolchain.py pin ROOT ID [--out FILE]                          -> (maintainer) write the manifest of an official install
#   toolchain.py install ROOT ID DEST                              -> copy ROOT to DEST (e.g. a node-local disk), verify copy
# OPT-IN UNSAFE toolchains (build menu option T1, user decision 18:05Z): patched / PGO-rebuilt toolchains that are NOT the
# official release; they diverge from it (findings listed in their manifest). They are pinned separately and verified the same
# way (whole tree + must start), and the result is always marked "unsafe": true:
#   toolchain.py verify-unofficial ROOT NAME [--json FILE]          -> exit 0 / 2; manifest toolchains/unofficial/NAME.json
#   toolchain.py pin-unofficial ROOT NAME --base RELEASE_ID --source TEXT --findings LIST --description TEXT
#                [--lean-version LINE --lake-version LINE]          -> (maintainer) pin; version lines only if lean cannot start here
# ID = the exact toolchain string, e.g. leanprover/lean4:v4.33.1. Search order for resolve: --search dirs (in the given
# order), then ~/.elan/toolchains. Every candidate is verified; the first one that verifies is used. No environment variable
# is read for any decision.
import concurrent.futures as cf, hashlib, json, os, re, shutil, stat, subprocess, sys, time

HERE = os.path.dirname(os.path.realpath(__file__))
PINS = os.path.join(os.path.dirname(HERE), "toolchains")
ID_RE = re.compile(r"^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$")
UNOFF_RE = re.compile(r"^[a-z0-9][a-z0-9._-]{2,80}$")
CLEAN_ENV = {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "HOME": "/nonexistent"}


def dirname_of(tid):            # elan's directory name for a toolchain id
    return tid.replace("/", "--").replace(":", "---")


def pin_path(tid):
    return os.path.join(PINS, dirname_of(tid) + ".json")


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb", buffering=0) as f:
        while True:
            b = f.read(1 << 22)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def scan(root, threads=32):
    """Canonical description of the tree under root (never follows symlinks)."""
    files, links, dirs, other = {}, {}, [], []
    todo = []
    for d, dns, fns in os.walk(root, followlinks=False):
        rd = os.path.relpath(d, root)
        for n in sorted(dns):
            p = os.path.join(d, n); rp = os.path.normpath(os.path.join(rd, n))
            st = os.lstat(p)
            if stat.S_ISLNK(st.st_mode):
                links[rp] = os.readlink(p)
            else:
                dirs.append(rp)
        for n in sorted(fns):
            p = os.path.join(d, n); rp = os.path.normpath(os.path.join(rd, n))
            st = os.lstat(p)
            if stat.S_ISLNK(st.st_mode):
                links[rp] = os.readlink(p)
            elif stat.S_ISREG(st.st_mode):
                todo.append((rp, p, stat.S_IMODE(st.st_mode) & 0o111, st.st_size))
            else:
                other.append(rp)
    with cf.ThreadPoolExecutor(threads) as ex:
        for (rp, p, x, size), h in zip(todo, ex.map(lambda t: sha256_file(t[1]), todo)):
            files[rp] = [h, "x" if x else "-", size]
    return {"files": files, "symlinks": links, "dirs": sorted(dirs), "other": sorted(other)}


def tree_digest(desc):
    s = json.dumps({k: desc[k] for k in ("files", "symlinks", "dirs")}, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(s.encode()).hexdigest()


def run_version(root, tool):
    exe = os.path.join(root, "bin", tool)
    try:
        r = subprocess.run([exe, "--version"], env=CLEAN_ENV, cwd="/", stdin=subprocess.DEVNULL,
                           capture_output=True, timeout=120)
    except Exception as e:  # cannot start = decline
        return None, f"{tool} cannot start: {e}"
    if r.returncode != 0:
        return None, f"{tool} --version exited {r.returncode}: {r.stderr.decode(errors='replace')[:300]}"
    return r.stdout.decode(errors="replace").strip(), None


def unofficial_pin_path(name):
    return os.path.join(PINS, "unofficial", name + ".json")


def verify(root, tid, threads=32, unofficial=False):
    t0 = time.time()
    res = {"id": tid, "root": root, "verified": False, "official": not unofficial}
    if unofficial:
        if not UNOFF_RE.match(tid):
            res["reason"] = f"'{tid}' is not a valid unofficial toolchain name"; return res
        pp = unofficial_pin_path(tid)
        if not os.path.isfile(pp):
            res["reason"] = f"no pinned unofficial manifest {pp}"; return res
    else:
        if not ID_RE.match(tid):
            res["reason"] = f"toolchain '{tid}' is not an official release id leanprover/lean4:vX.Y.Z[-rcN]"
            return res
        pp = pin_path(tid)
        if not os.path.isfile(pp):
            res["reason"] = f"no pinned manifest {pp} for {tid} (run 'toolchain.py pin' on an official install first)"
            return res
    pin = json.load(open(pp))
    res["manifest"] = pp
    if unofficial:
        res.update({"unsafe": True, "base": pin.get("base"), "source": pin.get("source"),
                    "findings": pin.get("findings"), "description": pin.get("description")})
    res["pinned_tree_sha256"] = pin["tree_sha256"]
    if not os.path.isdir(root) or os.path.islink(root):
        res["reason"] = f"{root} is not a real directory (symlinked/linked toolchains are refused)"
        return res
    desc = scan(root, threads)
    problems = []
    if desc["other"]:
        problems.append(f"special files: {desc['other'][:3]}")
    for k in ("files", "symlinks"):
        a, b = pin[k], desc[k]
        miss = sorted(set(a) - set(b)); extra = sorted(set(b) - set(a))
        bad = sorted(p for p in set(a) & set(b) if a[p] != b[p])
        if miss: problems.append(f"{len(miss)} missing {k}, e.g. {miss[:3]}")
        if extra: problems.append(f"{len(extra)} extra {k}, e.g. {extra[:3]}")
        if bad: problems.append(f"{len(bad)} modified {k}, e.g. {bad[:3]}")
    if sorted(pin["dirs"]) != desc["dirs"]:
        problems.append("directory set differs")
    dig = tree_digest(desc)
    res["tree_sha256"] = dig
    if not problems and dig != pin["tree_sha256"]:
        problems.append("tree digest differs")
    if problems:
        res["reason"] = ("toolchain tree does not match the pinned " + ("UNOFFICIAL" if unofficial else "official")
                         + " manifest: " + "; ".join(problems))
        return res
    for tool, key in (("lean", "lean_version"), ("lake", "lake_version")):
        out, err = run_version(root, tool)
        if err:
            res["reason"] = err; return res
        if out != pin[key]:
            res["reason"] = f"{tool} --version prints {out!r}, pinned {pin[key]!r}"; return res
        res[key] = out
    res["verified"] = True
    res["seconds"] = round(time.time() - t0, 3)
    return res


def read_toolchain_id(project):
    p = os.path.join(project, "lean-toolchain")
    if not os.path.isfile(p):
        return None, f"{p} missing: the official `lake build` would use the machine's default toolchain -> refused"
    lines = [l.strip() for l in open(p, encoding="utf-8", errors="strict").read().splitlines() if l.strip()]
    if len(lines) != 1:
        return None, f"{p} must contain exactly one non-empty line, has {len(lines)}"
    return lines[0], None


def emit(res, jf, ok_print=None):
    if jf:
        with open(jf, "w") as f:
            json.dump(res, f, indent=1)
    if res.get("verified"):
        if ok_print: print(ok_print)
        return 0
    print("DECLINE: " + res.get("reason", "?"), file=sys.stderr)
    return 2


def main(a):
    def opt(name, multi=False):
        vals = []
        while name in a:
            i = a.index(name); vals.append(a[i + 1]); del a[i:i + 2]
        return vals if multi else (vals[-1] if vals else None)
    jf = opt("--json"); out = opt("--out"); search = opt("--search", True)
    base = opt("--base"); src = opt("--source"); fnd = opt("--findings"); desc_t = opt("--description")
    lv0 = opt("--lean-version"); kv0 = opt("--lake-version")
    if not a:
        print(open(__file__).read().split("\nimport ")[0]); return 1
    cmd = a[0]
    if cmd == "resolve" and len(a) == 2:
        tid, err = read_toolchain_id(a[1])
        if err:
            return emit({"verified": False, "reason": err}, jf)
        if not ID_RE.match(tid):
            return emit({"id": tid, "verified": False, "reason": f"lean-toolchain '{tid}' is not an official release id "
                         "leanprover/lean4:vX.Y.Z[-rcN] (channels, nightlies, custom/linked toolchains are refused)"}, jf)
        cands = [os.path.join(d, dirname_of(tid)) for d in search] + \
                [os.path.join(os.path.expanduser("~"), ".elan", "toolchains", dirname_of(tid))]
        tried = []
        for c in cands:
            if not os.path.exists(c):
                continue
            r = verify(os.path.realpath(c) if not os.path.islink(c) else c, tid)
            if r["verified"]:
                r["tried"] = tried
                return emit(r, jf, r["root"])
            tried.append({"root": c, "reason": r.get("reason")})
        return emit({"id": tid, "verified": False, "tried": tried,
                     "reason": f"no verified official install of {tid} found (tried {[t['root'] for t in tried] or cands})"}, jf)
    if cmd == "verify" and len(a) == 3:
        r = verify(a[1], a[2])
        return emit(r, jf, r["root"])
    if cmd == "verify-unofficial" and len(a) == 3:
        r = verify(a[1], a[2], unofficial=True)
        if r.get("verified"):
            print(f"WARNING: UNOFFICIAL toolchain {a[2]} (not the release; known divergences: {r.get('findings')})",
                  file=sys.stderr)
        return emit(r, jf, r["root"])
    if cmd == "pin-unofficial" and len(a) == 3:
        root, name = os.path.realpath(a[1]), a[2]
        if not UNOFF_RE.match(name) or not base or not ID_RE.match(base) or not src or not fnd or not desc_t:
            print("pin-unofficial needs a valid NAME, --base RELEASE_ID, --source, --findings, --description", file=sys.stderr)
            return 2
        desc = scan(root)
        if desc["other"]:
            print(f"special files in tree: {desc['other'][:5]}", file=sys.stderr); return 2
        lv, e1 = run_version(root, "lean"); kv, e2 = run_version(root, "lake")
        started = not (e1 or e2)
        if not started:
            if not (lv0 and kv0):
                print((e1 or e2) + " (pass --lean-version/--lake-version recorded on a host where it starts)", file=sys.stderr)
                return 2
            lv, kv = lv0, kv0
        m = {"name": name, "unsafe": True, "base": base, "source": src, "description": desc_t,
             "findings": [x.strip() for x in fnd.split(",") if x.strip()], "lean_version": lv, "lake_version": kv,
             "version_lines_from_this_host": started, "pinned_from": root,
             "pinned_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
             "tree_sha256": tree_digest(desc), "nfiles": len(desc["files"]),
             "bytes": sum(v[2] for v in desc["files"].values()), **{k: desc[k] for k in ("files", "symlinks", "dirs")}}
        out = out or unofficial_pin_path(name)
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out + ".tmp", "w") as f:
            json.dump(m, f, sort_keys=True, separators=(",", ":"))
        os.replace(out + ".tmp", out)
        print(f"pinned UNOFFICIAL {name}: {m['nfiles']} files, {m['bytes']} bytes, tree sha256 {m['tree_sha256']} -> {out}")
        return 0
    if cmd == "pin" and len(a) == 3:
        root, tid = os.path.realpath(a[1]), a[2]
        if not ID_RE.match(tid):
            print(f"not an official release id: {tid}", file=sys.stderr); return 2
        desc = scan(root)
        if desc["other"]:
            print(f"special files in tree: {desc['other'][:5]}", file=sys.stderr); return 2
        lv, e1 = run_version(root, "lean"); kv, e2 = run_version(root, "lake")
        if e1 or e2:
            print(e1 or e2, file=sys.stderr); return 2
        m = {"id": tid, "dirname": dirname_of(tid), "lean_version": lv, "lake_version": kv,
             "pinned_from": root, "pinned_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
             "tree_sha256": tree_digest(desc), "nfiles": len(desc["files"]),
             "bytes": sum(v[2] for v in desc["files"].values()), **{k: desc[k] for k in ("files", "symlinks", "dirs")}}
        out = out or pin_path(tid)
        with open(out + ".tmp", "w") as f:
            json.dump(m, f, sort_keys=True, separators=(",", ":"))
        os.replace(out + ".tmp", out)
        print(f"pinned {tid}: {m['nfiles']} files, {m['bytes']} bytes, tree sha256 {m['tree_sha256']} -> {out}")
        return 0
    if cmd == "install" and len(a) == 4:
        src, tid, dest = a[1], a[2], a[3]
        r = verify(src, tid)
        if not r["verified"]:
            return emit(r, jf)
        tmp = dest.rstrip("/") + ".tmp.%d" % os.getpid()
        shutil.copytree(src, tmp, symlinks=True)
        if os.path.exists(dest):
            shutil.rmtree(dest)
        os.replace(tmp, dest)
        r = verify(dest, tid)
        return emit(r, jf, r["root"])
    print("bad arguments; run without arguments for usage", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

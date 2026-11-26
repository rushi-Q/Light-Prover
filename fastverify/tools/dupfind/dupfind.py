#!/usr/bin/python3 -I
"""dupfind — duplicate-lemma lookup for the daily proving loop. UNTRUSTED analysis tool: it never
produces a verdict; it tells a mathematician or a proving agent "a theorem with exactly this statement already exists".

How it works. The kernel statement of every declaration of a lean4export export is hashed by `exphash`
(`type_hk`: binder names, binder infos, mdata and let-nondep flags ignored; constants by full name; universe levels
structurally with level parameters BY NAME). Two theorems with equal (type_hk, lvl_h) have the same kernel statement up
to binder names and binder infos, i.e. one can be used wherever the other is (proof irrelevance). An index is a sqlite
file over one export (Mathlib, or the live repository's export); a query hashes a candidate `theorem X : T := sorry`
module the same way (compile in the package sandbox -> native exporter E1 -> exphash) and looks every target up in every
index given. Near matches (universe names differ: `type_hu`, computed by the patched exphash when available) are
reported separately with lower confidence.

  dupfind.py index  NAME EXPORT OUT [--exphash BIN] [--decls FILE] [--base DIR ...] [--ilean-root DIR ...] [--jobs N]
  dupfind.py lookup --index DIR [--index DIR ...] (--name N ... | --hash HK[:LVLH] ... | --decls FILE) [--all-kinds] [--aux] [--json]
  dupfind.py query  --index DIR [--index DIR ...] --toolchain TC --packages WS [--fv PKG] [--work DIR] [--targets A,B] [--json] FILE.lean
  dupfind.py report --index DIR [--base DIR] [--aux] [--top N] [--json]
  dupfind.py serve  --index DIR [--index DIR ...] --socket PATH      (one JSON line per connection: {"op":"lookup",...})

Exit: 0 = ran (see output), 2 = could not run. Output: human text, or one JSON object with --json.
"""
import argparse, hashlib, json, os, re, shutil, sqlite3, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.realpath(__file__))
AUX_RE = re.compile(r"(^|\.)(_proof_\d+|_simp_\d+(_\d+)*|_eq_\d+|eq_\d+|eq_def|eq_unfold|_auxLemma\.\d+|match_\d+|proof_\d+|_sunfold|"
                    r"_unfold|_cstage\d*|_spec_\d+|_[a-z]+_\d+(_\d+)*|injEq|sizeOf_spec|noConfusionType|noConfusion|"
                    r"brecOn|binductionOn|below|ibelow|rec|recOn|casesOn|inj|mk\.inj|mk\.injEq|mk\.sizeOf_spec|ctorIdx)$|"
                    r"^_private\.|\._@\.|\._hyg\.|\binst[A-Z]\w*$|^inst[A-Z]")
BWRAP = "/usr/bin/bwrap"


def die(msg, rc=2):
    print(f"dupfind: {msg}", file=sys.stderr)
    sys.exit(rc)


def sha256_file(p, limit=None):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        while True:
            b = f.read(1 << 24)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def is_aux(name):
    return bool(AUX_RE.search(name))


# ------------------------------------------------------------------------------------------------------------ index
def find_exphash(explicit=None):
    for c in ([explicit] if explicit else []) + [os.environ.get("DUPFIND_EXPHASH"), os.path.join(HERE, "bin", "exphash"),
                                                 os.path.join(HERE, "..", "compress", "exphash", "target", "release", "exphash")]:
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return os.path.realpath(c)
    return None


def scan_ileans(roots):
    """name -> (module, line) from the .ilean files below the given build roots (lib/lean trees)."""
    out = {}
    for root in roots:
        for dp, _, fs in os.walk(root):
            for fn in fs:
                if not fn.endswith(".ilean"):
                    continue
                try:
                    d = json.load(open(os.path.join(dp, fn), encoding="utf-8"))
                except Exception:  # noqa: BLE001
                    continue
                mod = d.get("module")
                for n, pos in (d.get("decls") or {}).items():
                    if n not in out and isinstance(pos, list) and pos:
                        out[n] = (mod, pos[0])
    return out


def cmd_index(a):
    out = os.path.realpath(a.out)
    os.makedirs(out, exist_ok=True)
    t0 = time.time()
    decls = a.decls
    exph = find_exphash(a.exphash)
    if not decls:
        if not exph:
            die("no exphash binary (give --exphash or --decls)")
        xd = os.path.join(out, "x")
        shutil.rmtree(xd, ignore_errors=True)
        p = subprocess.run([exph, os.path.realpath(a.export), xd], capture_output=True, text=True)
        if p.returncode != 0:
            die(f"exphash failed: {p.stderr[-800:]}")
        decls = os.path.join(xd, "decls.tsv")
    hu = {}
    hup = os.path.join(os.path.dirname(decls), "hu.tsv")
    if os.path.isfile(hup):
        for ln in open(hup, encoding="utf-8"):
            f = ln.rstrip("\n").split("\t")
            if len(f) >= 2 and f[0] != "name":
                hu[f[0]] = f[1]
    t1 = time.time()
    mods = scan_ileans([os.path.realpath(r) for r in (a.ilean_root or [])])
    t2 = time.time()
    bases = [open_db(b) for b in (a.base or [])]
    dbp = os.path.join(out, "index.sqlite")
    if os.path.exists(dbp):
        os.unlink(dbp)
    db = sqlite3.connect(dbp)
    db.executescript("""
      CREATE TABLE meta(key TEXT PRIMARY KEY, val TEXT);
      CREATE TABLE decls(name TEXT PRIMARY KEY, kind TEXT, nlvl INT, lvl_h TEXT, type_hk TEXT, type_hs TEXT, value_hk TEXT,
                         type_hu TEXT, aux INT, origin TEXT, module TEXT, line INT);
    """)
    rows = []
    n = 0
    with open(decls, encoding="utf-8") as f:
        hdr = f.readline().rstrip("\n").split("\t")
        ki = {h: i for i, h in enumerate(hdr)}
        need = ["kind", "name", "nlvl", "lvl_h", "type_hk", "type_hs", "value_hk"]
        for k in need:
            if k not in ki:
                die(f"{decls}: missing column {k}")
        for ln in f:
            fl = ln.rstrip("\n").split("\t")
            if len(fl) < len(need):
                continue
            name = fl[ki["name"]]
            kind, lvl_h, thk, ths, vhk = fl[ki["kind"]], fl[ki["lvl_h"]], fl[ki["type_hk"]], fl[ki["type_hs"]], fl[ki["value_hk"]]
            origin = a.origin or "project"
            for b in bases:
                r = b.execute("SELECT kind, type_hk, lvl_h FROM decls WHERE name=?", (name,)).fetchone()
                if r and r[0] == kind and r[1] == thk and r[2] == lvl_h:
                    origin = "library"
                    break
            m = mods.get(name)
            rows.append((name, kind, int(fl[ki["nlvl"]] or 0), lvl_h, thk, ths, vhk, hu.get(name), 1 if is_aux(name) else 0,
                         origin, m[0] if m else None, m[1] if m else None))
            n += 1
            if len(rows) >= 50000:
                db.executemany("INSERT OR REPLACE INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?)", rows)
                rows = []
    if rows:
        db.executemany("INSERT OR REPLACE INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?)", rows)
    db.execute("CREATE INDEX i_hk ON decls(type_hk, lvl_h)")
    db.execute("CREATE INDEX i_hu ON decls(type_hu)")
    meta = {"name": a.name, "export": os.path.realpath(a.export) if a.export else None, "decls_tsv": os.path.realpath(decls),
            "created": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "n_decls": n, "bases": a.base or [],
            "ilean_roots": a.ilean_root or [], "modules_known": len(mods), "exphash": exph,
            "exphash_sha256": sha256_file(exph) if exph else None, "hu": bool(hu)}
    if a.export and os.path.isfile(a.export):
        meta["export_size"] = os.path.getsize(a.export)
        with open(a.export, "rb") as f:
            first = f.readline()
        try:
            meta["export_meta"] = json.loads(first).get("meta")
        except Exception:  # noqa: BLE001
            pass
        if not a.no_sha:
            meta["export_sha256"] = sha256_file(a.export)
    db.executemany("INSERT INTO meta VALUES (?,?)", [(k, json.dumps(v)) for k, v in meta.items()])
    db.commit()
    db.close()
    print(json.dumps({"index": dbp, "n_decls": n, "modules_known": len(mods), "seconds": {"exphash": round(t1 - t0, 1),
                      "ileans": round(t2 - t1, 1), "sqlite": round(time.time() - t2, 1), "total": round(time.time() - t0, 1)}}))


# ----------------------------------------------------------------------------------------------------------- lookup
def open_db(d):
    p = os.path.join(d, "index.sqlite") if os.path.isdir(d) else d
    if not os.path.isfile(p):
        die(f"no index at {d}")
    db = sqlite3.connect(f"file:{p}?mode=ro", uri=True)
    db.row_factory = sqlite3.Row
    return db


class Indexes:
    def __init__(self, dirs):
        self.dbs = []
        for d in dirs:
            db = open_db(d)
            name = json.loads(db.execute("SELECT val FROM meta WHERE key='name'").fetchone()[0])
            self.dbs.append((name, db))

    def by_name(self, name):
        for iname, db in self.dbs:
            r = db.execute("SELECT * FROM decls WHERE name=?", (name,)).fetchone()
            if r:
                return iname, dict(r)
        return None, None

    def matches(self, type_hk, lvl_h, type_hu=None, exclude=(), kinds=("thm",), aux=False):
        out = []
        for iname, db in self.dbs:
            q = "SELECT * FROM decls WHERE type_hk=?" + ("" if lvl_h is None else " AND lvl_h=?")
            for r in db.execute(q, (type_hk,) if lvl_h is None else (type_hk, lvl_h)):
                r = dict(r)
                if r["name"] in exclude or (kinds and r["kind"] not in kinds) or (not aux and r["aux"]):
                    continue
                r["index"] = iname
                r["match"] = "statement" if lvl_h is not None else "statement (universe-parameter list not compared)"
                out.append(r)
            if type_hu:
                for r in db.execute("SELECT * FROM decls WHERE type_hu=? AND type_hk<>?", (type_hu, type_hk)):
                    r = dict(r)
                    if r["name"] in exclude or (kinds and r["kind"] not in kinds) or (not aux and r["aux"]):
                        continue
                    r["index"] = iname
                    r["match"] = "near (universe names differ)"
                    out.append(r)
        out.sort(key=lambda r: (r["match"] != "statement", r["aux"], r["origin"] != "project", r["name"]))
        return out


def fmt_match(r):
    loc = f" ({r['module']}:{r['line']})" if r.get("module") else ""
    return f"{r['name']}{loc} [{r['index']}, {r['kind']}, {r['origin']}{', aux' if r['aux'] else ''}; {r['match']}]"


def cmd_lookup(a):
    ix = Indexes(a.index)
    kinds = () if a.all_kinds else ("thm",)
    res = []
    items = []
    for n in a.name or []:
        iname, r = ix.by_name(n)
        if not r:
            items.append({"query": n, "error": "name not in any index"})
            continue
        items.append({"query": n, "name": n, "index": iname, "kind": r["kind"], "type_hk": r["type_hk"], "lvl_h": r["lvl_h"],
                      "matches": ix.matches(r["type_hk"], r["lvl_h"], r.get("type_hu"), exclude={n}, kinds=kinds, aux=a.aux)})
    for h in a.hash or []:
        hk, _, lh = h.partition(":")
        items.append({"query": h, "type_hk": hk, "lvl_h": lh or None,
                      "matches": ix.matches(hk, lh or None, None, kinds=kinds, aux=a.aux)})
    if a.decls:
        with open(a.decls, encoding="utf-8") as f:
            hdr = f.readline().rstrip("\n").split("\t")
            ki = {h: i for i, h in enumerate(hdr)}
            for ln in f:
                fl = ln.rstrip("\n").split("\t")
                if fl[ki["kind"]] != "thm" or (not a.aux and is_aux(fl[ki["name"]])):
                    continue
                items.append({"query": fl[ki["name"]], "type_hk": fl[ki["type_hk"]], "lvl_h": fl[ki["lvl_h"]],
                              "matches": ix.matches(fl[ki["type_hk"]], fl[ki["lvl_h"]], None, exclude={fl[ki["name"]]},
                                                    kinds=kinds, aux=a.aux)})
    emit(items, a.json)


def emit(items, as_json):
    for it in items:
        it["duplicate"] = any(m["match"] == "statement" for m in it.get("matches", []))
    if as_json:
        print(json.dumps({"tool": "dupfind", "items": items}, ensure_ascii=False))
        return
    for it in items:
        if it.get("error"):
            print(f"{it['query']}: {it['error']}")
            continue
        ms = it.get("matches", [])
        if not ms:
            print(f"{it['query']}: unique (no theorem with this statement in the indexes)")
        else:
            print(f"{it['query']}: {'DUPLICATE' if it['duplicate'] else 'near matches'} - {len(ms)} match(es)")
            for m in ms[:10]:
                print("    " + fmt_match(m))


# ------------------------------------------------------------------------------------------------------------ query
DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma)\s+([^\s:({\[⦃]+)", re.M)


def header_of(text):
    """the header of a Lean file = everything up to the first non-import, non-blank, non-comment line (what the
    official `--incr-header-save` snapshot covers)."""
    out = []
    for ln in text.splitlines(keepends=True):
        t = ln.strip()
        if t == "" or t.startswith("import ") or t.startswith("--") or t.startswith("prelude"):
            out.append(ln)
        else:
            break
    return "".join(out)


def sandbox(tc, ro, rw, env, chdir):
    a = [BWRAP, "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run/user", "--tmpfs", "/tmp",
         "--dir", "/tmp/home", "--tmpfs", "/run", "--tmpfs", "/var", "--dev", "/dev", "--proc", "/proc", "--clearenv",
         "--ro-bind", tc, tc]
    for p in ro:
        a += ["--ro-bind", p, p]
    for p in rw:
        a += ["--bind", p, p]
    e = {"PATH": f"{tc}/bin:/usr/bin:/bin", "HOME": "/tmp/home", "LANG": "C.UTF-8"}
    e.update(env or {})
    for k, v in e.items():
        a += ["--setenv", k, v]
    return a + ["--unshare-all", "--die-with-parent", "--new-session", "--chdir", chdir, "--"]


def cmd_query(a):
    t0 = time.time()
    ix = Indexes(a.index)
    tc = os.path.realpath(a.toolchain)
    ws = os.path.realpath(a.packages)
    ws_pk = os.path.join(ws, ".lake", "packages")
    fv = os.path.realpath(a.fv or os.path.join(HERE, "..", ".."))
    src = os.path.realpath(a.file)
    text = open(src, encoding="utf-8").read()
    names = a.targets.split(",") if a.targets else [m.group(2) for m in DECL_RE.finditer(text)]
    if not names:
        die("no theorem/lemma in the file (or give --targets)")
    # namespaces: a plain `namespace N` ... `end N` prefix is applied best-effort; names with explicit prefixes are kept
    ns = []
    full = []
    for ln in text.splitlines():
        m = re.match(r"^\s*namespace\s+([^\s]+)", ln)
        if m:
            ns.append(m.group(1))
        m = re.match(r"^\s*end\s+([^\s]+)", ln)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
        m = DECL_RE.match(ln)
        if m and m.group(2) in names:
            full.append(".".join(ns + [m.group(2)]) if ns else m.group(2))
    targets = full if full and not a.targets else names
    work = os.path.realpath(a.work) if a.work else tempfile.mkdtemp(prefix="dupfind-", dir=a.work_dir or None)
    proj = os.path.join(work, "proj")
    lib = os.path.join(proj, "build", "lib", "lean")
    os.makedirs(lib, exist_ok=True)
    modname = "DupQuery"
    shutil.copyfile(src, os.path.join(proj, modname + ".lean"))
    lp_ws = ":".join(os.path.join(ws_pk, d, ".lake", "build", "lib", "lean") for d in sorted(os.listdir(ws_pk)))
    # 0. optional warm path: the official lean's header snapshot of exactly this file's header (import lines), built once
    #    per header under --snapshot DIR (as tools/batchverify.py does); untrusted speed-up, same official elaborator
    snap_opts, snap_ro, snap_s = [], [], 0.0
    if a.snapshot:
        hdr = header_of(text)
        key = hashlib.sha256((tc + "\n" + ws + "\n" + hdr).encode()).hexdigest()[:16]
        sd = os.path.join(os.path.realpath(a.snapshot), key)
        sf = os.path.join(sd, "hdr.snap")
        if not os.path.isfile(sf):
            ts = time.time()
            tmp = tempfile.mkdtemp(prefix="tmp.", dir=os.path.realpath(a.snapshot))
            open(os.path.join(tmp, "Hdr.lean"), "w", encoding="utf-8").write(hdr)
            pa = sandbox(tc, ro=[ws_pk], rw=[tmp], env={"LEAN_PATH": lp_ws}, chdir=tmp) + [
                os.path.join(tc, "bin", "lean"), "--incr-header-save=" + os.path.join(tmp, "hdr.snap"), os.path.join(tmp, "Hdr.lean")]
            ps = subprocess.run(pa, capture_output=True, text=True, env={})
            if ps.returncode == 0 and os.path.isfile(os.path.join(tmp, "hdr.snap")):
                try:
                    os.rename(tmp, sd)
                except OSError:
                    shutil.rmtree(tmp, ignore_errors=True)
            else:
                shutil.rmtree(tmp, ignore_errors=True)
            snap_s = round(time.time() - ts, 2)
        if os.path.isfile(sf):
            snap_opts, snap_ro = ["--incr-load=" + sf], [sd]
    # 1. compile in the package sandbox (untrusted candidate code: no network, home hidden, only `lib` writable)
    t1 = time.time()
    argv = sandbox(tc, ro=[ws_pk, proj] + snap_ro, rw=[lib], env={"LEAN_PATH": lp_ws}, chdir=proj) + [
        os.path.join(tc, "bin", "lean"), *snap_opts, "-o", os.path.join(lib, modname + ".olean"), "-i", os.path.join(lib, modname + ".ilean"),
        os.path.join(proj, modname + ".lean")]
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=a.timeout, env={})
    except subprocess.TimeoutExpired:
        die(f"compile timed out after {a.timeout} s")
    t2 = time.time()
    if p.returncode != 0:
        out = {"tool": "dupfind", "error": "compile failed", "compiler_output": (p.stdout + p.stderr)[-4000:],
               "seconds": {"compile": round(t2 - t1, 2)}}
        print(json.dumps(out) if a.json else f"compile failed:\n{out['compiler_output']}")
        sys.exit(1)
    # 2. native export of the targets' closure (E1, sandboxed, closure guard)
    tf = os.path.join(work, "targets.txt")
    open(tf, "w", encoding="utf-8").write("\n".join(targets) + "\n")
    binds = os.path.join(work, "binds.tsv")
    open(binds, "w", encoding="utf-8").write(f"{ws_pk}\t{ws_pk}\n")
    exp = os.path.join(work, "query.export")
    if a.fast_export:
        # the pinned native exporter directly (same sandbox and arguments as export/export.sh's native run, without the
        # per-call preflight and closure guard: this is an analysis tool, a bad export can only give a wrong hint)
        comp = json.load(open(os.path.join(fv, "export", "components.json")))
        nat = comp["native"]["path"]
        pa = sandbox(tc, ro=[ws_pk, proj, os.path.dirname(nat)], rw=[], env={"LEAN_PATH": lp_ws + ":" + lib, "LEAN_ABORT_ON_PANIC": "1",
                     "LEAN4EXPORT_VERBOSE": "0", "LEAN_NUM_THREADS": str(a.threads)}, chdir=proj) + [nat, modname, "--", *targets]
        with open(exp, "wb") as fo:
            p = subprocess.run(pa, stdout=fo, stderr=subprocess.PIPE, env={})
        t3 = time.time()
        if p.returncode != 0:
            die(f"native export failed (exit {p.returncode}): {p.stderr.decode(errors='replace')[-1500:]}")
    else:
        p = subprocess.run([os.path.join(fv, "export", "export.sh"), "--lean-path", lp_ws + ":" + lib, "--module", modname,
                            "--targets-nl", tf, "--toolchain", tc, "--project", proj, "--binds", binds, "--out", exp,
                            "--threads", str(a.threads), "--json", os.path.join(work, "export.json")],
                           capture_output=True, text=True, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"})
        t3 = time.time()
        if p.returncode != 0:
            die(f"export failed (exit {p.returncode}): {(p.stdout + p.stderr)[-1500:]}")
    # 3. hash
    exph = find_exphash(a.exphash)
    if not exph:
        die("no exphash binary")
    xd = os.path.join(work, "x")
    shutil.rmtree(xd, ignore_errors=True)
    p = subprocess.run([exph, exp, xd], capture_output=True, text=True)
    if p.returncode != 0:
        die(f"exphash failed: {p.stderr[-800:]}")
    t4 = time.time()
    rows = {}
    with open(os.path.join(xd, "decls.tsv"), encoding="utf-8") as f:
        hdr = f.readline().rstrip("\n").split("\t")
        ki = {h: i for i, h in enumerate(hdr)}
        for ln in f:
            fl = ln.rstrip("\n").split("\t")
            rows[fl[ki["name"]]] = fl
    hu = {}
    hup = os.path.join(xd, "hu.tsv")
    if os.path.isfile(hup):
        for ln in open(hup, encoding="utf-8"):
            f2 = ln.rstrip("\n").split("\t")
            if len(f2) >= 2:
                hu[f2[0]] = f2[1]
    items = []
    seen = {}
    for t in targets:
        fl = rows.get(t)
        if not fl:
            items.append({"query": t, "error": "not in the export (not a theorem of this module?)"})
            continue
        key = (fl[ki["type_hk"]], fl[ki["lvl_h"]])
        it = {"query": t, "kind": fl[ki["kind"]], "type_hk": key[0], "lvl_h": key[1], "type_hu": hu.get(t),
              "matches": ix.matches(key[0], key[1], hu.get(t), exclude={t}, kinds=() if a.all_kinds else ("thm",), aux=a.aux)}
        if key in seen:
            it["same_statement_in_file"] = seen[key]
        seen.setdefault(key, t)
        items.append(it)
    secs = {"compile": round(t2 - t1, 2), "export": round(t3 - t2, 2), "hash": round(t4 - t3, 2),
            "lookup": round(time.time() - t4, 3), "total": round(time.time() - t0, 2), "snapshot_build": snap_s,
            "warm": bool(snap_opts), "fast_export": bool(a.fast_export)}
    if a.json:
        for it in items:
            it["duplicate"] = any(m["match"] == "statement" for m in it.get("matches", []))
        print(json.dumps({"tool": "dupfind", "file": src, "module": modname, "targets": targets, "items": items,
                          "seconds": secs, "work": work, "export_sha256": sha256_file(exp)}, ensure_ascii=False))
    else:
        emit(items, False)
        print(f"[dupfind] compile {secs['compile']} s, export {secs['export']} s, hash {secs['hash']} s, lookup {secs['lookup']} s")
    if not a.work and not a.keep:
        shutil.rmtree(work, ignore_errors=True)


# ----------------------------------------------------------------------------------------------------------- report
def cmd_report(a):
    ix = Indexes([a.index])
    _, db = ix.dbs[0]
    base = Indexes([a.base]) if a.base else None
    q = "SELECT name, type_hk, lvl_h, module, line FROM decls WHERE kind='thm' AND origin='project'" + ("" if a.aux else " AND aux=0")
    rows = db.execute(q).fetchall()
    if a.module_prefix:   # restrict to the project's own modules (module known from .ilean files)
        pre = tuple(a.module_prefix.split(","))
        rows = [r for r in rows if r[3] and r[3].startswith(pre)]
    classes = {}
    for r in rows:
        classes.setdefault((r[1], r[2]), []).append(r[0])
    multi = sorted([v for v in classes.values() if len(v) >= 2], key=lambda v: -len(v))
    restated = []
    if base:
        for r in rows:
            ms = base.matches(r[1], r[2], None, kinds=("thm",), aux=a.aux)
            if ms:
                restated.append({"name": r[0], "module": r[3], "line": r[4], "library": [m["name"] for m in ms[:5]]})
    rep = {"tool": "dupfind", "index": a.index, "module_prefix": a.module_prefix, "project_theorems": len(rows), "same_statement_classes": len(multi),
           "redundant_theorems": sum(len(v) - 1 for v in multi), "restating_library": len(restated),
           "classes": multi[:a.top], "restated": restated[:a.top]}
    if a.json:
        print(json.dumps(rep, ensure_ascii=False))
    else:
        print(f"project theorems {rep['project_theorems']}: {rep['same_statement_classes']} same-statement classes, "
              f"{rep['redundant_theorems']} redundant theorems; {rep['restating_library']} restate a library theorem")
        for v in multi[:a.top]:
            print("  " + " == ".join(v[:6]) + (f" (+{len(v) - 6})" if len(v) > 6 else ""))
        for r in restated[:a.top]:
            print(f"  {r['name']} restates {', '.join(r['library'][:3])}")


# ------------------------------------------------------------------------------------------------------------ delta
def cmd_delta(a):
    """new or changed theorems of NEW_EXPORT (vs the base indexes) whose statement already exists elsewhere: the duplicate
    alert of a merge / PR gate (fvwork, CI): `dupfind delta --index IX_base [--index IX_lib ...] NEW.export`"""
    t0 = time.time()
    ix = Indexes(a.index)
    exph = find_exphash(a.exphash)
    if not exph:
        die("no exphash binary")
    work = tempfile.mkdtemp(prefix="dupdelta-", dir=a.work_dir or None)
    p = subprocess.run([exph, os.path.realpath(a.export), os.path.join(work, "x")], capture_output=True, text=True)
    if p.returncode != 0:
        die(f"exphash failed: {p.stderr[-800:]}")
    t1 = time.time()
    new_rows = []
    allnew = {}
    with open(os.path.join(work, "x", "decls.tsv"), encoding="utf-8") as f:
        hdr = f.readline().rstrip("\n").split("\t")
        ki = {h: i for i, h in enumerate(hdr)}
        for ln in f:
            fl = ln.rstrip("\n").split("\t")
            name, kind, thk, lh = fl[ki["name"]], fl[ki["kind"]], fl[ki["type_hk"]], fl[ki["lvl_h"]]
            if kind == "thm":
                allnew.setdefault((thk, lh), []).append(name)
            if kind != "thm" or (not a.aux and is_aux(name)):
                continue
            _, r = ix.by_name(name)
            if r is None or r["type_hk"] != thk or r["lvl_h"] != lh:
                new_rows.append((name, thk, lh, "new" if r is None else "restated"))
    items = []
    for name, thk, lh, status in new_rows:
        ms = ix.matches(thk, lh, None, exclude={name}, kinds=("thm",), aux=a.aux)
        within = [n for n in allnew.get((thk, lh), []) if n != name and (a.aux or not is_aux(n))]
        for n in within:
            if not any(m["name"] == n for m in ms):
                ms.append({"name": n, "index": "(new export)", "kind": "thm", "origin": "project", "aux": 0, "module": None,
                           "line": None, "match": "statement"})
        if ms:
            items.append({"query": name, "status": status, "type_hk": thk, "lvl_h": lh, "matches": ms, "duplicate": True})
    rep = {"tool": "dupfind", "op": "delta", "export": os.path.realpath(a.export), "new_or_changed_theorems": len(new_rows),
           "duplicates_introduced": len(items), "items": items, "seconds": {"hash": round(t1 - t0, 2), "total": round(time.time() - t0, 2)}}
    shutil.rmtree(work, ignore_errors=True)
    if a.json:
        print(json.dumps(rep, ensure_ascii=False))
    else:
        print(f"{rep['new_or_changed_theorems']} new or changed theorems, {rep['duplicates_introduced']} with a statement that already exists")
        for it in items[:a.top]:
            print(f"  {it['query']} ({it['status']}): " + "; ".join(fmt_match(m) for m in it["matches"][:4]))


# ------------------------------------------------------------------------------------------------------------ serve
def cmd_serve(a):
    import socket
    ix = Indexes(a.index)
    if os.path.exists(a.socket):
        os.unlink(a.socket)
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.bind(a.socket)
    os.chmod(a.socket, 0o600)
    s.listen(64)
    print(json.dumps({"serving": a.socket, "indexes": [n for n, _ in ix.dbs]}), flush=True)
    while True:
        c, _ = s.accept()
        try:
            data = b""
            while not data.endswith(b"\n") and len(data) < 1 << 20:
                b = c.recv(65536)
                if not b:
                    break
                data += b
            req = json.loads(data.decode("utf-8"))
            if req.get("op") == "stop":
                c.sendall(b'{"ok":true}\n')
                c.close()
                break
            if req.get("op") == "lookup":
                if "name" in req:
                    iname, r = ix.by_name(req["name"])
                    res = {"name": req["name"], "index": iname, "matches": ix.matches(r["type_hk"], r["lvl_h"], r.get("type_hu"),
                                                                                       exclude={req["name"]}, aux=bool(req.get("aux"))) if r else []}
                else:
                    res = {"matches": ix.matches(req["type_hk"], req.get("lvl_h"), req.get("type_hu"), aux=bool(req.get("aux")))}
                res["duplicate"] = any(m["match"] == "statement" for m in res["matches"])
                c.sendall((json.dumps(res, ensure_ascii=False) + "\n").encode("utf-8"))
            else:
                c.sendall(b'{"error":"unknown op"}\n')
        except Exception as e:  # noqa: BLE001
            try:
                c.sendall((json.dumps({"error": str(e)}) + "\n").encode("utf-8"))
            except Exception:  # noqa: BLE001
                pass
        finally:
            c.close()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    p = sp.add_parser("index"); p.set_defaults(f=cmd_index)
    p.add_argument("name"); p.add_argument("export", nargs="?"); p.add_argument("out")
    p.add_argument("--exphash"); p.add_argument("--decls", help="reuse an existing exphash decls.tsv instead of running exphash")
    p.add_argument("--base", action="append", help="index dir: declarations identical there are marked origin=library")
    p.add_argument("--ilean-root", action="append", help="lib/lean tree with .ilean files (name -> module:line)")
    p.add_argument("--no-sha", action="store_true", help="do not sha256 the export (big exports)")
    p.add_argument("--origin", choices=("project", "library"), help="origin label of every declaration (default project; "
                   "declarations identical to a --base index are always 'library')")
    p.add_argument("--jobs", type=int, default=1)
    p = sp.add_parser("lookup"); p.set_defaults(f=cmd_lookup)
    p.add_argument("--index", action="append", required=True); p.add_argument("--name", action="append")
    p.add_argument("--hash", action="append"); p.add_argument("--decls"); p.add_argument("--all-kinds", action="store_true")
    p.add_argument("--aux", action="store_true", help="include auto-generated declarations (_proof_N, _simp_N, instances, ...)")
    p.add_argument("--json", action="store_true")
    p = sp.add_parser("query"); p.set_defaults(f=cmd_query)
    p.add_argument("file"); p.add_argument("--index", action="append", required=True)
    p.add_argument("--toolchain", required=True); p.add_argument("--packages", required=True); p.add_argument("--fv")
    p.add_argument("--work"); p.add_argument("--work-dir"); p.add_argument("--keep", action="store_true")
    p.add_argument("--targets"); p.add_argument("--threads", type=int, default=4); p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--exphash"); p.add_argument("--all-kinds", action="store_true"); p.add_argument("--aux", action="store_true")
    p.add_argument("--snapshot", help="directory for official header snapshots (warm compile: --incr-header-save/--incr-load)")
    p.add_argument("--fast-export", action="store_true", help="call the pinned native exporter directly (no per-call preflight)")
    p.add_argument("--json", action="store_true")
    p = sp.add_parser("report"); p.set_defaults(f=cmd_report)
    p.add_argument("--index", required=True); p.add_argument("--base"); p.add_argument("--aux", action="store_true")
    p.add_argument("--module-prefix", help="only theorems whose module (from .ilean) starts with one of these comma-separated prefixes")
    p.add_argument("--top", type=int, default=20); p.add_argument("--json", action="store_true")
    p = sp.add_parser("delta"); p.set_defaults(f=cmd_delta)
    p.add_argument("export"); p.add_argument("--index", action="append", required=True); p.add_argument("--exphash")
    p.add_argument("--aux", action="store_true"); p.add_argument("--work-dir"); p.add_argument("--top", type=int, default=50)
    p.add_argument("--json", action="store_true")
    p = sp.add_parser("serve"); p.set_defaults(f=cmd_serve)
    p.add_argument("--index", action="append", required=True); p.add_argument("--socket", required=True)
    a = ap.parse_args()
    a.f(a)


if __name__ == "__main__":
    main()

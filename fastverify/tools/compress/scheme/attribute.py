#!/usr/bin/env python3
"""attribute.py MANIFEST_DIR FAILURES.tsv OUTDIR --decls DECLS.tsv [--src ORIG_SRC] [--chainmerge FILE] [--quarantine N]

Failure -> owner-key attribution for an integration train (stage-3 triage; untrusted, read-only).

  MANIFEST_DIR/manifest.tsv  owner<TAB>edit-list file (priority order; files relative to MANIFEST_DIR)
  FAILURES.tsv               failures.py output: module, error class, identifiers, line, decl kind, decl name, message
  --decls DECLS.tsv          declaration index of the ORIGINAL tree (prune.py's <report>.decls.tsv:
                             module start end kind live deleted names[,names])
  --src ORIG_SRC             original sources (src/ of the frozen base): decides whether a missing name was used there
  --chainmerge FILE          the train's member<TAB>kept chain-merge map (t2/.chainmerge.tsv): a failing kept module stands
                             for its merged members too

For every failing module: the owners whose edits touch it (via the merge map), and for an 'Unknown identifier/constant
X' or 'ambiguous' error the owner whose edit REMOVED X (delete / deletefile / replace covering X's declaration in the
original tree) or RENAMED it (subst X NEW). Recommendation per failure:
  * X removed by owner R and X is used by the module's ORIGINAL text -> deny R in X's defining module (restore X);
  * X not in the original text (introduced by an owner's subst / replace) -> deny that introducer in the failing module;
  * other errors -> deny the touching owners of the module, lowest priority first (the most recently composed list).
Writes OUTDIR/report.tsv, OUTDIR/deny/<owner>.txt (modules, for edits_deny.py) and prints a summary incl. owners above
the quarantine threshold (default > 5 failures attributed to one owner -> quarantine it from the next freeze).
"""
import argparse, collections, os, re, sys

ap = argparse.ArgumentParser()
ap.add_argument("manifest_dir"); ap.add_argument("failures"); ap.add_argument("outdir")
ap.add_argument("--decls", required=True); ap.add_argument("--src"); ap.add_argument("--chainmerge")
ap.add_argument("--quarantine", type=int, default=5)
ap.add_argument("--risk", default="P03-dedup,D19-defdedup,P01r4,P01r3,P01r2,P01,P06,P05-dhe,D18-rename,D18-docs,P07-stmtfmt",
                help="owner keys from most to least likely to break a module semantically (fallback order)")
a = ap.parse_args()

owners, lists = [], {}
for ln in open(os.path.join(a.manifest_dir, "manifest.tsv"), encoding="utf-8"):
    p = ln.rstrip("\n").split("\t")
    if len(p) >= 2 and p[0] and not p[0].startswith("#"):
        owners.append(p[0]); lists[p[0]] = p[1] if os.path.isabs(p[1]) else os.path.join(a.manifest_dir, p[1])
prio = {o: i for i, o in enumerate(owners)}

decls = collections.defaultdict(list)          # module -> [(start, end, kind, [names])]
for ln in open(a.decls, encoding="utf-8"):
    if ln.startswith("#"):
        continue
    p = ln.rstrip("\n").split("\t")
    if len(p) < 7:
        continue
    try:
        decls[p[0]].append((int(p[1]), int(p[2]), p[3], [x for x in p[6].split(",") if x]))
    except ValueError:
        pass

shorts = {n.rsplit(".", 1)[-1] for ds in decls.values() for (_, _, _, names) in ds for n in names}
hazard = collections.defaultdict(set)                  # module -> {(owner, note)}: renames onto an existing short name
touch = collections.defaultdict(collections.Counter)   # module -> owner -> #edits
removed = collections.defaultdict(list)                # full name -> [(owner, module, action)]
renamed = collections.defaultdict(list)                # OLD -> [(owner, module, NEW)]
changed = collections.defaultdict(list)                # full name -> [(owner, module)] (declaration rewritten in place)
inserts = collections.defaultdict(list)                # module -> [(owner, line)]
deletes = collections.defaultdict(list)                # module -> [(owner, start, end, action)]
introduced = collections.defaultdict(list)             # module -> [(owner, text)] (subst NEW / replacement texts)
for o in owners:
    for ln in open(lists[o], encoding="utf-8"):
        p = ln.rstrip("\n").split("\t", 5)
        if len(p) < 5:
            continue
        mod, act = p[0], p[3]
        try:
            s, e = int(p[1]), int(p[2])
        except ValueError:
            continue
        rep = p[5] if len(p) > 5 else ""
        touch[mod][o] += 1
        if act == "subst":
            old, _, new = rep.partition(" ")
            renamed[old].append((o, mod, new)); introduced[mod].append((o, new))
            ns, os_ = new.rsplit(".", 1)[-1], old.rsplit(".", 1)[-1]
            if ns != os_ and ns in shorts:   # the new short name is already a project declaration's: shadowing hazard
                hazard[mod].add((o, "%s -> %s: the new short name %s also names another project declaration (possible shadowing)" % (old, new, ns)))
            continue
        if act in ("replace", "insert_before", "newfile"):
            introduced[mod].append((o, rep))
        if act == "insert_before":
            inserts[mod].append((o, s))
        if act in ("delete", "deletefile"):
            deletes[mod].append((o, s, e, act))
        if act in ("delete", "replace", "deletefile"):
            for (ds, de, kind, names) in decls.get(mod, ()):
                if act == "deletefile" or (s <= ds and de <= e):
                    for n in names:
                        short = n.rsplit(".", 1)[-1]
                        if act == "replace" and re.search(r"(?<![\w.'])" + re.escape(short) + r"(?![\w'])", rep):
                            changed[n].append((o, mod))   # still declared, but its text (binders, statement) may differ
                            continue
                        removed[n].append((o, mod, act))

members = collections.defaultdict(list)
if a.chainmerge and os.path.exists(a.chainmerge):
    for ln in open(a.chainmerge, encoding="utf-8"):
        p = ln.split()
        if len(p) == 2:
            members[p[1]].append(p[0])

def orig_text(mod):
    if not a.src:
        return None
    try:
        return open(os.path.join(a.src, mod.replace(".", "/") + ".lean"), encoding="utf-8").read()
    except OSError:
        return ""

risk = {o: i for i, o in enumerate(a.risk.split(","))}

def introducers(origs, ids):
    out = []
    for x in [i for i in ids.split(",") if i][:3]:
        short = x.rsplit(".", 1)[-1]
        for m in origs:
            for (o, txt) in introduced.get(m, ()):
                if re.search(r"(?<![\w'])" + re.escape(short) + r"(?![\w'])", txt) and (o, m) not in out:
                    out.append((o, m))
    return out

def match_names(x, table):
    if x in table:
        return [x]
    hits = [n for n in table if n.endswith("." + x) or x.endswith("." + n)]
    return hits[:5]

MISSING = re.compile(r"[Uu]nknown (identifier|constant)|ambiguous|unknown namespace|does not have|not found")
NONCOMP = re.compile(r"consider marking it as 'noncomputable'")
PARSE = re.compile(r"unexpected end of input|unexpected token")
IMPCLASH = re.compile(r"import (\S+) failed, environment already contains '([^']+)' from (\S+)")
DUPDECL = re.compile(r"has already been declared")
os.makedirs(os.path.join(a.outdir, "deny"), exist_ok=True)
deny = collections.defaultdict(set)
stages = collections.defaultdict(set)
blame = collections.Counter()
rows = []
for ln in open(a.failures, encoding="utf-8"):
    f = ln.rstrip("\n").split("\t")
    if not f or not f[0]:
        continue
    f += [""] * (7 - len(f))
    mod, cls, ids, line, dk, dn, msg = f[:7]
    origs = [mod] + members.get(mod, [])
    t = collections.Counter()
    for m in origs:
        t.update(touch.get(m, {}))
    recs, why, stage = [], "", ""
    clash = IMPCLASH.search(msg)
    if clash:   # import-time clash: two imported modules declare the same (often auxiliary) constant -> blame THOSE modules
        x_mod, cname, y_mod = clash.group(1), clash.group(2), clash.group(3).rstrip(".")
        if y_mod not in touch and not members.get(y_mod):   # failures.py truncates long messages: complete by prefix
            full = sorted(m2 for m2 in touch if m2.startswith(y_mod))
            if len(full) == 1:
                y_mod = full[0]
        inv = {mm: k for k, v in members.items() for mm in v}
        cand = []
        for mm in (y_mod, x_mod):
            for m2 in [mm] + members.get(mm, []) + ([inv[mm]] if mm in inv else []):
                if m2 not in cand:
                    cand.append(m2)
        aux = bool(re.search(r"\._(abel|proof|simp|aux|eq|unfold)_|\.match_\d", cname))
        tt = collections.Counter()
        for m2 in cand:
            tt.update(touch.get(m2, {}))
        pref = ["P06", "P05-dhe"] if aux else []
        order = sorted(tt, key=lambda o: (0 if o in pref else 1, risk.get(o, len(risk))))
        if order:
            o = order[0]
            recs = [(o, m2) for m2 in cand if touch.get(m2, {}).get(o)]
            why = "import clash on %s%s between %s and %s; %s edits them" % (cname, " (auxiliary: numbering changed by a proof edit)" if aux else "", x_mod, y_mod, o)
        else:
            why = "import clash on %s between %s and %s (no owner edits: base/pipeline)" % (cname, x_mod, y_mod)
    if not recs and PARSE.search(cls + " " + msg):   # parse error: an insert anchored inside code another owner deleted
        for m in origs:
            for (io, il) in inserts.get(m, ()):
                for (do, ds, de, act) in deletes.get(m, ()):
                    if io != do and (act == "deletefile" or ds <= il <= de + 1):
                        if (io, m) not in recs:
                            recs.append((io, m))
                            why += "%s inserts at line %d, inside/after code %s deletes (%s %d-%d) -> dangling text (insert_guard class); " % (io, il, do, act, ds, de)
    if recs:
        pass
    elif NONCOMP.search(cls + " " + msg):
        stage = "normalize:ncs"
        why = "pipeline: 'noncomputable section' removed by normalize (class ncs) from a module whose proofs compile auxiliary definitions"
    elif DUPDECL.search(cls + " " + msg) and introducers(origs, ids):
        recs = introducers(origs, ids)
        why = "duplicate declaration introduced by " + ", ".join("%s in %s" % r for r in recs)
    elif DUPDECL.search(cls + " " + msg) and members.get(mod):
        stage = "chainmerge"
        why = "pipeline: chain-merge group %s declares a name twice -> cm_deny.py / chainmerge --deny" % ",".join(origs)
    elif MISSING.search(cls + " " + msg):
        texts = [orig_text(m) for m in origs]
        for x in [i for i in ids.split(",") if i][:3]:
            short = x.rsplit(".", 1)[-1]
            used = None
            if a.src:
                used = any(tx and re.search(r"(?<![\w'])" + re.escape(short) + r"(?![\w'])", tx) for tx in texts)
            R = [(o, dm, act, n) for n in match_names(x, removed) for (o, dm, act) in removed[n]]
            I = [(o, m) for m in origs for (o, txt) in introduced.get(m, ()) if short in txt] if used is False else []
            N = [(o, dm, n, new) for n in match_names(x, renamed) for (o, dm, new) in renamed[n] if dm in origs]
            for (o, dm, act, n) in R:
                why += "%s removed %s (%s of %s); " % (o, n, act, dm)
            for (o, m) in I:
                why += "%s introduced %s in %s; " % (o, x, m)
            for (o, dm, n, new) in N:
                why += "%s renamed %s -> %s in %s; " % (o, n, new, dm)
            if I:          # narrowest repair: give the failing module its own text back for the introducing owner(s)
                recs += I
            elif N:
                recs += [(o, dm) for (o, dm, _, _) in N]
            elif R:        # the module used X originally: restore X where it was removed
                recs += [(o, dm) for (o, dm, _, _) in R]
    if not recs and not stage and ids:   # a named constant whose declaration an owner rewrote (binder names, statement)
        for x in [i for i in ids.split(",") if i][:3]:
            for n in match_names(x, changed):
                for (o, dm) in changed[n]:
                    if (o, dm) not in recs:
                        recs.append((o, dm)); why += "%s rewrote the declaration of %s in %s; " % (o, n, dm)
    if not recs and not stage:   # a rename onto an existing project short name (name resolution changes silently)
        for m in origs:
            for (o, note) in sorted(hazard.get(m, ())):
                if (o, m) not in recs:
                    recs.append((o, m)); why += "%s: %s; " % (o, note)
    if not recs and not stage:   # no name-level cause: the touching owners, most semantically risky first (--risk)
        order = sorted(t, key=lambda o: (risk.get(o, len(risk)), -prio.get(o, 0)))
        why += "touched by " + ", ".join("%s(%d)" % (o, t[o]) for o in sorted(t, key=lambda o: prio.get(o, 0))) if t else "no owner edits (base / pipeline)"
        recs = [(o, m) for o in order[:1] for m in origs if touch.get(m, {}).get(o)]
        if recs:
            why += " -> riskiest toucher %s (deny the next one if the rebuild still fails)" % order[0]
    seen = []
    for r in recs:
        if r not in seen:
            seen.append(r)
    for (o, m) in seen:
        deny[o].add(m); blame[o] += 1
    if stage:
        stages[stage].add(mod)
    rows.append((mod, cls, ids, ";".join("%s@%s" % r for r in seen) or ("pipeline:" + stage if stage else "-"), why.strip() or "-",
                 ",".join("%s:%d" % (o, t[o]) for o in sorted(t, key=lambda o: prio.get(o, 0)))))

with open(os.path.join(a.outdir, "report.tsv"), "w", encoding="utf-8") as fo:
    fo.write("#module\terror\tidentifiers\tdeny(owner@module)\twhy\ttouching owners(edits)\n")
    for r in rows:
        fo.write("\t".join(r) + "\n")
for o, ms in deny.items():
    with open(os.path.join(a.outdir, "deny", o + ".txt"), "w", encoding="utf-8") as fo:
        fo.write("".join(m + "\n" for m in sorted(ms)))
print("failures %d; deny rows per owner: %s" % (len(rows), dict(sorted(((o, len(m)) for o, m in deny.items()), key=lambda x: -x[1]))))
for st, ms in stages.items():
    with open(os.path.join(a.outdir, "pipeline-" + st.replace(":", "-") + ".txt"), "w", encoding="utf-8") as fo:
        fo.write("".join(m + "\n" for m in sorted(ms)))
    print("pipeline cause %s: %d module(s) -> %s/pipeline-%s.txt" % (st, len(ms), a.outdir, st.replace(":", "-")))
q = [o for o, n in blame.items() if n > a.quarantine]
print("quarantine (> %d failures attributed): %s" % (a.quarantine, ", ".join(q) or "none"))
print("repair: python3 edits_deny.py LIST OUT %s/deny/<owner>.txt for each owner; then rebuild the cone (tools/incr)" % a.outdir)

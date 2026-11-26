#!/usr/bin/python3 -I
"""dedup_filter_v2.py PLAN EDITS SRC SCAN_DIR IMPORTS_JSON OUT [--deny FILE] [--jobs N]

Hardened Stage-3 filter for DEDUP.c1r_v2 (keeping --cp-guard IMPORT edits at 0.0% failures!):
  1. Preserves all dedup_filter.py guards: SHORT, NOSUBST, DANGLING, NAMED, unmapped drop, _root_. target rooting.
  2. OPEN_PRIVATE guard: drops any redirect whose name appears on an `open private ...` line anywhere in the tree.
  3. OPEN_CLAUSE_REF guard: drops any redirect whose short name appears in `open <NS> hiding/renaming/(...)` in any
     importer (prevents Lean `Unknown constant` errors on `open ... hiding` clauses!).
  4. APPLY_BOUNDARY guard: drops any redirect if any exact occurrence in a `subst` module is preceded by a character
     (e.g. `‖`, `↑`, `¬`) not matched by `apply_edits.py`'s lookbehind regex.
  5. TRANSITIVE ALREADY_DECLARED_IMPORT guard: blocks any added `(mod, tmod)` import whose transitive new modules
     `trans(tmod) - trans(mod)` declare a full constant name already declared in `mod` / `rdeps[mod]` or their
     existing transitive imports.
  6. TRANSITIVE AMBIGUOUS_IMPORT guard (exact two-constant + Mathlib-ns collision check): blocks any added `(mod, tmod)`
     import whose transitive new modules `trans(tmod) - trans(mod)` introduce a public `(ns1, short)` where `ns1` is
     opened in `ma` (`mod` or direct importer), `short` is used in `ma`, AND either `ma` already has another visible
     `(ns2, short)` (`ns2 != ns1`) in an opened namespace or `ns1` is a root/Mathlib namespace.
  7. Orphan insert_before pruning: drops any `import T` line from `insert_before` edits when all edits in that module
     requiring `T` were dropped (zero unneeded imports left behind!).
"""
import argparse
import collections
import glob
import json
import os
import re
import sys
from multiprocessing import Pool

_LL = (
    "A-Za-z0-9_'!?"
    "α-κμ-ωΑ-ΟΡ΢Τ-Ωϊ-ϻἀ-῾"
    "℀-⅏\U0001d49c-\U0001d59f₀-₉ₐ-ₜᵢ-ᵪⱼ"
)
TOK = re.compile("[" + _LL + "]+(?:\\.[" + _LL + "]+)*")
NAMED = re.compile(r"\(\s*[A-Za-z_α-ω][A-Za-z0-9_'α-ω₀-₉]*\s*:=")
OPEN_PRIV = re.compile(r"^\s*open\s+private\s+(.+?)\s+from\b")
OPEN_NS = re.compile(r"^\s*open\s+(?!private\b)(?:scoped\s+)?(.+)")
OPEN_HIDING = re.compile(r"^\s*open\s+(?!private\b)(?:scoped\s+)?([^\n]+?)\s+(?:hiding|renaming)\s+([^\n]+)")
OPEN_PAREN = re.compile(r"^\s*(?:open\s+(?!private\b)(?:scoped\s+)?|export\s+)([A-Za-z_α-ω][" + _LL + r".]*)\s*\(([^)]+)\)")
NS_DECL = re.compile(r"^\s*namespace\s+([A-Za-z_α-ω][" + _LL + r".]*)")
DECL_HEAD_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|opaque|axiom|instance)\s+([^\s:({\[⦃]+)"
)
CLOSE = {")": "(", "]": "[", "}": "{", "⟩": "⟨"}
TOKCH = re.compile("[" + _LL + ".@]")
MODIN = re.compile(r"\bin\s*(?:--.*)?$")
# Exact lookbehind/lookahead from tools/compress/dedup/apply_edits.py L111
APPLY_LB_CH = set(" \t\r\n()[]{}⟨⟩,;@←·$`|:=<>+*/\\^&!~-")
AUTO_RE = re.compile(
    r"(?:\.eq_\d+|\.eq_def|\.eq_unfold|\.congr_simp|\.congr_eq|\._sunfold|\._cstage\d+"
    r"|\.induct|\.fun_cases|\._proof_\d+|\._simp_\d+|\.match_\d+|\._unary|\._override"
    r"|\._sparseCasesOn_\d+|\.else_eq|\.splitter|\.eqn_\d+|\.injEq|\.sizeOf_spec)$"
)
PROJECT_ROOTS = {
    "GlobalTheory", "Formalism", "ReciprocityTheory", "Development", "CompanionTheory",
    "GroundTheory", "PositivityTheory", "Reformulated", "UpperTheory", "PI", "Lemmata",
    "Main", "Statements", "Supplements", "RootFieldNumerics",
}


def app_tokens(line, p):
    out = []
    i = p - 1
    while i >= 0:
        ch = line[i]
        if ch.isspace():
            i -= 1
            continue
        if ch in CLOSE:
            depth = 0
            while i >= 0:
                if line[i] in CLOSE:
                    depth += 1
                elif line[i] in CLOSE.values():
                    depth -= 1
                i -= 1
                if depth == 0:
                    break
            continue
        if TOKCH.match(ch):
            j = i
            while j >= 0 and TOKCH.match(line[j]):
                j -= 1
            out.append(line[j + 1 : i + 1].lstrip("@"))
            i = j
            continue
        break
    return out


# Globals initialized before fork
G_SRC = ""
G_SHORTS = set()
G_REDIR_NAMES = set()
G_CHECK_OPEN_MODS = set()


def scan_mod(mod):
    p = os.path.join(G_SRC, mod.replace(".", "/") + ".lean")
    try:
        lines = open(p, encoding="utf-8").read().split("\n")
    except OSError:
        return mod, [], [], [], [], None, None, None
    hits = []
    named = []
    open_privs = []
    open_clause_refs = []  # (ns_or_empty, short)
    check_open = mod in G_CHECK_OPEN_MODS
    opened_ns = set() if check_open else None
    used_shorts = set() if check_open else None
    own_decl_shorts = set() if check_open else None
    for k, line in enumerate(lines, 1):
        s = line.lstrip()
        if s.startswith("--"):
            continue
        code = line.split("--", 1)[0]
        m_op = OPEN_PRIV.match(code)
        if m_op:
            for t in TOK.findall(m_op.group(1)):
                if t in G_REDIR_NAMES:
                    open_privs.append(t)
        m_oh = OPEN_HIDING.match(code)
        if m_oh:
            nss = [x.strip() for x in m_oh.group(1).split() if x.strip()]
            rhs = m_oh.group(2)
            for t in TOK.findall(rhs):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_SHORTS:
                    for ns in nss:
                        open_clause_refs.append((ns, sh))
                    open_clause_refs.append(("", sh))
        m_opar = OPEN_PAREN.match(code)
        if m_opar:
            ns = m_opar.group(1)
            for t in TOK.findall(m_opar.group(2)):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_SHORTS:
                    open_clause_refs.append((ns, sh))
        if check_open:
            m_on = OPEN_NS.match(code)
            if m_on:
                body = re.split(r"\b(?:hiding|renaming|in)\b", m_on.group(1), maxsplit=1)[0]
                if "(" not in body:
                    for tok in body.split():
                        if tok and tok[0].isalpha() and tok not in ("scoped", "in"):
                            opened_ns.add(tok.strip("()"))
            m_ns = NS_DECL.match(code)
            if m_ns:
                ns = m_ns.group(1)
                parts = ns.split(".")
                for i in range(1, len(parts) + 1):
                    opened_ns.add(".".join(parts[:i]))
            m_dh = DECL_HEAD_RE.match(code)
            if m_dh:
                own_decl_shorts.add(m_dh.group(1).rsplit(".", 1)[-1])
        for mo in TOK.finditer(code):
            t = mo.group(0)
            c = t.rsplit(".", 1)[-1]
            if c in G_SHORTS:
                st = mo.start()
                lb_ok = (st == 0) or (code[st - 1] in APPLY_LB_CH)
                hits.append((k, t, lb_ok))
            if check_open:
                used_shorts.add(c)
        for mo in NAMED.finditer(code):
            for t in app_tokens(code, mo.start()):
                c = t.rsplit(".", 1)[-1]
                if c in G_SHORTS:
                    named.append(c)
    return mod, hits, named, open_privs, open_clause_refs, opened_ns, used_shorts, own_decl_shorts


def main():
    global G_SRC, G_SHORTS, G_REDIR_NAMES, G_CHECK_OPEN_MODS
    ap = argparse.ArgumentParser()
    ap.add_argument("plan")
    ap.add_argument("edits")
    ap.add_argument("src")
    ap.add_argument("scan_dir")
    ap.add_argument("imports_json")
    ap.add_argument("out")
    ap.add_argument("--deny", action="append", default=[])
    ap.add_argument("--protect-from", default=None)
    ap.add_argument("--jobs", type=int, default=32)
    ap.add_argument("--no-ambig-guard", action="store_true")
    a = ap.parse_args()

    prot = set()
    if a.protect_from and os.path.isfile(a.protect_from):
        cj = json.load(open(a.protect_from))
        prot = set(cj.get("theorem_names", [])) | set(cj.get("definition_names", []))

    # plan[name] = (act, mod, tgt, tmod, l1, l2)
    plan = {}
    by_mod = collections.defaultdict(list)
    with open(a.plan, encoding="utf-8") as f:
        for ln in f:
            p = ln.rstrip("\n").split("\t")
            if p[0] == "group" or len(p) < 13:
                continue
            act, name, mod, tgt, tmod = p[1], p[2], p[3], p[4], p[5]
            if act in ("KEEP", "KEEP_BINFO"):
                continue
            plan[name] = (act, mod, tgt, tmod, int(p[11]), int(p[12]))
            by_mod[mod].append(name)

    edits = [ln.rstrip("\n").split("\t", 5) for ln in open(a.edits, encoding="utf-8")]
    member_of = {}
    subst_of = collections.defaultdict(list)
    subst_mods = collections.defaultdict(set)
    own_range = {}
    kind = {}
    del_range = {}
    unmapped = 0
    unmapped_edits = set()

    for i, e in enumerate(edits):
        if e[3] == "subst":
            old = e[5].split(" ", 1)[0]
            subst_of[old].append(i)
            subst_mods[old].add(e[0])
            if int(e[1]) > 0:
                own_range[old] = (e[0], int(e[1]), int(e[2]))
    own_by_end = {(mod, t): old for old, (mod, s, t) in own_range.items()}
    plan_of = {}
    for i, e in enumerate(edits):
        mod, s, t, act = e[0], int(e[1]), int(e[2]), e[3]
        if act not in ("replace", "delete"):
            continue
        cands = [n for n in by_mod.get(mod, ()) if plan[n][5] == t or (s <= plan[n][4] and plan[n][5] <= t)]
        pn = cands[0] if len(cands) == 1 else None
        if act == "delete" and (mod, t) in own_by_end:
            m = own_by_end[(mod, t)]
        elif pn is not None:
            m = pn
        else:
            unmapped += 1
            unmapped_edits.add(i)
            continue
        member_of[i] = m
        kind[m] = "alias" if act == "replace" else "redirect"
        if pn is not None:
            plan_of[m] = pn
        if act == "delete":
            del_range[m] = (mod, s, t)
    for m in own_range:
        kind[m] = "redirect"

    members = set(kind)
    short = {m: m.rsplit(".", 1)[-1] for m in members}
    names_by_short = collections.defaultdict(set)
    for m, s in short.items():
        names_by_short[s].add(m)

    # Load import graph
    imp_raw = json.load(open(a.imports_json))
    imp = {m: [d for d in v.get("imports", ()) if d in imp_raw] for m, v in imp_raw.items()}
    rdeps = collections.defaultdict(set)
    for m, ds in imp.items():
        for d in ds:
            rdeps[d].add(m)

    import_adding_mods = set()
    added_edges = []  # (m0, tmod)
    for e in edits:
        if e[3] == "insert_before":
            m0 = e[0]
            import_adding_mods.add(m0)
            for line in e[5].split("\\n"):
                if line.startswith("import "):
                    tmod = line.split()[1]
                    added_edges.append((m0, tmod))

    check_open_mods = set(import_adding_mods)
    for m in import_adding_mods:
        check_open_mods |= rdeps.get(m, set())

    G_SRC = a.src
    G_SHORTS = set(names_by_short)
    G_REDIR_NAMES = {m for m in members if kind[m] == "redirect"}
    G_CHECK_OPEN_MODS = check_open_mods

    mods = []
    for root, _, files in os.walk(a.src):
        for fn in files:
            if fn.endswith(".lean"):
                mods.append(os.path.relpath(os.path.join(root, fn), a.src)[:-5].replace("/", "."))

    unsafe = collections.defaultdict(set)
    named_short = set()
    open_priv_hits = set()
    open_clause_hits = set()  # full member name or (ns, sh)
    mod_opened_ns = {}
    mod_used_shorts = {}
    mod_own_decl_shorts = {}

    with Pool(a.jobs) as pool:
        for mod, hits, named, oprivs, ocrefs, ons, ush, ods in pool.imap_unordered(scan_mod, mods, chunksize=64):
            named_short.update(named)
            open_priv_hits.update(oprivs)
            for ns, sh in ocrefs:
                for m in names_by_short[sh]:
                    if kind[m] != "redirect":
                        continue
                    m_ns = m.rsplit(".", 1)[0] if "." in m else ""
                    if ns == "" or m_ns == ns or m_ns.endswith("." + ns):
                        open_clause_hits.add(m)
            if ons is not None:
                mod_opened_ns[mod] = ons
                mod_used_shorts[mod] = ush
                mod_own_decl_shorts[mod] = ods
            for k, t, lb_ok in hits:
                c = t.rsplit(".", 1)[-1]
                for m in names_by_short[c]:
                    if kind[m] != "redirect":
                        continue
                    r = own_range.get(m)
                    if r and r[0] == mod and r[1] <= k <= r[2]:
                        continue
                    exact = t == m or t == "_root_." + m
                    if exact and mod in subst_mods[m]:
                        if not lb_ok:
                            unsafe[m].add("APPLY_BOUNDARY")
                        continue
                    unsafe[m].add("SHORT" if not exact else "NOSUBST")

    # DANGLING check
    dangling = set()
    cache = {}
    for m, (mod, s0, t0) in del_range.items():
        if mod not in cache:
            try:
                cache[mod] = open(os.path.join(a.src, mod.replace(".", "/") + ".lean"), encoding="utf-8").read().split("\n")
            except OSError:
                cache[mod] = []
        L = cache[mod]
        k = s0 - 2
        while k >= 0 and not L[k].strip():
            k -= 1
        if k >= 0 and MODIN.search(L[k]) and not L[k].lstrip().startswith("--"):
            dangling.add(m)

    # TRANSITIVE AMBIGUOUS_IMPORT + ALREADY_DECLARED_IMPORT checks over scan2/out!
    ambig_pairs = set()    # (m0, tmod)
    already_pairs = set()  # (m0, tmod)
    if not a.no_ambig_guard and added_edges:
        all_opened_ns = set()
        for ons in mod_opened_ns.values():
            all_opened_ns |= ons

        # Single pass over scan2/out:
        # 1) Track all public (ns, sh) where ns in all_opened_ns (for AMBIGUOUS_IMPORT)
        # 2) Track duplicate full names declared in >=2 modules (for ALREADY_DECLARED_IMPORT)
        cname_first_mod = {}
        dup_cname_mods = collections.defaultdict(set)
        mod_pub_by_ns = collections.defaultdict(lambda: collections.defaultdict(set))  # mod -> ns -> {sh}
        for fp in sorted(glob.glob(os.path.join(a.scan_dir, "c*.tsv"))):
            with open(fp, encoding="utf-8", errors="replace") as f:
                for ln in f:
                    if not ln.startswith("K\t"):
                        continue
                    p = ln.split("\t", 5)
                    if len(p) < 4:
                        continue
                    cm, cname = p[1], p[3]
                    if cname.startswith("_private.") or "._proof_" in cname or "._simp_" in cname or ".match_" in cname or "._sparseCasesOn_" in cname or AUTO_RE.search(cname):
                        continue
                    prev = cname_first_mod.get(cname)
                    if prev is None:
                        cname_first_mod[cname] = cm
                    elif prev != cm:
                        dup_cname_mods[cname].add(prev)
                        dup_cname_mods[cname].add(cm)
                    if "." in cname:
                        ns, sh = cname.rsplit(".", 1)
                    else:
                        ns, sh = "", cname
                    if ns in all_opened_ns:
                        mod_pub_by_ns[cm][ns].add(sh)
        del cname_first_mod

        mod_dup_cnames = collections.defaultdict(set)
        for cname, ms in dup_cname_mods.items():
            for cm in ms:
                mod_dup_cnames[cm].add(cname)

        # Build fast topological bitmasks ONLY over relevant modules (those with pub decls in opened_ns OR dup_cnames)
        rel_mods = sorted(set(mod_pub_by_ns.keys()) | set(mod_dup_cnames.keys()))
        rel_idx = {m: i for i, m in enumerate(rel_mods)}
        dup_rel_mask = 0
        for m in mod_dup_cnames:
            dup_rel_mask |= 1 << rel_idx[m]

        # Topo order of full import graph
        topo = []
        state = {}
        for m0 in imp:
            if m0 in state:
                continue
            st = [(m0, iter(imp[m0]))]
            state[m0] = 1
            while st:
                u, it = st[-1]
                nxt = None
                for v in it:
                    if v not in state:
                        nxt = v
                        break
                if nxt is None:
                    st.pop()
                    state[u] = 2
                    topo.append(u)
                else:
                    state[nxt] = 1
                    st.append((nxt, iter(imp[nxt])))

        # Compute transitive bitmask over rel_mods for every module
        tmask = {}
        for m in topo:
            mk = (1 << rel_idx[m]) if m in rel_idx else 0
            for d in imp[m]:
                mk |= tmask.get(d, 0)
            tmask[m] = mk

        def iter_bits(mask):
            while mask:
                lsb = mask & -mask
                yield rel_mods[lsb.bit_length() - 1]
                mask ^= lsb

        # Cache existing visible (sh -> set of ns) per check_open_mod (lazily, only if needed)
        ma_dup_cache = {}
        def get_ma_dups(ma):
            if ma in ma_dup_cache:
                return ma_dup_cache[ma]
            res = set()
            for cm in iter_bits(tmask.get(ma, 0) & dup_rel_mask):
                res |= mod_dup_cnames[cm]
            ma_dup_cache[ma] = res
            return res

        ma_vis_cache = {}
        def get_ma_vis(ma):
            """For ma, map each used short name -> set of opened namespaces that already declare it in trans(ma)."""
            if ma in ma_vis_cache:
                return ma_vis_cache[ma]
            ons = mod_opened_ns.get(ma, set())
            ush = mod_used_shorts.get(ma, set())
            vis = collections.defaultdict(set)
            if ons and ush:
                for cm in iter_bits(tmask.get(ma, 0)):
                    mp = mod_pub_by_ns.get(cm)
                    if not mp:
                        continue
                    for ns in ons:
                        shs = mp.get(ns)
                        if shs:
                            for sh in (shs & ush):
                                vis[sh].add(ns)
            ma_vis_cache[ma] = vis
            return vis

        seen_edges = set()
        for m0, tmod in added_edges:
            if (m0, tmod) in seen_edges:
                continue
            seen_edges.add((m0, tmod))
            tm_mk = tmask.get(tmod, 0)
            if not tm_mk:
                continue
            affected = [m0] + list(rdeps.get(m0, ()))
            for ma in affected:
                ma_mk = tmask.get(ma, 0)
                new_mk = tm_mk & ~ma_mk
                if not new_mk:
                    continue
                # 1. ALREADY_DECLARED_IMPORT check
                new_dup_mk = new_mk & dup_rel_mask
                if new_dup_mk:
                    cur_dups = get_ma_dups(ma)
                    if cur_dups:
                        hit_dup = False
                        for nm in iter_bits(new_dup_mk):
                            if mod_dup_cnames[nm] & cur_dups:
                                already_pairs.add((m0, tmod))
                                hit_dup = True
                                break
                        if hit_dup:
                            break
                # 2. EXACT TRANSITIVE AMBIGUOUS_IMPORT check
                ons = mod_opened_ns.get(ma)
                ush = mod_used_shorts.get(ma)
                if not ons or not ush:
                    continue
                vis = None
                hit_ambig = False
                for nm in iter_bits(new_mk):
                    mp = mod_pub_by_ns.get(nm)
                    if not mp:
                        continue
                    for ns in ons:
                        shs = mp.get(ns)
                        if not shs:
                            continue
                        overlap = shs & ush
                        if not overlap:
                            continue
                        if vis is None:
                            vis = get_ma_vis(ma)
                        root_ns = ns.split(".", 1)[0]
                        own_ds = mod_own_decl_shorts.get(ma, set())
                        for sh in overlap:
                            ex_nss = vis.get(sh)
                            # True Lean Ambiguous term: another opened namespace already provides `sh`,
                            # OR `ma` itself declares a (possibly private) decl with short name `sh` (e.g. GrpRel.nU_val),
                            # OR `ns` is a non-project/Mathlib/root namespace (where existing decls may be in Mathlib).
                            if (ex_nss and (len(ex_nss) > 1 or ns not in ex_nss)) or (sh in own_ds) or (root_ns not in PROJECT_ROOTS):
                                ambig_pairs.add((m0, tmod))
                                hit_ambig = True
                                break
                        if hit_ambig:
                            break
                    if hit_ambig:
                        break
                if hit_ambig:
                    break

    deny = set()
    for f in a.deny:
        deny |= {l.strip() for l in open(f) if l.strip() and not l.startswith("#")}

    # Map each member -> set of (mod_needing_import, tmod)
    member_imp_edges = collections.defaultdict(set)
    for m in members:
        pinfo = plan.get(plan_of.get(m, m))
        if not pinfo:
            continue
        pact, pmod, ptgt, ptmod, _, _ = pinfo
        if pact in ("IMPORT", "SHARED") and ptmod:
            if kind[m] == "alias":
                member_imp_edges[m].add((pmod, ptmod))
            else:
                for um in subst_mods.get(m, ()):
                    member_imp_edges[m].add((um, ptmod))

    drop = {}
    for m in members:
        if m in prot or plan_of.get(m, m) in prot:
            drop[m] = "PROTECTED"
        elif m in open_priv_hits:
            drop[m] = "OPEN_PRIVATE"
        elif m in open_clause_hits:
            drop[m] = "OPEN_CLAUSE_REF"
        elif m in unsafe:
            drop[m] = sorted(unsafe[m])[0]
        elif m in dangling:
            drop[m] = "DANGLING"
        elif short[m] in named_short:
            drop[m] = "NAMED"
        elif m in deny or short[m] in deny:
            drop[m] = "DENY"
        elif any(edge in already_pairs for edge in member_imp_edges.get(m, ())):
            drop[m] = "ALREADY_DECLARED_IMPORT"
        elif any(edge in ambig_pairs for edge in member_imp_edges.get(m, ())):
            drop[m] = "AMBIGUOUS_IMPORT"

    # Recompute exact (mod, tmod) imports STILL NEEDED by kept edits!
    needed_imports = collections.defaultdict(set)
    for m in members:
        if m in drop:
            continue
        for (imod, tmod) in member_imp_edges.get(m, ()):
            if imod != tmod:
                needed_imports[imod].add(tmod)

    cnt = collections.Counter()
    kept = collections.Counter()
    lines_kept = 0
    lines_dropped = 0
    with open(a.out, "w", encoding="utf-8") as fo:
        for i, e in enumerate(edits):
            act = e[3]
            if act == "insert_before":
                imod = e[0]
                want = needed_imports.get(imod, set())
                orig_imps = [ln for ln in e[5].split("\\n") if ln.strip()]
                keep_imps = [ln for ln in orig_imps if ln.startswith("import ") and ln.split()[1] in want]
                dropped_n = len(orig_imps) - len(keep_imps)
                cnt["orphan_imports_pruned"] += dropped_n
                if not keep_imps:
                    cnt["edit_dropped_insert_before"] += 1
                    continue
                e = e[:5] + ["\\n".join(keep_imps)]
                kept["insert_before"] += 1
                kept["import_lines_kept"] += len(keep_imps)
                fo.write("\t".join(e) + "\n")
                continue
            if act == "subst":
                m, nw = e[5].split(" ", 1)
                if m in drop:
                    cnt["edit_dropped_subst"] += 1
                    continue
                if not nw.startswith("_root_."):
                    e = e[:5] + [m + " _root_." + nw]
                    cnt["subst_target_rooted"] += 1
            elif i in unmapped_edits:
                cnt["edit_dropped_unmapped_" + act] += 1
                continue
            elif i in member_of and member_of[i] in drop:
                cnt["edit_dropped_" + act] += 1
                lines_dropped += int(e[2]) - int(e[1]) + 1
                continue
            if act in ("replace", "delete"):
                lines_kept += int(e[2]) - int(e[1]) + 1
            kept[act] += 1
            fo.write("\t".join(e) + "\n")

    why = collections.Counter(drop.values())
    bykind = collections.Counter((kind[m], drop[m]) for m in drop)
    print("members", len(members), dict(collections.Counter(kind.values())), "unmapped", unmapped)
    print("dropped members", len(drop), dict(why))
    print("by kind", dict(bykind))
    print("already_pairs", len(already_pairs), "ambig_pairs", len(ambig_pairs))
    print("edits kept", dict(kept), "dropped", dict(cnt), "lines_kept", lines_kept, "lines_dropped", lines_dropped)
    with open(a.out + ".dropped.tsv", "w", encoding="utf-8") as f:
        for m, w in sorted(drop.items()):
            f.write(f"{m}\t{kind[m]}\t{plan.get(plan_of.get(m, m), ('?',))[0]}\t{w}\n")

    K = [l.rstrip("\n").split("\t", 5) for l in open(a.out, encoding="utf-8")]
    dels = {(e[0], int(e[2])) for e in K if e[3] == "delete"}
    owns = {(e[0], int(e[2])) for e in K if e[3] == "subst" and int(e[1]) > 0}
    bad = owns - dels
    print("self-check: own-module substs without delete:", len(bad))
    if bad:
        sys.exit(3)


if __name__ == "__main__":
    main()

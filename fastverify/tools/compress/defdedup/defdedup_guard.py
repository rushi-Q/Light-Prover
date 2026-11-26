#!/usr/bin/python3 -I
"""defdedup_guard.py DEFPLAN_TSV EDITS_TSV SRC SCAN_DIR IMPORTS_JSON OUT_TSV [--jobs 32]

Hardened Stage-3 P5 tree-wide safety filter for tools/compress/defdedup:
  1. PROTECTED & PRIVATE_TARGET: never touch protected comparator decls; never redirect/alias to `_private.*` targets.
  2. BINFO_MISMATCH: requires exact kernel binder-info match (`binfo[name] == binfo[target]` from dupscan col 12).
  3. RW_UNFOLD (stage-3 guard P5): scans ALL 175k source files for identifiers inside `rw/erw/rwa/simp/simp_all/dsimp/
     simp_rw/norm_num/push_neg/field_simp [...]` and `unfold/delta/dsimp ...`. Drops any `replace` (alias) whose name
     or short name appears in RW_UNFOLD anywhere in its transitive importer cone (closes PsiScal.cT!).
  4. EXT_USED: drops any local `delete` that has external kernel users or external source mentions in its importer cone.
  5. OPEN_CLAUSE_REF & OPEN_PRIVATE: drops any `delete` whose short name is referenced in `open <NS> hiding/renaming/(...)`
     or `open private ...` in any module in its importer cone (closes RkVolSeam `Unknown constant mat`!).
  6. TRANSITIVE ALREADY_DECLARED_IMPORT & AMBIGUOUS_IMPORT: blocks any added `import tmod` whose transitive new modules
     `trans(tmod) - trans(ma)` declare a full constant already in `ma` / `trans(ma)` or create a namespace ambiguity.
  7. NAMED_ARG: drops any edit whose short name is called with named arguments `(x := ...)` in its cone (replace) or
     module (delete).
  8. LOCAL SUBST SAFETY (for `delete` + bare `short` subst):
     - SHORT_NAME_LT3 (`len(short) < 3`)
     - DOT_NOTATION (field `.short` in `mod`)
     - APPLY_BOUNDARY (occurrence of `short`/`un` preceded by a char like `‖`/`↑` not matched by `apply_edits.py` L111)
     - SHORT_DOT_PREFIX (`short.` as prefix of another decl/name in `mod`, e.g. `NormOne.one`)
     - SHORT_DECL_COLLISION (`short` is the head name of ANOTHER decl in `mod`, e.g. `FactorialMulTruncLog.IsLog`)
     - TACTIC_POS (`short` used at tactic position in `mod`, e.g. `ext j`)
     - LOCAL_INSTANCE (`instance` mentioning `short` in `mod`)
  9. ORPHAN_IMPORT pruning + emits `OUT_TSV.cone.txt` (all kept edited modules + all direct importers).
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
TAC_BRACKET_RE = re.compile(
    r"\b(?:rw|erw|rwa|simp|simp_all|dsimp|simp_rw|norm_num|push_neg|field_simp)\s*(?:only\s*)?\["
)
TAC_UNFOLD_RE = re.compile(r"\b(?:unfold|delta|dsimp)\s+([^\n;·]+)")
NAMED_RE = re.compile(r"\(\s*[A-Za-z_α-ω][A-Za-z0-9_'α-ω₀-₉]*\s*:=")
OPEN_PRIV = re.compile(r"^\s*open\s+private\s+(.+?)\s+from\b")
OPEN_NS = re.compile(r"^\s*open\s+(?!private\b)(?:scoped\s+)?(.+)")
OPEN_HIDING = re.compile(r"^\s*open\s+(?!private\b)(?:scoped\s+)?([^\n]+?)\s+(?:hiding|renaming)\s+([^\n]+)")
OPEN_PAREN = re.compile(r"^\s*(?:open\s+(?!private\b)(?:scoped\s+)?|export\s+)([A-Za-z_α-ω][" + _LL + r".]*)\s*\(([^)]+)\)")
NS_DECL = re.compile(r"^\s*namespace\s+([A-Za-z_α-ω][" + _LL + r".]*)")
DECL_HEAD_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|opaque|axiom|instance)\s+([^\s:({\[⦃]+)"
)
APPLY_LB = r"(?<![^\s()\[\]{}⟨⟩,;@←·$`|:=<>+*/\\^&!~-])"
APPLY_LA = r"(?![A-Za-z0-9_'!?\u0370-\u03ff\u1f00-\u1ffe\u2100-\u214f\u2080-\u209c\u1d62-\u1d6a\u2c7c])"
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
CLOSE = {")": "(", "]": "[", "}": "{", "⟩": "⟨"}
TOKCH = re.compile("[" + _LL + ".@]")
LEAN_TACTICS_KW = {
    "ext", "ext1", "ring", "ring1", "ring_nf", "simp", "simpa", "dsimp", "simp_all", "simp_rw",
    "omega", "exact", "apply", "intro", "intros", "rintro", "introv", "cases", "rcases",
    "obtain", "refine", "have", "haveI", "let", "letI", "exactI", "show", "from", "calc",
    "congr", "rfl", "rw", "erw", "rwa", "nth_rw", "assoc_rw", "unfold", "delta", "split",
    "split_ifs", "use", "exists", "induction", "linarith", "nlinarith", "polyrith",
    "linear_combination", "positivity", "gcongr", "norm_num", "field_simp", "push_neg",
    "contrapose", "by_contra", "by_cases", "clear", "revert", "subst", "specialize",
    "aesop", "tauto", "itauto", "abel", "abel_nf", "group", "continuity", "measurability",
    "fun_prop", "bound", "norm_cast", "push_cast", "exact_mod_cast", "assumption",
    "contradiction", "exfalso", "symm", "trans", "swap", "rotate", "focus", "first",
    "repeat", "try", "done", "decide", "trivial", "constructor", "left", "right",
    "change", "generalize", "rename", "suffices", "set", "mod_cases", "fin_cases",
    "interval_cases", "grind", "funext", "propext", "convert", "all_goals", "any_goals",
    "case", "next", "skip", "fail", "admit", "sorry", "classical", "choose", "lift",
    "wlog", "peel", "filter_upwards", "zify", "qify", "rify", "conv", "conv_lhs",
    "conv_rhs", "arg", "enter", "lhs", "rhs", "whnf", "reduce", "injection", "injections",
    "absurd", "match", "with", "fun", "if", "then", "else", "by", "in", "at", "as", "do",
    "return", "for", "while", "where", "open", "end", "namespace", "section", "variable",
    "universe", "attribute", "set_option", "import", "export", "def", "abbrev", "theorem",
    "lemma", "instance", "structure", "class", "inductive", "opaque", "axiom", "example",
    "alias", "macro", "syntax", "elab", "notation", "scoped", "local", "private", "protected",
    "noncomputable", "partial", "unsafe", "mutual", "mono", "rel", "finiteness", "ac_rfl",
    "noncomm_ring", "module", "cc",
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

G_SRC = ""
G_CAND_SHORTS = set()
G_CAND_FULLS = set()
G_CHECK_OPEN_MODS = set()


def extract_bracket_spans(text):
    n = len(text)
    for m in TAC_BRACKET_RE.finditer(text):
        i = m.end()
        depth = 1
        j = i
        while j < n and depth > 0:
            ch = text[j]
            if ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
            j += 1
        yield text[i : max(i, j - 1)]


def scan_file(mod):
    fp = os.path.join(G_SRC, mod.replace(".", "/") + ".lean")
    try:
        txt = open(fp, encoding="utf-8", errors="replace").read()
    except OSError:
        return mod, set(), set(), set(), set(), set(), [], [], None, None, None

    raw_lines = txt.split("\n")
    clean_lines = []
    open_privs = []
    open_clause_refs = []
    named_shorts = set()
    check_open = mod in G_CHECK_OPEN_MODS
    opened_ns = set() if check_open else None
    used_shorts = set() if check_open else None
    own_decl_shorts = set() if check_open else None

    for ln in raw_lines:
        idx = ln.find("--")
        code = ln[:idx] if idx >= 0 else ln
        clean_lines.append(code)
        m_op = OPEN_PRIV.match(code)
        if m_op:
            for t in TOK.findall(m_op.group(1)):
                open_privs.append(t)
        m_oh = OPEN_HIDING.match(code)
        if m_oh:
            nss = [x.strip() for x in m_oh.group(1).split() if x.strip()]
            for t in TOK.findall(m_oh.group(2)):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_CAND_SHORTS:
                    for ns in nss:
                        open_clause_refs.append((ns, sh))
                    open_clause_refs.append(("", sh))
        m_opar = OPEN_PAREN.match(code)
        if m_opar:
            ns = m_opar.group(1)
            for t in TOK.findall(m_opar.group(2)):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_CAND_SHORTS:
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
        if check_open:
            for t in TOK.findall(code):
                t0 = t[7:] if t.startswith("_root_.") else t
                used_shorts.add(t0.rsplit(".", 1)[-1])
        for mo in NAMED_RE.finditer(code):
            for t in app_tokens(code, mo.start()):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_CAND_SHORTS:
                    named_shorts.add(sh)

    clean = "\n".join(clean_lines)

    rw_shorts = set()
    rw_fulls = set()
    for span in extract_bracket_spans(clean):
        for t in TOK.findall(span):
            t0 = t[7:] if t.startswith("_root_.") else t
            sh = t0.rsplit(".", 1)[-1]
            if sh in G_CAND_SHORTS:
                rw_shorts.add(sh)
            if t0 in G_CAND_FULLS:
                rw_fulls.add(t0)
    for m in TAC_UNFOLD_RE.finditer(clean):
        for t in TOK.findall(m.group(1)):
            t0 = t[7:] if t.startswith("_root_.") else t
            sh = t0.rsplit(".", 1)[-1]
            if sh in G_CAND_SHORTS:
                rw_shorts.add(sh)
            if t0 in G_CAND_FULLS:
                rw_fulls.add(t0)

    tok_fulls = set()
    dot_shorts = set()
    for m in re.finditer(r"(?:[\)\]\⟩]|(?<![A-Za-z0-9_'.])[a-z_α-ω][A-Za-z0-9_'α-ω₀-₉]*)\.([A-Za-z_α-ω][" + _LL + r"]*)", clean):
        sh = m.group(1)
        if sh in G_CAND_SHORTS:
            dot_shorts.add(sh)
    for t in TOK.findall(clean):
        t0 = t[7:] if t.startswith("_root_.") else t
        if t0 in G_CAND_FULLS:
            tok_fulls.add(t0)

    return mod, rw_shorts, rw_fulls, tok_fulls, dot_shorts, named_shorts, open_privs, open_clause_refs, opened_ns, used_shorts, own_decl_shorts


def strip_priv(name):
    if name.startswith("_private."):
        i = name.find(".0.")
        if i > 0:
            return name[i + 3 :]
    return name


def main():
    global G_SRC, G_CAND_SHORTS, G_CAND_FULLS, G_CHECK_OPEN_MODS
    ap = argparse.ArgumentParser()
    ap.add_argument("plan", help="defplan.tsv from defdedup_plan.py")
    ap.add_argument("edits", help="edits TSV from defdedup_edits.py")
    ap.add_argument("src", help="Base-A src dir")
    ap.add_argument("scan_dir", help="P03 dupscan out dir")
    ap.add_argument("imports_json", help="rh-imports.json")
    ap.add_argument("out", help="guarded output edits TSV")
    ap.add_argument("--protect-from", default=None)
    ap.add_argument("--jobs", type=int, default=32)
    a = ap.parse_args()

    prot = set()
    if a.protect_from and os.path.isfile(a.protect_from):
        cj = json.load(open(a.protect_from))
        prot = set(cj.get("theorem_names", [])) | set(cj.get("definition_names", []))

    plan_by_end = {}
    with open(a.plan, encoding="utf-8") as f:
        hdr = f.readline().rstrip("\n").split("\t")
        ix = {k: i for i, k in enumerate(hdr)}
        for ln in f:
            p = ln.rstrip("\n").split("\t")
            if p[ix["action"]] in ("VISIBLE", "IMPORT_CP"):
                row = {k: p[i] for k, i in ix.items()}
                plan_by_end[(row["module"], int(row["end"]))] = row

    edits = [ln.rstrip("\n").split("\t", 5) for ln in open(a.edits, encoding="utf-8") if ln.strip()]

    cand_fulls = set()
    cand_shorts = set()
    cand_rows = {}  # (mod, end) -> (act, row)
    for e in edits:
        mod, s, en, act = e[0], int(e[1]), int(e[2]), e[3]
        if act in ("replace", "delete"):
            row = plan_by_end.get((mod, en))
            if row is None:
                continue
            un = strip_priv(row["name"])
            sh = un.rsplit(".", 1)[-1]
            cand_fulls.add(un)
            cand_fulls.add(row["name"])
            cand_shorts.add(sh)
            cand_rows[(mod, en)] = (act, row)

    imp_raw = json.load(open(a.imports_json))
    imp = {m: [d for d in v.get("imports", ()) if d in imp_raw] for m, v in imp_raw.items()}
    rdeps = collections.defaultdict(set)
    for m, ds in imp.items():
        for d in ds:
            rdeps[d].add(m)

    import_adding_mods = set()
    added_edges = []
    for (mod, en), (act, row) in cand_rows.items():
        if row["action"].startswith("IMPORT") and row["target_mod"] and row["target_mod"] != mod:
            import_adding_mods.add(mod)
            added_edges.append((mod, row["target_mod"]))
    check_open_mods = set(import_adding_mods)
    for m in import_adding_mods:
        check_open_mods |= rdeps.get(m, set())

    # 1. Full 175k source scan (RW_UNFOLD, external refs, open clauses, named args, opened_ns)
    G_SRC = a.src
    G_CAND_SHORTS = cand_shorts
    G_CAND_FULLS = cand_fulls
    G_CHECK_OPEN_MODS = check_open_mods
    all_mods = []
    for root, _, files in os.walk(a.src):
        for fn in files:
            if fn.endswith(".lean"):
                all_mods.append(os.path.relpath(os.path.join(root, fn), a.src)[:-5].replace("/", "."))

    rw_shorts_all = collections.defaultdict(set)
    rw_fulls_all = collections.defaultdict(set)
    src_full_users = collections.defaultdict(set)
    dot_in_mod = collections.defaultdict(set)
    named_in_mod = collections.defaultdict(set)
    open_priv_mods = collections.defaultdict(set)
    open_clause_mods = collections.defaultdict(set)  # (ns, sh) -> set of mods
    mod_opened_ns = {}
    mod_used_shorts = {}
    mod_own_decl_shorts = {}

    with Pool(a.jobs) as pool:
        for mod, rws, rwf, tf, dsh, nsh, oprivs, ocrefs, ons, ush, ods in pool.imap_unordered(scan_file, all_mods, chunksize=64):
            for s in rws:
                rw_shorts_all[s].add(mod)
            for f in rwf:
                rw_fulls_all[f].add(mod)
            for f in tf:
                src_full_users[f].add(mod)
            if dsh:
                dot_in_mod[mod] = dsh
            if nsh:
                named_in_mod[mod] = nsh
            for op in oprivs:
                open_priv_mods[op].add(mod)
            for ns, sh in ocrefs:
                open_clause_mods[(ns, sh)].add(mod)
            if ons is not None:
                mod_opened_ns[mod] = ons
                mod_used_shorts[mod] = ush
                mod_own_decl_shorts[mod] = ods

    all_opened_ns = set()
    for ons in mod_opened_ns.values():
        all_opened_ns |= ons

    # 2. Single-pass dupscan load: binfo, owner, ext_kernel_users, dup_cnames, mod_pub_by_ns
    cand_knames = {row["name"] for _, row in cand_rows.values()}
    cand_need_binfo = cand_knames | {row["target"] for _, row in cand_rows.values()}
    binfo = {}
    owner = {}
    cname_first_mod = {}
    dup_cname_mods = collections.defaultdict(set)
    mod_pub_by_ns = collections.defaultdict(lambda: collections.defaultdict(set))
    ext_kernel_users = collections.defaultdict(set)

    # Pass 1: owner, binfo, dup_cnames, mod_pub_by_ns
    scan_files = sorted(glob.glob(os.path.join(a.scan_dir, "c*.tsv")))
    for fp in scan_files:
        for ln in open(fp, encoding="utf-8", errors="replace"):
            if not ln.startswith("K\t"):
                continue
            p = ln.rstrip("\n").split("\t")
            if len(p) < 4:
                continue
            cm, cname = p[1], p[3]
            owner[cname] = cm
            if cname in cand_need_binfo and len(p) >= 13:
                binfo[cname] = p[12]
            if not (cname.startswith("_private.") or "._proof_" in cname or "._simp_" in cname or ".match_" in cname or "._sparseCasesOn_" in cname or AUTO_RE.search(cname)):
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

    # Pass 2: external kernel users
    for fp in scan_files:
        for ln in open(fp, encoding="utf-8", errors="replace"):
            if not ln.startswith("K\t"):
                continue
            p = ln.rstrip("\n").split("\t")
            if len(p) > 10 and p[10]:
                um = p[1]
                for u in p[10].split(" "):
                    if u in cand_knames and owner.get(u) != um:
                        ext_kernel_users[u].add(um)

    # 3. Transitive ALREADY_DECLARED_IMPORT & AMBIGUOUS_IMPORT over added_edges
    mod_dup_cnames = collections.defaultdict(set)
    for cname, ms in dup_cname_mods.items():
        for cm in ms:
            mod_dup_cnames[cm].add(cname)

    rel_mods = sorted(set(mod_pub_by_ns.keys()) | set(mod_dup_cnames.keys()))
    rel_idx = {m: i for i, m in enumerate(rel_mods)}
    dup_rel_mask = 0
    for m in mod_dup_cnames:
        dup_rel_mask |= 1 << rel_idx[m]

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

    already_pairs = set()
    ambig_pairs = set()
    seen_edges = set()
    for m0, tmod in added_edges:
        if (m0, tmod) in seen_edges:
            continue
        seen_edges.add((m0, tmod))
        tm_mk = tmask.get(tmod, 0)
        if not tm_mk:
            continue
        for ma in [m0] + list(rdeps.get(m0, ())):
            ma_mk = tmask.get(ma, 0)
            new_mk = tm_mk & ~ma_mk
            if not new_mk:
                continue
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

    # Transitive importer cone helper
    cone_cache = {}
    def importers_trans(m0):
        if m0 in cone_cache:
            return cone_cache[m0]
        seen = {m0}
        st = [m0]
        while st:
            u = st.pop()
            for v in rdeps.get(u, ()):
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        cone_cache[m0] = seen
        return seen

    # Evaluate every candidate decl
    file_cache = {}
    def get_lines(m):
        if m not in file_cache:
            fp = os.path.join(a.src, m.replace(".", "/") + ".lean")
            file_cache[m] = open(fp, encoding="utf-8", errors="replace").read().split("\n") if os.path.exists(fp) else []
        return file_cache[m]

    drop_reasons = {}
    drop_stats = collections.Counter()
    kept_decls = set()
    for (mod, en), (act, row) in sorted(cand_rows.items()):
        kn = row["name"]
        tgt = row["target"]
        tmod = row["target_mod"]
        un = strip_priv(kn)
        m_ns = un.rsplit(".", 1)[0] if "." in un else ""
        sh = un.rsplit(".", 1)[-1]
        if kn in prot or un in prot:
            drop_reasons[(mod, en)] = "PROTECTED"; drop_stats["PROTECTED"] += 1; continue
        if tgt.startswith("_private."):
            drop_reasons[(mod, en)] = "PRIVATE_TARGET"; drop_stats["PRIVATE_TARGET"] += 1; continue
        bn, bt = binfo.get(kn), binfo.get(tgt)
        if bn is None or bt is None or bn != bt:
            drop_reasons[(mod, en)] = f"BINFO_MISMATCH({bn}!={bt})"; drop_stats["BINFO_MISMATCH"] += 1; continue
        if row["action"].startswith("IMPORT") and tmod and tmod != mod:
            if (mod, tmod) in already_pairs:
                drop_reasons[(mod, en)] = "ALREADY_DECLARED_IMPORT"; drop_stats["ALREADY_DECLARED_IMPORT"] += 1; continue
            if (mod, tmod) in ambig_pairs:
                drop_reasons[(mod, en)] = "AMBIGUOUS_IMPORT"; drop_stats["AMBIGUOUS_IMPORT"] += 1; continue
        cone = importers_trans(mod)
        if act == "replace":
            rw_mods = (rw_shorts_all.get(sh, set()) | rw_fulls_all.get(un, set())) & cone
            if rw_mods:
                drop_reasons[(mod, en)] = f"RW_UNFOLD({len(rw_mods)}_mods)"; drop_stats["RW_UNFOLD"] += 1; continue
            if any(sh in named_in_mod.get(cm, set()) for cm in cone):
                drop_reasons[(mod, en)] = "NAMED_ARG"; drop_stats["NAMED_ARG"] += 1; continue
        else:
            # delete (local redirect inside mod)
            ext_k = ext_kernel_users.get(kn, set())
            ext_s = (src_full_users.get(un, set()) - {mod}) & cone
            if ext_k or ext_s:
                drop_reasons[(mod, en)] = f"EXT_USED(k={len(ext_k)},s={len(ext_s)})"; drop_stats["EXT_USED"] += 1; continue
            if open_priv_mods.get(un, set()) & cone:
                drop_reasons[(mod, en)] = "OPEN_PRIVATE"; drop_stats["OPEN_PRIVATE"] += 1; continue
            oc_hit = False
            for (ons, osh), omods in open_clause_mods.items():
                if osh == sh and (omods & cone):
                    if ons == "" or m_ns == ons or m_ns.endswith("." + ons):
                        oc_hit = True
                        break
            if oc_hit:
                drop_reasons[(mod, en)] = "OPEN_CLAUSE_REF"; drop_stats["OPEN_CLAUSE_REF"] += 1; continue
            if len(sh) < 3:
                drop_reasons[(mod, en)] = "SHORT_NAME_LT3"; drop_stats["SHORT_NAME_LT3"] += 1; continue
            if sh in dot_in_mod.get(mod, set()):
                drop_reasons[(mod, en)] = "DOT_NOTATION"; drop_stats["DOT_NOTATION"] += 1; continue
            if sh in named_in_mod.get(mod, set()):
                drop_reasons[(mod, en)] = "NAMED_ARG"; drop_stats["NAMED_ARG"] += 1; continue
            # Inspect rest of mod body outside [start..end] for local subst hazards
            lines = get_lines(mod)
            s0 = int(row["start"])
            other_lines = lines[: max(0, s0 - 1)] + lines[en:]
            other_clean = "\n".join(ln.split("--", 1)[0] for ln in other_lines)
            # 1) Another declaration in mod has head name == sh (or starts with sh.)
            decl_coll = False
            for ln in other_lines:
                m_dh = DECL_HEAD_RE.match(ln)
                if m_dh:
                    hn = m_dh.group(1)
                    if hn == sh or hn.startswith(sh + ".") or hn.endswith("." + sh):
                        decl_coll = True
                        break
            if decl_coll:
                drop_reasons[(mod, en)] = "SHORT_DECL_COLLISION"; drop_stats["SHORT_DECL_COLLISION"] += 1; continue
            # 2) sh. prefix (e.g. NormOne.one)
            if re.search(r"(?<![" + _LL + r"])" + re.escape(sh) + r"\.", other_clean):
                drop_reasons[(mod, en)] = "SHORT_DOT_PREFIX"; drop_stats["SHORT_DOT_PREFIX"] += 1; continue
            # 3) Tactic / Lean keyword short name (e.g. `ext j`)
            if sh in LEAN_TACTICS_KW:
                drop_reasons[(mod, en)] = "TACTIC_KW"; drop_stats["TACTIC_KW"] += 1; continue
            # 4) apply_edits.py boundary mismatch (e.g. `‖eps`, `‖extId`, `↑sh`)
            all_occ = len(re.findall(r"(?<![" + _LL + r"\.])" + re.escape(sh) + APPLY_LA, other_clean))
            sub_occ = len(re.findall(APPLY_LB + r"(_root_\.)?" + re.escape(sh) + APPLY_LA, other_clean))
            if all_occ > sub_occ:
                drop_reasons[(mod, en)] = "APPLY_BOUNDARY"; drop_stats["APPLY_BOUNDARY"] += 1; continue
            # 5) Local instance involving sh (Type-valued defs with local typeclass instances)
            if re.search(r"^\s*(?:local\s+|scoped\s+|private\s+)*instance\b[^\n]*\b" + re.escape(sh) + r"\b", other_clean, re.M):
                drop_reasons[(mod, en)] = "LOCAL_INSTANCE"; drop_stats["LOCAL_INSTANCE"] += 1; continue
        kept_decls.add((mod, en))

    # Build kept subst keys and needed imports per module
    kept_subst_old = collections.defaultdict(set)
    needed_imports = collections.defaultdict(set)
    for (mod, en) in kept_decls:
        act, row = cand_rows[(mod, en)]
        if row["action"].startswith("IMPORT") and row["target_mod"] and row["target_mod"] != mod:
            needed_imports[mod].add(row["target_mod"])
        if act == "delete":
            un = strip_priv(row["name"])
            sh = un.rsplit(".", 1)[-1]
            kept_subst_old[mod].add(un)
            kept_subst_old[mod].add(sh)

    # Filter edits TSV
    out_edits = []
    kept_mods = set()
    edit_stats = collections.Counter()
    for e in edits:
        mod, s, en, act = e[0], int(e[1]), int(e[2]), e[3]
        if act in ("replace", "delete"):
            if (mod, en) not in kept_decls:
                edit_stats["dropped_" + act] += 1
                continue
            out_edits.append(e)
            kept_mods.add(mod)
            edit_stats["kept_" + act] += 1
        elif act == "subst":
            old = e[5].split(" ", 1)[0]
            if old not in kept_subst_old.get(mod, set()):
                edit_stats["dropped_subst"] += 1
                continue
            out_edits.append(e)
            edit_stats["kept_subst"] += 1
        elif act == "insert_before":
            want = needed_imports.get(mod, set())
            keep_imps = [ln for ln in e[5].split("\\n") if ln.startswith("import ") and ln.split()[1] in want]
            if not keep_imps:
                edit_stats["dropped_insert_before"] += 1
                continue
            out_edits.append(e[:5] + ["\\n".join(keep_imps)])
            edit_stats["kept_insert_before"] += 1

    with open(a.out, "w", encoding="utf-8") as fo:
        for e in out_edits:
            fo.write("\t".join(e) + "\n")

    with open(a.out + ".dropped.tsv", "w", encoding="utf-8") as fd:
        for (mod, en), why in sorted(drop_reasons.items()):
            act, row = cand_rows[(mod, en)]
            fd.write(f"{mod}\t{en}\t{act}\t{row['kw']}\t{row['name']}\t{why}\n")

    direct_importers = set()
    for m in kept_mods:
        direct_importers |= rdeps.get(m, set())
    cone_mods = sorted(kept_mods | direct_importers)
    with open(a.out + ".cone.txt", "w", encoding="utf-8") as fc:
        for m in cone_mods:
            fc.write(m + "\n")

    print(
        json.dumps(
            {
                "candidates": len(cand_rows),
                "kept_decls": len(kept_decls),
                "dropped_decls": len(drop_reasons),
                "drop_reasons": dict(drop_stats),
                "edit_stats": dict(edit_stats),
                "already_pairs": len(already_pairs),
                "ambig_pairs": len(ambig_pairs),
                "kept_modules": len(kept_mods),
                "direct_importers": len(direct_importers - kept_mods),
                "total_l1_cone_modules": len(cone_mods),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()

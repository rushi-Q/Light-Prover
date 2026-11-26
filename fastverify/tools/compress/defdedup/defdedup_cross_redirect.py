#!/usr/bin/python3 -I
"""defdedup_cross_redirect.py DEFPLAN_TSV SRC SCAN_DIR IMPORTS_JSON COSTS_GZ OUT_TSV [--protect-from CFG] [--jobs 32]

Hardened Stage-3 cross-module `redirect` for externally-referenced duplicate `def`s (DEFDEDUP.hybrid):
Enforces ALL static guards:
  - PROTECTED, PRIVATE_TARGET, BINFO_MISMATCH (exact dupscan col 12)
  - EXT_NON_EXACT, DOT_NOTATION, NAMED_ARG, OPEN_PRIVATE, OPEN_CLAUSE_REF (`open ... hiding/renaming/(...)`)
  - APPLY_BOUNDARY (every occurrence matched by `apply_edits.py` L111 lookbehind/lookahead)
  - SHORT_DECL_COLLISION, SHORT_DOT_PREFIX, TACTIC_POS inside declaring module
  - CP_GUARD (`finish(tmod) <= start(um)`) + acyclicity + TRANSITIVE ALREADY_DECLARED_IMPORT & AMBIGUOUS_IMPORT
  - Emits team-format edits AND `OUT_TSV.cone.txt` (all touched modules + all direct importers of declaring mods).
"""
import argparse
import collections
import glob
import gzip
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
OPEN_HIDING = re.compile(r"^\s*open\s+(?!private\b)(?:scoped\s+)?([^\n]+?)\s+(?:hiding|renaming)\s+([^\n]+)")
OPEN_PAREN = re.compile(r"^\s*open\s+(?!private\b)(?:scoped\s+)?([A-Za-z_α-ω][" + _LL + r".]*)\s*\(([^)]+)\)")
OPEN_NS = re.compile(r"^\s*open\s+(?!private\b)(?:scoped\s+)?(.+)")
NS_DECL = re.compile(r"^\s*namespace\s+([A-Za-z_α-ω][" + _LL + r".]*)")
DECL_HEAD_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|opaque|axiom|instance)\s+([^\s:({\[⦃]+)"
)
MOD_KW = re.compile(r"^\s*(?:set_option|attribute|variable|open|omit|include)\b")
STOP_KW = re.compile(r"^\s*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|namespace|section|end|import|alias)\b")
APPLY_LB_CH = set(" \t\r\n()[]{}⟨⟩,;@←·$`|:=<>+*/\\^&!~-")
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


def strip_priv(name):
    if name.startswith("_private."):
        i = name.find(".0.")
        if i > 0:
            return name[i + 3 :]
    return name


def find_modifier_start(lines, s):
    i = s - 1
    while i > 0:
        j = i - 1
        while j >= 0 and lines[j].strip() == "":
            j -= 1
        if j < 0:
            break
        if re.search(r"(?:^|\s)in\s*(?:--.*)?$", lines[j]):
            k = j
            while k > 0 and not MOD_KW.match(lines[k]):
                if lines[k].strip() == "" or STOP_KW.match(lines[k]):
                    k = j + 1
                    break
                k -= 1
            if k <= j and MOD_KW.match(lines[k]):
                i = k
                continue
        break
    return i + 1


def first_non_import_line(lines):
    last_imp = 0
    for i, l in enumerate(lines, 1):
        s = l.strip()
        if s.startswith("import "):
            last_imp = i
        elif s == "" or s.startswith("--"):
            continue
        else:
            break
    return last_imp + 1


G_SRC = ""
G_SHORTS = set()


def scan_mod(mod):
    fp = os.path.join(G_SRC, mod.replace(".", "/") + ".lean")
    try:
        lines = open(fp, encoding="utf-8", errors="replace").read().split("\n")
    except OSError:
        return mod, [], [], [], set(), set()
    hits = []
    oprivs = []
    ocrefs = []
    dots = set()
    named_sh = set()
    for k, line in enumerate(lines, 1):
        s = line.lstrip()
        if s.startswith("--"):
            continue
        code = line.split("--", 1)[0]
        m_op = OPEN_PRIV.match(code)
        if m_op:
            for t in TOK.findall(m_op.group(1)):
                oprivs.append(t)
        m_oh = OPEN_HIDING.match(code)
        if m_oh:
            nss = [x.strip() for x in m_oh.group(1).split() if x.strip()]
            for t in TOK.findall(m_oh.group(2)):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_SHORTS:
                    for ns in nss:
                        ocrefs.append((ns, sh))
                    ocrefs.append(("", sh))
        m_opar = OPEN_PAREN.match(code)
        if m_opar:
            ns = m_opar.group(1)
            for t in TOK.findall(m_opar.group(2)):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_SHORTS:
                    ocrefs.append((ns, sh))
        for mo in NAMED.finditer(code):
            for t in app_tokens(code, mo.start()):
                sh = t.rsplit(".", 1)[-1]
                if sh in G_SHORTS:
                    named_sh.add(sh)
        for mo in TOK.finditer(code):
            t = mo.group(0)
            t0 = t[7:] if t.startswith("_root_.") else t
            sh = t0.rsplit(".", 1)[-1]
            if sh in G_SHORTS:
                st = mo.start()
                lb_ok = (st == 0) or (code[st - 1] in APPLY_LB_CH)
                hits.append((k, t0, lb_ok))
        for m in re.finditer(r"(?:[\)\]\⟩]|(?<![A-Za-z0-9_'.])[a-z_α-ω][A-Za-z0-9_'α-ω₀-₉]*)\.([A-Za-z_α-ω][" + _LL + r"]*)", code):
            sh = m.group(1)
            if sh in G_SHORTS:
                dots.add(sh)
    return mod, hits, oprivs, ocrefs, dots, named_sh


def main():
    global G_SRC, G_SHORTS
    ap = argparse.ArgumentParser()
    ap.add_argument("plan")
    ap.add_argument("src")
    ap.add_argument("scan_dir")
    ap.add_argument("imports_json")
    ap.add_argument("costs_gz")
    ap.add_argument("out")
    ap.add_argument("--protect-from", required=True)
    ap.add_argument("--owner", default="D13-defdedup-xmod")
    ap.add_argument("--jobs", type=int, default=32)
    a = ap.parse_args()

    cj = json.load(open(a.protect_from))
    prot = set(cj.get("theorem_names", [])) | set(cj.get("definition_names", []))

    imp_raw = json.load(open(a.imports_json))
    imp = {m: [d for d in v.get("imports", []) if d in imp_raw] for m, v in imp_raw.items()}
    rdeps = collections.defaultdict(set)
    for m, ds in imp.items():
        for d in ds:
            rdeps[d].add(m)
    order = {}
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
                order[u] = len(topo)
                topo.append(u)
            else:
                state[nxt] = 1
                st.append((nxt, iter(imp[nxt])))

    costs = json.load(gzip.open(a.costs_gz))
    cp_start = {}
    cp_finish = {}
    for m in topo:
        st_t = max((cp_finish.get(d, 0.0) for d in imp[m]), default=0.0)
        cp_start[m] = st_t
        cp_finish[m] = st_t + costs.get(m, 1.0)

    reach_cache = {}
    def imports_trans(mi, mr):
        if mi == mr:
            return True
        k = (mi, mr)
        if k in reach_cache:
            return reach_cache[k]
        lo = order.get(mr, -1)
        if lo < 0 or order.get(mi, -1) < lo:
            reach_cache[k] = False
            return False
        seen = {mi}; st = [mi]; found = False
        while st and not found:
            x = st.pop()
            for c in imp.get(x, ()):
                if c == mr:
                    found = True; break
                if c not in seen and order.get(c, -1) >= lo:
                    seen.add(c); st.append(c)
        reach_cache[k] = found
        return found

    cone_cache = {}
    def importers_trans(m0):
        if m0 in cone_cache:
            return cone_cache[m0]
        seen = {m0}; st = [m0]
        while st:
            u = st.pop()
            for v in rdeps.get(u, ()):
                if v not in seen:
                    seen.add(v); st.append(v)
        cone_cache[m0] = seen
        return seen

    cands = []
    with open(a.plan, encoding="utf-8") as f:
        hdr = f.readline().rstrip("\n").split("\t")
        ix = {k: i for i, k in enumerate(hdr)}
        for ln in f:
            p = ln.rstrip("\n").split("\t")
            if p[ix["action"]] not in ("VISIBLE", "IMPORT_CP"):
                continue
            if p[ix["kw"]] != "def":
                continue
            row = {k: p[i] for k, i in ix.items()}
            if row["name"] in prot or strip_priv(row["name"]) in prot:
                continue
            if row["is_priv"] == "1" or row["target"].startswith("_private."):
                continue
            un = strip_priv(row["name"])
            if "." not in un or len(un.rsplit(".", 1)[-1]) < 3:
                continue
            cands.append(row)

    cand_names = {r["name"] for r in cands}
    need_binfo = cand_names | {r["target"] for r in cands}
    binfo = {}
    owner = {}
    cname_first_mod = {}
    dup_cname_mods = collections.defaultdict(set)
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
            if cname in need_binfo and len(p) >= 13:
                binfo[cname] = p[12]
            if not (cname.startswith("_private.") or "._proof_" in cname or "._simp_" in cname or ".match_" in cname or "._sparseCasesOn_" in cname or AUTO_RE.search(cname)):
                prev = cname_first_mod.get(cname)
                if prev is None:
                    cname_first_mod[cname] = cm
                elif prev != cm:
                    dup_cname_mods[cname].add(prev)
                    dup_cname_mods[cname].add(cm)
    del cname_first_mod

    ext_kusers = collections.defaultdict(set)
    for fp in scan_files:
        for ln in open(fp, encoding="utf-8", errors="replace"):
            if not ln.startswith("K\t"):
                continue
            p = ln.rstrip("\n").split("\t")
            if len(p) > 10 and p[10]:
                um = p[1]
                for u in p[10].split(" "):
                    if u in cand_names and owner.get(u) != um:
                        ext_kusers[u].add(um)

    # Filter to ext_cands with exact binfo match
    ext_cands = [
        r for r in cands
        if ext_kusers.get(r["name"])
        and binfo.get(r["name"]) is not None
        and binfo.get(r["name"]) == binfo.get(r["target"])
    ]
    by_short = collections.defaultdict(list)
    by_un = collections.defaultdict(list)
    for r in ext_cands:
        un = strip_priv(r["name"])
        by_short[un.rsplit(".", 1)[-1]].append(r)
        by_un[un].append(r)

    G_SRC = a.src
    G_SHORTS = set(by_short)
    all_mods = []
    for root, _, files in os.walk(a.src):
        for fn in files:
            if fn.endswith(".lean"):
                all_mods.append(os.path.relpath(os.path.join(root, fn), a.src)[:-5].replace("/", "."))

    exact_users = collections.defaultdict(set)
    unsafe_reasons = collections.defaultdict(set)

    with Pool(a.jobs) as pool:
        for mod, hits, oprivs, ocrefs, dots, named_sh in pool.imap_unordered(scan_mod, all_mods, chunksize=64):
            for op in oprivs:
                for r in by_un.get(op, ()):
                    unsafe_reasons[r["name"]].add("OPEN_PRIVATE")
            for ns, sh in ocrefs:
                for r in by_short[sh]:
                    if mod in importers_trans(r["module"]):
                        un = strip_priv(r["name"])
                        m_ns = un.rsplit(".", 1)[0] if "." in un else ""
                        if ns == "" or m_ns == ns or m_ns.endswith("." + ns):
                            unsafe_reasons[r["name"]].add("OPEN_CLAUSE_REF")
            for sh in dots:
                for r in by_short[sh]:
                    if mod in importers_trans(r["module"]):
                        unsafe_reasons[r["name"]].add("DOT_NOTATION")
            for sh in named_sh:
                for r in by_short[sh]:
                    if mod in importers_trans(r["module"]):
                        unsafe_reasons[r["name"]].add("NAMED_ARG")
            for k, t0, lb_ok in hits:
                sh = t0.rsplit(".", 1)[-1]
                for r in by_short[sh]:
                    rmod = r["module"]
                    s, e = int(r["start"]), int(r["end"])
                    if mod == rmod and s <= k <= e:
                        continue
                    un = strip_priv(r["name"])
                    if mod == rmod:
                        if t0 != un and t0 != sh:
                            unsafe_reasons[r["name"]].add("PARTIAL_OWN")
                        elif not lb_ok:
                            unsafe_reasons[r["name"]].add("APPLY_BOUNDARY")
                    elif mod in importers_trans(rmod):
                        if t0 == un:
                            if not lb_ok:
                                unsafe_reasons[r["name"]].add("APPLY_BOUNDARY")
                            exact_users[r["name"]].add(mod)
                        else:
                            unsafe_reasons[r["name"]].add("EXT_NON_EXACT")

    # Precompute ALREADY_DECLARED_IMPORT bitmask
    mod_dup_cnames = collections.defaultdict(set)
    for cname, ms in dup_cname_mods.items():
        for cm in ms:
            mod_dup_cnames[cm].add(cname)
    dup_mods = sorted(mod_dup_cnames.keys())
    dup_idx = {m: i for i, m in enumerate(dup_mods)}
    dmask = {}
    for m in topo:
        mk = (1 << dup_idx[m]) if m in dup_idx else 0
        for d in imp[m]:
            mk |= dmask.get(d, 0)
        dmask[m] = mk

    def has_already_declared(m0, tmod):
        tm_mk = dmask.get(tmod, 0)
        if not tm_mk:
            return False
        for ma in [m0] + list(rdeps.get(m0, ())):
            ma_mk = dmask.get(ma, 0)
            new_mk = tm_mk & ~ma_mk
            if not new_mk or not ma_mk:
                continue
            cur = set()
            x = ma_mk
            while x:
                lsb = x & -x; cur |= mod_dup_cnames[dup_mods[lsb.bit_length() - 1]]; x ^= lsb
            y = new_mk
            while y:
                lsb = y & -y
                if mod_dup_cnames[dup_mods[lsb.bit_length() - 1]] & cur:
                    return True
                y ^= lsb
        return False

    stats = collections.Counter()
    kept = []
    for r in ext_cands:
        kn = r["name"]
        rmod = r["module"]
        tmod = r["target_mod"]
        un = strip_priv(kn)
        sh = un.rsplit(".", 1)[-1]
        if unsafe_reasons.get(kn):
            stats["drop_" + sorted(unsafe_reasons[kn])[0]] += 1
            continue
        kusers = ext_kusers[kn]
        susers = exact_users[kn]
        if not kusers.issubset(susers):
            stats["drop_kuser_missing_exact_text"] += 1
            continue
        all_users = susers | {rmod}
        cp_ok = True
        dup_ok = True
        for um in all_users:
            if not imports_trans(um, tmod):
                if order.get(tmod, 10**9) >= order.get(um, -1) or cp_finish.get(tmod, 0.0) > cp_start.get(um, 0.0) + 1e-9:
                    cp_ok = False; break
                if has_already_declared(um, tmod):
                    dup_ok = False; break
        if not cp_ok:
            stats["drop_user_cp_or_cycle"] += 1; continue
        if not dup_ok:
            stats["drop_already_declared_import"] += 1; continue
        fp = os.path.join(a.src, rmod.replace(".", "/") + ".lean")
        lines = open(fp, encoding="utf-8", errors="replace").read().split("\n")
        s, e = int(r["start"]), int(r["end"])
        decl_hdr = "\n".join(lines[s - 1 : e]).split(":=")[0]
        if "where" in decl_hdr or "match " in decl_hdr:
            stats["drop_pattern_def"] += 1; continue
        other_lines = lines[: max(0, s - 1)] + lines[e:]
        other_clean = "\n".join(ln.split("--", 1)[0] for ln in other_lines)
        if any(DECL_HEAD_RE.match(ln) and (DECL_HEAD_RE.match(ln).group(1) in (sh,) or DECL_HEAD_RE.match(ln).group(1).startswith(sh + ".")) for ln in other_lines):
            stats["drop_short_decl_collision"] += 1; continue
        if re.search(r"(?<![" + _LL + r"])" + re.escape(sh) + r"\.", other_clean):
            stats["drop_short_dot_prefix"] += 1; continue
        if sh in LEAN_TACTICS_KW:
            stats["drop_tactic_kw"] += 1; continue
        kept.append((r, susers, lines))
        stats["kept_xmod_defs"] += 1

    edits = []
    added_imps = collections.defaultdict(set)
    touched_mods = set()
    decl_mods = set()
    for r, susers, lines in kept:
        rmod = r["module"]
        tmod = r["target_mod"]
        tgt = r["target"]
        un = strip_priv(r["name"])
        sh = un.rsplit(".", 1)[-1]
        s, e = int(r["start"]), int(r["end"])
        s_mod = find_modifier_start(lines, s)
        edits.append((rmod, s_mod, e, "delete", a.owner, ""))
        edits.append((rmod, 0, 0, "subst", a.owner, f"{un} _root_.{tgt}"))
        edits.append((rmod, 0, 0, "subst", a.owner, f"{sh} _root_.{tgt}"))
        touched_mods.add(rmod)
        decl_mods.add(rmod)
        if not imports_trans(rmod, tmod):
            added_imps[rmod].add(tmod)
        for um in sorted(susers):
            edits.append((um, 0, 0, "subst", a.owner, f"{un} _root_.{tgt}"))
            touched_mods.add(um)
            if not imports_trans(um, tmod):
                added_imps[um].add(tmod)

    for mod, tmods in sorted(added_imps.items()):
        fp = os.path.join(a.src, mod.replace(".", "/") + ".lean")
        lines = open(fp, encoding="utf-8", errors="replace").read().split("\n")
        existing = {l.split()[1] for l in lines if l.startswith("import ") and len(l.split()) >= 2}
        need = sorted(t for t in tmods if t != mod and t not in existing)
        if need:
            ins = first_non_import_line(lines)
            edits.append((mod, ins, ins - 1, "insert_before", a.owner, "\\n".join(f"import {t}" for t in need)))
            stats["imports_added"] += len(need)

    with open(a.out, "w", encoding="utf-8") as fo:
        for mod, s, e, act, own, txt in edits:
            fo.write(f"{mod}\t{s}\t{e}\t{act}\t{own}\t{txt}\n")

    cone = set(touched_mods)
    for m in touched_mods:
        cone |= rdeps.get(m, set())
    with open(a.out + ".cone.txt", "w", encoding="utf-8") as fm:
        for m in sorted(cone):
            fm.write(m + "\n")

    stats["ext_cands_scanned"] = len(ext_cands)
    stats["touched_mods"] = len(touched_mods)
    stats["cone_mods"] = len(cone)
    stats["total_edits"] = len(edits)
    print(json.dumps(dict(stats), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

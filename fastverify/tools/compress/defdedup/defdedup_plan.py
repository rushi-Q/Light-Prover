#!/usr/bin/env python3
"""defdedup_plan.py DECLS_TSV SRCMAP_TSV IMPORTS_JSON SRC OUT_DIR [options]

Plans source-level consolidation of duplicate hand-written definitions (`def` / `abbrev`) found by
`exphash` (nominal `rhh/decls.tsv` or semantic `rhc/decls.tsv`).

Unlike theorems (where proof irrelevance makes same-statement consolidation safe at the kernel level),
consolidating definitions is a G2 transformation because definitions unfold during elaboration
(`rw [D]`, `simp [D]`, `dsimp`, `unfold`, dot notation, reducibility/typeclass synthesis, and
statement-closure pinning in code formalizations).

Protected names (--protect-from comparator.json, mandatory; optional --protect-closure FILE;
plus Main/Statements modules) are NEVER scheduled for modification.
"""
import argparse, collections, gzip, json, os, re, sys

ATTR_RE = re.compile(r'@\[|^\s*attribute\s*\[', re.M)
NONCOMP_SEC_RE = re.compile(r'^\s*noncomputable\s+section\b', re.M)


def load_protected(cfg_path, closure_path, protect_mods):
    c = json.load(open(cfg_path))
    prot = set(c.get('theorem_names', [])) | set(c.get('definition_names', []))
    if closure_path:
        for l in open(closure_path):
            s = l.strip().split('\t')[0]
            if s:
                prot.add(s)
    return prot, set(x for x in protect_mods.split(',') if x)


def topo_order(imp):
    state = {}
    topo = []
    for m in imp:
        if m in state:
            continue
        st = [(m, iter(imp.get(m, ())))]
        state[m] = 1
        while st:
            u, it = st[-1]
            nxt = None
            for v in it:
                if v in imp and v not in state:
                    nxt = v
                    break
            if nxt is None:
                st.pop()
                state[u] = 2
                topo.append(u)
            else:
                state[nxt] = 1
                st.append((nxt, iter(imp.get(nxt, ()))))
    return {m: i for i, m in enumerate(topo)}, topo


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('decls', help='exphash decls.tsv (nominal or semantic --classes)')
    ap.add_argument('srcmap', help='exphash srcmap.tsv')
    ap.add_argument('imports', help='dedup imports.json')
    ap.add_argument('src', help='project source directory (e.g. alpoge-rh/lean/src)')
    ap.add_argument('out', help='output directory')
    ap.add_argument('--protect-from', required=True, help='comparator.json (REQUIRED)')
    ap.add_argument('--protect-closure', default=None, help='optional file of statement-closure constant names')
    ap.add_argument('--protect-mods', default='Main,Statements', help='comma-separated protected modules')
    ap.add_argument('--semantic', action='store_true', help='group by exphash semantic `class` column instead of nominal hashes')
    ap.add_argument('--cp-guard', default=None, help='rh-build-costs.json.gz to guard added imports against CP increase')
    a = ap.parse_args()

    os.makedirs(a.out, exist_ok=True)
    prot_names, prot_mods = load_protected(a.protect_from, a.protect_closure, a.protect_mods)

    # 1. Load source outline (def/abbrev only)
    src = {}
    for l in open(a.srcmap, encoding='utf-8'):
        p = l.rstrip('\n').split('\t')
        if len(p) < 6 or p[0] in ('name', '-'):
            continue
        if p[2] in ('def', 'abbrev'):
            src[p[0]] = (p[1], p[2], int(p[3]), int(p[4]), int(p[5]))

    # 2. Load import graph & topo order
    imp_raw = json.load(open(a.imports))
    imp = {m: v.get('imports', []) for m, v in imp_raw.items()}
    order, topo = topo_order(imp)

    # Optional critical-path start/finish times
    cp_start = {}; cp_finish = {}
    if a.cp_guard:
        costs = json.load(gzip.open(a.cp_guard))
        for m in topo:
            st = max((cp_finish.get(d, 0.0) for d in imp.get(m, []) if d in cp_finish), default=0.0)
            cp_start[m] = st
            cp_finish[m] = st + costs.get(m, 1.0)

    reach_cache = {}
    def imports_trans(mi, mr):
        if mi == mr:
            return False
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

    # 3. Group hand-written project defs/abbrevs from decls.tsv
    groups = collections.defaultdict(list)
    with open(a.decls, encoding='utf-8') as f:
        hdr = f.readline().rstrip('\n').split('\t')
        ix = {k: i for i, k in enumerate(hdr)}
        use_cls = a.semantic and ('class' in ix)
        for l in f:
            p = l.rstrip('\n').split('\t')
            if p[ix['kind']] != 'def':
                continue
            nm = p[ix['name']]
            if nm not in src:
                continue
            key = p[ix['class']] if use_cls else (p[ix['type_hk']], p[ix['lvl_h']], p[ix['value_hk']], p[ix['extra']])
            groups[key].append((nm, p[ix['type_hs']], p[ix['lvl_h']], p[ix['extra']], src[nm]))

    # 4. Plan in topological order
    stats = collections.Counter()
    rows = []
    file_cache = {}
    def get_lines(mod):
        if mod not in file_cache:
            if len(file_cache) > 4000:
                file_cache.clear()
            fp = os.path.join(a.src, mod.replace('.', '/') + '.lean')
            file_cache[mod] = open(fp, encoding='utf-8', errors='replace').read().split('\n') if os.path.exists(fp) else []
        return file_cache[mod]

    gi = 0
    for key, mems in groups.items():
        if len(mems) < 2:
            continue
        gi += 1
        stats['classes'] += 1
        stats['members'] += len(mems)
        # Sort members by topological order of (module, start line)
        mems.sort(key=lambda x: (order.get(x[4][0], 10**9), x[4][2]))
        kept = []  # list of kept entries in this class
        for nm, ths, lvh, extra, (mod, kw, s, e, nl) in mems:
            is_priv = nm.startswith('_private.')
            lines = get_lines(mod)
            decl_text = '\n'.join(lines[max(0, s - 1):e])
            has_attr = bool(ATTR_RE.search(decl_text.split(':=')[0]))
            is_prot = (nm in prot_names) or (mod in prot_mods)
            is_noncomp = ('noncomputable ' in decl_text.split(':=')[0]) or bool(NONCOMP_SEC_RE.search('\n'.join(lines[:max(0, s - 1)])))
            red_kind = 'abbrev' if 'abbrev' in extra else 'regular'

            # Find a kept representative
            vis_tgt = None
            imp_tgt = None
            imp_cp_ok = False
            if not is_prot and not has_attr:
                for knm, kths, klvh, kextra, (kmod, kkw, ks, ke, knl), kpriv in kept:
                    if kpriv and kmod != mod:
                        continue
                    if kths != ths or klvh != lvh:
                        continue
                    if kmod == mod and ke < s:
                        vis_tgt = (knm, kmod, kkw, kextra); break
                    if imports_trans(mod, kmod):
                        vis_tgt = (knm, kmod, kkw, kextra); break
                if vis_tgt is None:
                    for knm, kths, klvh, kextra, (kmod, kkw, ks, ke, knl), kpriv in kept:
                        if kpriv:
                            continue
                        if kths != ths or klvh != lvh:
                            continue
                        if order.get(kmod, 10**9) < order.get(mod, -1):
                            ok_cp = (not a.cp_guard) or (cp_finish.get(kmod, 0.0) <= cp_start.get(mod, 0.0))
                            if imp_tgt is None or (ok_cp and not imp_cp_ok):
                                imp_tgt = (knm, kmod, kkw, kextra)
                                imp_cp_ok = ok_cp
                                if ok_cp:
                                    break

            if is_prot:
                act = 'KEEP_PROT'; tgt = ''; tmod = ''; tkw = ''; stats['keep_protected'] += 1
                kept.append((nm, ths, lvh, extra, (mod, kw, s, e, nl), is_priv))
            elif has_attr:
                act = 'KEEP_ATTR'; tgt = ''; tmod = ''; tkw = ''; stats['keep_attr'] += 1
                kept.append((nm, ths, lvh, extra, (mod, kw, s, e, nl), is_priv))
            elif vis_tgt is not None:
                act = 'VISIBLE'; tgt, tmod, tkw, _ = vis_tgt
                stats['visible'] += 1; stats['visible_' + kw] += 1; stats['visible_lines'] += nl
            elif imp_tgt is not None:
                act = 'IMPORT_CP' if imp_cp_ok else 'IMPORT_NOCP'
                tgt, tmod, tkw, _ = imp_tgt
                stats[act.lower()] += 1; stats[act.lower() + '_' + kw] += 1; stats[act.lower() + '_lines'] += nl
            else:
                act = 'KEEP'; tgt = ''; tmod = ''; tkw = ''; stats['keep_canon'] += 1
                kept.append((nm, ths, lvh, extra, (mod, kw, s, e, nl), is_priv))

            rows.append((gi, act, nm, mod, kw, red_kind, s, e, nl, int(is_priv), int(is_noncomp), tgt, tmod, tkw))

    plan_tsv = os.path.join(a.out, 'defplan.tsv')
    with open(plan_tsv, 'w', encoding='utf-8') as f:
        f.write('group\taction\tname\tmodule\tkw\tred_kind\tstart\tend\tnlines\tis_priv\tis_noncomp\ttarget\ttarget_mod\ttarget_kw\n')
        for r in rows:
            f.write('\t'.join(map(str, r)) + '\n')
    summary = dict(stats)
    summary['semantic'] = bool(use_cls)
    json.dump(summary, open(os.path.join(a.out, 'defplan.json'), 'w'), indent=1, sort_keys=True)
    print(json.dumps(summary, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()

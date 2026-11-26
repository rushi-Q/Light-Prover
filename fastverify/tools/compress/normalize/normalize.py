#!/usr/bin/env python3
"""normalize.py — G1 source normalization of a Lean 4 project tree (with module-system support).
Supports both traditional Lean 4 files and Lean 4 `module` / `public import` projects (e.g. Cedar, Cslib, Mathlib).

Soundness of IMP-C1 on `module` / mixed projects (from Lean 4.33.1 `Lean/Environment.lean:2177-2229`):
Let `pub_clo(X)` be the transitive closure of `X` following only re-exported non-meta/non-all imports
(`public import` in `module` files; plain/public `import` in non-`module` files).
1. A re-exported import (`public import c` in a `module` file, or plain `import c` in a non-`module` file) at position k
   is an exact `importModulesCore` no-op in EVERY context iff `c` lies in `pub_clo(b)` for an earlier kept re-exported
   import `b` (j < k, non-meta, non-all).
2. A non-exported import (plain/private `import c` in a `module` file) at position k is an exact `importModulesCore`
   no-op in EVERY context iff `c` lies in `pub_clo(b)` for ANY earlier kept import `b` (j < k, non-meta, non-all).
On purely traditional projects (`is_module == False` everywhere), this reduces identically to the classic IMP-C1 + IMP-C2.
"""
import os, sys, re, json, argparse, collections


def parse_header_ext(lines):
    """-> (is_module, [(line_index, vis, mod_name)]) where vis in ('plain', 'public', 'private', 'special'),
    or None if header cannot be parsed safely for import reduction (prelude, inline block comment on import line,
    multi-module import line). Never aborts option/NCS normalization on other classes."""
    out = []; depth = 0; is_mod = False; seen_imp = False
    for i, l in enumerate(lines):
        j = 0; n = len(l); rest = []
        while j < n:
            if depth:
                if l.startswith('/-', j): depth += 1; j += 2
                elif l.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
                continue
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('--', j): break
            rest.append(l[j]); j += 1
        t = ''.join(rest).split()
        if not t: continue
        if t == ['module'] and not seen_imp and not is_mod:
            if any(x in l for x in ('/-', '-/')): return None
            is_mod = True; continue
        if t[0] == 'prelude':
            return None
        if 'import' in t[:4] and t[0] in ('import', 'public', 'private', 'meta'):
            if any(x in l for x in ('/-', '-/')): return None
            seen_imp = True
            idx = t.index('import')
            pre = t[:idx]; aft = t[idx + 1:]
            if any(w not in ('public', 'private', 'meta') for w in pre):
                return None
            has_all = False
            if aft and aft[0] == 'all':
                has_all = True; aft = aft[1:]
            if len(aft) != 1:
                return None
            mod = aft[0]
            if has_all or ('meta' in pre):
                vis = 'special:' + ('pub:' if 'public' in pre else '') + ('meta:' if 'meta' in pre else '') + ('all:' if has_all else '')
            elif 'public' in pre:
                vis = 'public'
            elif 'private' in pre:
                vis = 'private'
            else:
                vis = 'plain'
            out.append((i, vis, mod))
            continue
        break
    return is_mod, out


def parse_header(lines):
    """Backward-compatible wrapper returning [(line_index, module)] for plain non-module files, else None."""
    r = parse_header_ext(lines)
    if r is None:
        return None
    is_mod, items = r
    if is_mod or any(vis != 'plain' for (_, vis, _) in items):
        return None
    return [(i, m) for (i, _, m) in items]


def ext_graph_ext(roots):
    """-> {mod: (is_mod, [(vis, target_mod)])} for external packages + toolchain."""
    E = {}
    for src in roots:
        for root, dirs, files in os.walk(src):
            dirs[:] = [d for d in dirs if d not in ('.lake', '.git', 'test', 'tests')]
            for f in files:
                if not f.endswith('.lean'): continue
                p = os.path.join(root, f); mod = os.path.relpath(p, src)[:-5].replace('/', '.')
                if mod in E: continue
                try:
                    lines = open(p, encoding='utf-8', errors='replace').read().split('\n')
                except OSError:
                    continue
                r = parse_header_ext(lines[:400])
                if r is not None:
                    is_m, items = r
                    E[mod] = (is_m, [(vis, c) for (_, vis, c) in items])
                else:
                    # fallback scan
                    imps = []; incomment = False; is_m = False
                    for line in lines[:400]:
                        s = line.strip()
                        if incomment:
                            if '-/' in s: incomment = False
                            continue
                        if s.startswith('/-'):
                            if '-/' not in s: incomment = True
                            continue
                        s = s.split('--')[0].strip()
                        if not s: continue
                        if s == 'module': is_m = True; continue
                        if s == 'prelude': continue
                        toks = s.split()
                        if 'import' in toks[:4] and toks[0] in ('import', 'public', 'meta', 'private'):
                            idx = toks.index('import'); pre = toks[:idx]; rest = toks[idx + 1:]
                            has_all = bool(rest and rest[0] == 'all')
                            if has_all: rest = rest[1:]
                            vis = 'special:' if (has_all or 'meta' in pre) else ('public' if 'public' in pre else ('private' if 'private' in pre else 'plain'))
                            for x in rest: imps.append((vis, x))
                            continue
                        break
                    E[mod] = (is_m, imps)
    return E


def ext_graph(roots):
    ee = ext_graph_ext(roots)
    return {m: [c for (_, c) in items] for m, (_, items) in ee.items()}


def closures(allg):
    order = []; seen = set()
    for m in list(allg):
        if m in seen: continue
        stack = [(m, iter(allg.get(m, [])))]; seen.add(m)
        while stack:
            n, it = stack[-1]
            for c in it:
                if c not in seen: seen.add(c); stack.append((c, iter(allg.get(c, [])))); break
            else: stack.pop(); order.append(n)
    idx = {m: i for i, m in enumerate(order)}; clo = {}
    for m in order:
        b = 0
        for c in allg.get(m, []):
            if c in idx: b |= clo[c] | (1 << idx[c])
        clo[m] = b
    return idx, clo


def reduce_imports(G, E):
    """Original plain-mode C1+C2 import reducer (used when no `module` files exist)."""
    allg = dict(E); allg.update(G)
    idx, clo = closures(allg)
    cl = lambda c: (clo[c] | (1 << idx[c])) if c in idx else 0
    drop = {}
    for m, L in G.items():
        d = {}; pre = 0; suffix = [0] * (len(L) + 1)
        for k in range(len(L) - 1, -1, -1): suffix[k] = suffix[k + 1] | cl(L[k])
        for k, c in enumerate(L):
            b = (1 << idx[c]) if c in idx else 0
            if b and pre & b: d[k] = 'IMP-C1'
            elif b and suffix[k + 1] & b: d[k] = 'IMP-C2'
            else: pre |= cl(c)
        drop[m] = d
    newlist = lambda m: [c for k, c in enumerate(G[m]) if k not in drop[m]]
    while True:
        first = {m: (newlist(m) or [None])[0] for m in G}
        def on_chain(j, c):
            n = j; steps = 0
            while n is not None and steps < 1000000:
                if n == c: return True
                if n in G: n = first[n]
                else:
                    ext = allg.get(n, []); n = ext[0] if ext else None
                steps += 1
            return False
        changed = 0
        for m, L in G.items():
            d = drop[m]
            for k in sorted(d):
                if d[k] != 'IMP-C2': continue
                j = next((L[t] for t in range(k + 1, len(L)) if t not in d), None)
                if j is None or not on_chain(j, L[k]): del d[k]; changed += 1
            pre = 0
            for k, c in enumerate(L):
                if d.get(k) == 'IMP-C1':
                    if not (c in idx and pre & (1 << idx[c])): del d[k]; changed += 1; pre |= cl(c)
                elif k not in d: pre |= cl(c)
        if not changed: break
    return drop, {m: newlist(m) for m in G}


def reduce_imports_modsys(G_ext, E_ext):
    """Module-system-aware G1 import reducer.
    G_ext, E_ext: {mod: (is_mod, [(vis, target_mod)])}.
    Returns (drop, N_ext) where drop = {mod: {pos: 'IMP-C1'|'IMP-C2'}}, N_ext = {mod: (is_mod, kept_items)}."""
    any_mod = any(is_m or any(v != 'plain' for (v, _) in items) for (is_m, items) in G_ext.values())
    if not any_mod:
        G_plain = {m: [c for (_, c) in items] for m, (_, items) in G_ext.items()}
        E_plain = {m: [c for (_, c) in items] for m, (_, items) in E_ext.items()}
        drop, N_plain = reduce_imports(G_plain, E_plain)
        N_ext = {m: (False, [('plain', c) for c in N_plain[m]]) for m in G_ext}
        return drop, N_ext

    all_ext = dict(E_ext); all_ext.update(G_ext)
    # Re-exported non-special edges: `public` in `module` files, `plain`/`public` in non-`module` files
    reexp_graph = {}
    for m, (is_m, items) in all_ext.items():
        edges = []
        for (vis, c) in items:
            if vis.startswith('special:'): continue
            if is_m:
                if vis == 'public': edges.append(c)
            else:
                if vis in ('plain', 'public'): edges.append(c)
        reexp_graph[m] = edges
    idx, pub_clo = closures(reexp_graph)
    pcl = lambda c: (pub_clo[c] | (1 << idx[c])) if c in idx else 0

    drop = {}
    N_ext = {}
    for m, (is_m, items) in G_ext.items():
        d = {}
        pre_any = 0
        pre_reexp = 0
        for k, (vis, c) in enumerate(items):
            if vis.startswith('special:'):
                continue
            b = (1 << idx[c]) if c in idx else 0
            eff_reexp = (vis == 'public') if is_m else (vis in ('plain', 'public'))
            if eff_reexp:
                if b and (pre_reexp & b):
                    d[k] = 'IMP-C1'
                else:
                    pc = pcl(c)
                    pre_reexp |= pc
                    pre_any |= pc
            else:
                if b and (pre_any & b):
                    d[k] = 'IMP-C1'
                else:
                    pre_any |= pcl(c)
        drop[m] = d
        N_ext[m] = (is_m, [it for k, it in enumerate(items) if k not in d])
    return drop, N_ext


def fmt_modsys_edge(vis, c):
    if vis == 'public': return 'pub:' + c
    if vis == 'private': return 'priv:' + c
    if vis.startswith('special:'): return vis[len('special:'):] + c
    return c


OPT = re.compile(r'^set_option\s+(\S+)\s+(\S+)(\s+in)?\s*$')
LIM = {'maxHeartbeats', 'synthInstance.maxHeartbeats'}
LEAN_DEFAULTS = {'autoImplicit': 'true', 'relaxedAutoImplicit': 'true', 'maxSynthPendingDepth': '1',
                 'maxHeartbeats': '200000', 'synthInstance.maxHeartbeats': '20000'}


NS_ONLY = re.compile(r'^namespace\s+(\S+)\s*(?:--.*)?$')
SEC_ONLY = re.compile(r'^(?:public\s+)?(?:noncomputable\s+)?section(?:\s+([^\s-]\S*))?\s*(?:--.*)?$')
END_ONLY = re.compile(r'^end(?:\s+([^\s-]\S*))?\s*(?:--.*)?$')


def opt_edits(mod, lines, base):
    stack = [{}]; res = []
    def eff(k):
        for s in reversed(stack):
            if k in s: return s[k]
        return base.get(k)
    for i, l in enumerate(lines):
        if not l or l[0].isspace(): continue
        mn = NS_ONLY.match(l)
        if mn:
            for _ in mn.group(1).split('.'): stack.append({})
            continue
        ms = SEC_ONLY.match(l)
        if ms:
            for _ in (ms.group(1).split('.') if ms.group(1) else ['']): stack.append({})
            continue
        me = END_ONLY.match(l)
        if me:
            kpop = len(me.group(1).split('.')) if me.group(1) else 1
            if kpop >= len(stack): stack = [{}]
            else: del stack[len(stack) - kpop:]
            continue
        if l.startswith('namespace ') or re.match(r'^(public\s+)?(noncomputable\s+)?section\b', l) or l.startswith('end '):
            # Multi-command line (e.g. `namespace X ... end X`): conservatively forget in-file scopes so OPT-O1 never drops a live option
            stack = [{}]
            continue
        m = OPT.match(l)
        if not m: continue
        k, v, isin = m.group(1), m.group(2), bool(m.group(3))
        e = eff(k)
        if e is not None and v == e: c = 'OPT-O1'
        elif k.startswith('linter.'): c = 'OPT-O3'
        elif k in LIM and e is not None and v.isdigit() and e.isdigit() and int(v) > 0 and (int(e) == 0 or int(v) < int(e)): c = 'OPT-O2'
        else: c = None
        if c: res.append((i, c, k, v, isin))
        if not isin and c is None: stack[-1][k] = v
    return res


def _toml_val(v):
    v = v.strip()
    if v.startswith('"'): return v.strip('"')
    if v in ('true', 'false'): return v
    return v


def _toml_inline(v):
    v = v.strip()[1:-1]; d = {}
    for part in v.split(','):
        if '=' in part:
            k, x = part.split('=', 1); d[k.strip().strip('"')] = _toml_val(x)
    return d


def _toml_list(v):
    return [x.strip().strip('"') for x in v.strip()[1:-1].split(',') if x.strip()]


NCS_DEFLIKE = re.compile(r'\b(def|abbrev|example|alias|instance|structure|class|inductive|opaque|irreducible_def|deriving|where|let rec|'
                         r'macro|syntax|elab|notation|infix|infixl|infixr|prefix|postfix|initialize|mutual|partial|unsafe|'
                         r'implemented_by|extern|csimp|export)\b')


def ncs_edits(lines):
    if any(NCS_DEFLIKE.search(l) for l in lines if l and not l.lstrip().startswith('--')): return []
    stack = []; res = []
    cmd_idx = [i for i, l in enumerate(lines) if l and not l[0].isspace()]
    for i in cmd_idx:
        l = lines[i].rstrip()
        if l.startswith('namespace '): stack.append(('ns', i)); continue
        if re.match(r'^(public\s+)?(noncomputable\s+)?section\b', l):
            stack.append(('ncs' if l == 'noncomputable section' else 'sec', i)); continue
        if l == 'end' or l.startswith('end '):
            if not stack: return []
            k, j = stack.pop()
            if k == 'ncs' and l == 'end':
                if i == cmd_idx[-1] and not stack: res += [j, i]
            continue
    for k, j in stack:
        if k == 'ncs' and all(kk != 'ncs' or jj == j for kk, jj in stack): res.append(j)
    return sorted(set(res))


def lake_options(project):
    p = os.path.join(project, 'lakefile.toml')
    base = dict(LEAN_DEFAULTS); libs = []
    if not os.path.exists(p): return base, libs
    sect = None; cur = None
    for raw in open(p, encoding='utf-8'):
        l = raw.split('#')[0].strip()
        if not l: continue
        if l.startswith('[['):
            sect = l.strip('[]').strip(); cur = {'globs': [], 'opts': {}} if sect == 'lean_lib' else None
            if cur is not None: libs.append(cur)
            continue
        if l.startswith('['): sect = l.strip('[]').strip(); cur = None; continue
        if '=' not in l: continue
        k, v = l.split('=', 1); k = k.strip().strip('"')
        if sect == 'leanOptions': base[k] = _toml_val(v)
        elif sect == 'lean_lib' and cur is not None:
            if k in ('globs', 'roots'): cur['globs'] += _toml_list(v)
            elif k == 'leanOptions': cur['opts'].update(_toml_inline(v))
    return base, [(c['globs'], c['opts']) for c in libs if c['opts']]


def lib_base(mod, base, libs):
    d = dict(base)
    for globs, o in libs:
        for g in globs:
            if (g.endswith('.+') and mod.startswith(g[:-1])) or (g.endswith('.*') and mod.startswith(g[:-1])) or mod == g:
                d.update(o); break
    return d


def resolve_srcdir(project, srcdir_arg):
    cand = os.path.join(project, srcdir_arg)
    if srcdir_arg != 'src' or os.path.isdir(cand):
        return cand
    lf = os.path.join(project, 'lakefile.toml')
    if os.path.exists(lf):
        head = open(lf, encoding='utf-8').read().split('\n[[', 1)[0]
        m = re.search(r'^srcDir\s*=\s*"([^"]*)"', head, re.M)
        if m:
            return os.path.join(project, m.group(1))
    return project


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('project'); ap.add_argument('--edits', required=True)
    ap.add_argument('--classes', default='imp,opt')
    ap.add_argument('--srcdir', default='src')
    ap.add_argument('--packages', default=None)
    ap.add_argument('--toolchain-src', default=None)
    ap.add_argument('--json', default=None); ap.add_argument('--graph-out', default=None)
    ap.add_argument('--owner', default='P04')
    ap.add_argument('--strict-headers', action='store_true', help='exit if any file has an unsupported import header')
    a = ap.parse_args()
    classes = set(a.classes.split(','))
    src = resolve_srcdir(a.project, a.srcdir)
    files = {}
    for root, dirs, fs in os.walk(src):
        dirs[:] = [d for d in dirs if d not in ('.lake', '.git')]
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(root, f); files[os.path.relpath(p, src)[:-5].replace('/', '.')] = p
    texts = {m: open(p, encoding='utf-8').read().split('\n') for m, p in files.items()}
    hdr = {}; skipped_hdr = []
    for m, lines in texts.items():
        h = parse_header_ext(lines)
        if h is None:
            if a.strict_headers:
                sys.exit(f'normalize: unsupported header in {m}')
            skipped_hdr.append(m)
            continue
        hdr[m] = h
    G_ext = {m: (is_m, [(vis, c) for (_, vis, c) in items]) for m, (is_m, items) in hdr.items()}
    any_modsys = any(is_m or any(v != 'plain' for (v, _) in items) for (is_m, items) in G_ext.values())
    pk = a.packages or os.path.join(a.project, '.lake', 'packages')
    roots = [os.path.join(pk, d) for d in sorted(os.listdir(pk))] if os.path.isdir(pk) else []
    if a.toolchain_src: roots.append(a.toolchain_src)
    E_ext = ext_graph_ext(roots)
    st = collections.Counter(); edits = []
    lines_before = sum(len(t) - (1 if t and t[-1] == '' else 0) for t in texts.values())
    if 'imp' in classes:
        drop, N_ext = reduce_imports_modsys(G_ext, E_ext)
        for m, d in drop.items():
            items = hdr[m][1]
            for k, c in d.items():
                i = items[k][0]; edits.append((m, i + 1, i + 1, 'delete', a.owner, '', c)); st[c] += 1
        if a.graph_out:
            with open(a.graph_out + '.old.txt', 'w') as f1, open(a.graph_out + '.new.txt', 'w') as f2, open(a.graph_out + '.roots.txt', 'w') as f3:
                if not any_modsys:
                    for m, (_, v) in E_ext.items():
                        s = ' '.join(c for (_, c) in v)
                        f1.write(m + ' ' + s + '\n'); f2.write(m + ' ' + s + '\n')
                    for m, (_, v) in G_ext.items():
                        f1.write(m + ' ' + ' '.join(c for (_, c) in v) + '\n')
                        f2.write(m + ' ' + ' '.join(c for (_, c) in N_ext[m][1]) + '\n')
                        f3.write(m + '\n')
                else:
                    for m, (is_m, v) in E_ext.items():
                        tag = (m + '@mod') if is_m else m
                        s = ' '.join(fmt_modsys_edge(vis, c) for (vis, c) in v)
                        f1.write(tag + ' ' + s + '\n'); f2.write(tag + ' ' + s + '\n')
                    for m, (is_m, v) in G_ext.items():
                        tag = (m + '@mod') if is_m else m
                        f1.write(tag + ' ' + ' '.join(fmt_modsys_edge(vis, c) for (vis, c) in v) + '\n')
                        f2.write(tag + ' ' + ' '.join(fmt_modsys_edge(vis, c) for (vis, c) in N_ext[m][1]) + '\n')
                        f3.write(m + '\n')
    if 'opt' in classes or 'optres' in classes:
        base, libs = lake_options(a.project)
        for m, lines in texts.items():
            for (i, c, k, v, isin) in opt_edits(m, lines, lib_base(m, base, libs)):
                if c == 'OPT-O2' and 'optres' not in classes: continue
                if c in ('OPT-O1', 'OPT-O3') and 'opt' not in classes: continue
                edits.append((m, i + 1, i + 1, 'delete', a.owner, '', c)); st[c] += 1
    if 'ncs' in classes:
        for m, lines in texts.items():
            for i in ncs_edits(lines):
                edits.append((m, i + 1, i + 1, 'delete', a.owner, '', 'NCS')); st['NCS'] += 1
    seen = set(); uniq = []
    for e in sorted(edits):
        if (e[0], e[1]) in seen: continue
        seen.add((e[0], e[1])); uniq.append(e)
    edits = uniq
    with open(a.edits, 'w', encoding='utf-8') as f:
        for e in edits: f.write('\t'.join(map(str, e[:6])) + '\n')
    with open(a.edits + '.classes.tsv', 'w', encoding='utf-8') as f:
        for e in edits: f.write(f'{e[0]}\t{e[1]}\t{e[6]}\n')
    stats = {'modules': len(texts), 'module_system_files': sum(1 for (im, _) in G_ext.values() if im),
             'skipped_headers': len(skipped_hdr), 'lines_before': lines_before, 'edits': len(edits),
             'by_class': dict(st), 'import_lines_before': sum(len(v) for (_, v) in G_ext.values())}
    print(json.dumps(stats))
    if a.json: json.dump(stats, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""consolidate.py DECLS_TSV SRCMAP_TSV IMPORTS_TSV OUTDIR [--modules ALLCONSTS_TSV] [--project-prefix-file F]

Plan the source-level consolidation of same-statement theorems (G2 'merge duplicate theorems', export side: exphash).

A class = project theorems with equal kernel statement hash (type_hk) and equal level-parameter names.  For every class
we pick a representative R and, for every other member T, decide whether T can be rewritten as `alias T := R`
(T keeps its name, so no use site changes; its proof disappears):
  * R must be visible in T's module: same module and R's declaration ends before T's starts, or R's module is a
    transitive import of T's module (import graph from the sources);
  * the source hash (binder infos included) must be equal, else implicit/explicit argument positions would change at
    T's use sites (binder NAMES are not compared: a use with named arguments `(h := ..)` can still break - the build
    catches it);
  * T must be found in the source outline (srcmap) as a `theorem`/`lemma` (auto-generated names have no source).
R = the member visible to the most other members (ties: the shortest source text).  Writes OUTDIR/plan.tsv (one row per
rewrite: module, name, start, end, nlines, target R, R's module) and OUTDIR/plan.json (counts, lines saved, and why the
other members cannot be rewritten)."""
import sys, os, json, argparse, collections

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('decls'); ap.add_argument('srcmap'); ap.add_argument('imports'); ap.add_argument('out')
    ap.add_argument('--modules', help="S02 allconsts.tsv (name, module, kind): restrict to project constants")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    # source outline
    src = {}
    for line in open(a.srcmap):
        p = line.rstrip('\n').split('\t')
        if p[0] in ('name', '-'):
            continue
        src[p[0]] = (p[1], p[2], int(p[3]), int(p[4]), int(p[5]))
    mods = None
    if a.modules:
        mods = {}
        for line in open(a.modules):
            p = line.rstrip('\n').split('\t')
            mods[p[0]] = p[1]
    # import graph + topological index
    imp = {}
    for line in open(a.imports):
        p = line.rstrip('\n').split('\t')
        imp[p[0]] = [x for x in (p[1].split() if len(p) > 1 else [])]
    order = {}
    sys.setrecursionlimit(1000000)
    state = {}
    topo = []
    for m in imp:
        if m in state:
            continue
        stack = [(m, iter(imp.get(m, ())))]
        state[m] = 1
        while stack:
            node, it = stack[-1]
            nxt = None
            for c in it:
                if c in imp and c not in state:
                    nxt = c
                    break
            if nxt is None:
                stack.pop(); state[node] = 2; topo.append(node)
            else:
                state[nxt] = 1
                stack.append((nxt, iter(imp.get(nxt, ()))))
    for i, m in enumerate(topo):
        order[m] = i
    reach_cache = {}
    def imports_trans(mi, mr):
        """does module mi transitively import mr?"""
        if mi == mr:
            return False
        key = (mi, mr)
        if key in reach_cache:
            return reach_cache[key]
        lo = order.get(mr, -1)
        if lo < 0 or order.get(mi, -1) < lo:
            reach_cache[key] = False
            return False
        seen = {mi}
        st = [mi]
        found = False
        while st and not found:
            x = st.pop()
            for c in imp.get(x, ()):
                if c == mr:
                    found = True
                    break
                if c in seen or order.get(c, -1) < lo:
                    continue
                seen.add(c)
                st.append(c)
        reach_cache[key] = found
        return found
    # classes
    cls = collections.defaultdict(list)
    with open(a.decls) as f:
        hdr = f.readline().rstrip('\n').split('\t')
        ix = {k: i for i, k in enumerate(hdr)}
        for line in f:
            p = line.rstrip('\n').split('\t')
            if p[ix['kind']] != 'thm':
                continue
            name = p[ix['name']]
            if mods is not None and name not in mods:
                continue
            cls[(p[ix['type_hk']], p[ix['lvl_h']])].append((name, p[ix['type_hs']], int(p[ix['new_bytes']])))
    stats = collections.Counter()
    lines_saved = 0
    bytes_saved = 0
    rows = []
    for key, mem in cls.items():
        if len(mem) < 2:
            continue
        stats['classes'] += 1
        stats['members'] += len(mem)
        insrc = [m for m in mem if m[0] in src and src[m[0]][1] in ('theorem', 'lemma')]
        stats['members_without_source'] += len(mem) - len(insrc)
        if len(insrc) < 2:
            stats['classes_lt2_in_source'] += 1
            continue
        def visible(r, t):
            mr, _, rs, re_, _ = src[r[0]]
            mt, _, ts, te, _ = src[t[0]]
            if mr == mt:
                return re_ < ts
            return imports_trans(mt, mr)
        best = None
        for r in insrc:
            vis = [t for t in insrc if t is not r and t[1] == r[1] and visible(r, t)]
            score = (len(vis), -src[r[0]][4])
            if best is None or score > best[0]:
                best = (score, r, vis)
        _, r, vis = best
        visn = set(t[0] for t in vis)
        for t in insrc:
            if t is r:
                continue
            if t[0] in visn:
                mt, kw, ts, te, nl = src[t[0]]
                rows.append((mt, t[0], ts, te, nl, r[0], src[r[0]][0]))
                stats['rewrites'] += 1
                lines_saved += nl - 1
                bytes_saved += t[2]
                stats['rewrite_same_module' if mt == src[r[0]][0] else 'rewrite_cross_module'] += 1
            elif t[1] != r[1]:
                stats['blocked_binderinfo_differs'] += 1
            else:
                stats['blocked_not_visible'] += 1
    rows.sort()
    with open(os.path.join(a.out, 'plan.tsv'), 'w') as f:
        f.write('module\tname\tstart\tend\tnlines\ttarget\ttarget_module\n')
        for r in rows:
            f.write('\t'.join(map(str, r)) + '\n')
    res = dict(stats)
    res['source_lines_saved'] = lines_saved
    res['export_bytes_of_rewritten_decls'] = bytes_saved
    res['modules_touched'] = len(set(r[0] for r in rows))
    json.dump(res, open(os.path.join(a.out, 'plan.json'), 'w'), indent=1)
    print(json.dumps(res, indent=1))

if __name__ == '__main__':
    main()

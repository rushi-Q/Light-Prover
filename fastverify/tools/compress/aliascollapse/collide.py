#!/usr/bin/env python3
"""collide.py SRC EXT_IMPORTS.pkl DEPSRC... --out DENY.txt [--pairs flt] [--jobs J]

Static pre-filter for collapse.py: a pair (M inlined into H) is DENIED when M's body would see a declaration it never saw
before with the same full name as one of its own declarations (Lean: "a non-private declaration X has already been
declared" when M declares X - private or not - and a module newly imported through H declares X publicly).
  extra(M, H) = closure(imports(H) - {M}) - closure(imports(M))      (project + dependency import graph)
  deny  iff  names(M) & public_names(extra) != {}
Names are read from source with the package's own scanner (build/mergeplan.py scan(): namespace-resolved declaration
names, `_root_`, private) for project modules and dependency modules (DEPSRC = source roots of Mathlib and the other
packages). Approximate (generated names such as structure fields / instances are not seen); residual failures are
caught by the build (collapse.py --deny FILE keeps the pair separate).
"""
import os, sys, pickle, collections, json
from concurrent.futures import ProcessPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, '..', '..', '..', 'build')))
import mergeplan  # noqa: E402


def walk(root):
    out = {}
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if x not in ('.lake', '.git', 'test', 'tests')]
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(d, f); out[os.path.relpath(p, root)[:-5].replace(os.sep, '.')] = p
    return out


def scan1(p):
    try:
        r = mergeplan.scan(p)
    except Exception:
        return None
    if r is None: return None
    norm = lambda n: n.rsplit('_root_.', 1)[1] if '_root_.' in n else n   # mergeplan resolves `_root_` only for public decls
    return (r['imports'], [norm(n) for n in r['decls']], [norm(n) for n in r['privs']])


def main():
    a, pos, optv = sys.argv[1:], [], {}
    i = 0
    while i < len(a):
        if a[i].startswith('--'): optv[a[i]] = a[i + 1]; i += 2
        else: pos.append(a[i]); i += 1
    src, extp, deps = pos[0], pos[1], pos[2:]
    out = optv['--out']; jobs = int(optv.get('--jobs', 32))
    proj = walk(src)
    dep = {}
    for r in deps: dep.update(walk(r))
    E = {} if extp in ('-', '/dev/null') else pickle.load(open(extp, 'rb'))   # '-': dependency graph from DEPSRC only
    paths = dict(dep); paths.update(proj)
    names = list(paths)
    with ProcessPoolExecutor(jobs) as ex:
        res = dict(zip(names, ex.map(scan1, [paths[n] for n in names], chunksize=256)))
    graph = {}
    for n in names:
        r = res.get(n)
        graph[n] = (r[0] if r else E.get(n, []))
    for n, v in E.items(): graph.setdefault(n, v)
    # closure bitsets in topological order
    order, seen = [], set()
    for s in graph:
        if s in seen: continue
        stack = [(s, iter(graph[s]))]; seen.add(s)
        while stack:
            n, it = stack[-1]
            for c in it:
                if c in graph and c not in seen: seen.add(c); stack.append((c, iter(graph[c]))); break
            else: stack.pop(); order.append(n)
    idx = {m: i for i, m in enumerate(order)}
    clo = {}
    for m in order:
        b = 1 << idx[m]
        for c in graph[m]:
            if c in clo: b |= clo[c]
        clo[m] = b
    pub = {n: set(res[n][1]) if res.get(n) else set() for n in names}
    own = {n: set(res[n][1]) | set(res[n][2]) if res.get(n) else set() for n in proj}
    pairs = []
    for m in sorted(proj):
        if m.startswith('P2M.Sol.S_'):
            h = 'Theorems.Thm_' + m[len('P2M.Sol.S_'):]
            if h in proj: pairs.append((m, h))
    deny, stats = [], collections.Counter()
    for m, h in pairs:
        cm = 0
        for c in graph[m]: cm |= clo.get(c, 0)
        ch = 0
        for c in graph[h]:
            if c != m: ch |= clo.get(c, 0)
        extra = ch & ~cm
        if not extra: stats['no_extra'] += 1; continue
        mine = own.get(m, set())
        hit = None
        x = extra
        while x and mine:
            low = x & -x; i = low.bit_length() - 1; x ^= low
            mod = order[i]
            inter = mine & pub.get(mod, set())
            if inter: hit = (mod, sorted(inter)[:3]); break
        if hit: deny.append((m, hit)); stats['deny'] += 1
        else: stats['ok'] += 1
    with open(out, 'w') as f:
        for m, (mod, nm) in deny: f.write(f'{m}\t{mod}\t{" ".join(nm)}\n')
    print(json.dumps({'pairs': len(pairs), **stats, 'deny_file': out}, indent=1))


if __name__ == '__main__':
    main()

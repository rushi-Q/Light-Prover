#!/usr/bin/env python3
"""dedup_delta.py BASE_DEDUP.tsv NEW_DEDUP.tsv DECLS_TSV OUT.tsv --base LIST... --texts LIST... [--owner KEY]

Stage-3 integrator: the part of a NEW dedup plan that can join a train whose pruning rounds (P01, P01r2) were
computed with the BASE dedup plan inside their fixpoint. Swapping the whole plan would invalidate those rounds (a new
round 1 can resurrect declarations that a round 2 computed on the previous candidate's oleans cannot see); a DELTA of
whole groups that is consistent with the base deletions is safe to add after them.

Groups (rows present in NEW but not in BASE):
  alias group     a `replace` row `alias D := _root_.T` at D's declaration + the `import M` inserts of the same module
                  whose M declares T
  redirect group  the `delete` rows of D + every `subst` row `D NEW` (D = the deleted declaration's full name), + the
                  `import M` inserts of modules with a subst row, M declaring the target
  orphan import   an `import` insert matched to no group (dropped: it would only add visibility)
A group is dropped when: its target T or D is deleted by a --base list (P01 / P01r2 / BASE delete rows, deletefile =
whole module); D is touched by BASE (any BASE row anchored at D or a BASE subst with OLD = D); any of its line rows
overlaps a --base row (an import insert inside a header that P01 rewrites would be lost: the alias would then not see
T); an imported module is deleted; for redirect groups, D's name occurs as a token in a --texts list (an edit written
against the original tree that still uses D, e.g. an automation proof). Untrusted; only drops.
"""
import bisect, collections, re, sys

def load(p):
    return [l.rstrip('\n').split('\t') for l in open(p, encoding='utf-8') if l.strip()]

def key(x):
    return tuple(x[:4]) + (x[5] if len(x) > 5 else '',)

TOK = re.compile(r"[A-Za-z_][\w'.!?]*")
ALIAS = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)*alias\s+(\S+)\s*:=\s*(?:_root_\.)?(\S+)')

def main(a):
    base_f, new_f, decls_f, out = a[1:5]
    opts = {'--base': [], '--texts': [], '--owner': ['P03-dedup-v2']}; cur = None
    for x in a[5:]:
        if x in opts: cur = x; opts[x] = [] if x != '--owner' else []; continue
        opts[cur].append(x)
    owner = (opts['--owner'] or ['P03-dedup-v2'])[0]
    D = collections.defaultdict(list); mod_of = collections.defaultdict(set)
    for ln in open(decls_f, encoding='utf-8'):
        if ln.startswith('#'): continue
        p = ln.rstrip('\n').split('\t')
        if len(p) < 7: continue
        ns = p[6].split(); D[p[0]].append((int(p[1]), int(p[2]), ns))
        for n in ns: mod_of[n].add(p[0])
    for m in D: D[m].sort()
    starts = {m: [d[0] for d in L] for m, L in D.items()}
    def decl_at(m, s):
        L = D.get(m)
        if not L: return None
        k = bisect.bisect_right(starts[m], s) - 1
        return L[k] if k >= 0 and L[k][0] <= s <= L[k][1] else None
    base = load(base_f); new = load(new_f)
    kb = set(map(key, base))
    delta = [x for x in new if key(x) not in kb]
    # deletions and line rows of the --base lists (BASE dedup included)
    gone_mod = set(); iv = collections.defaultdict(list); lines = collections.defaultdict(list)
    for f in opts['--base'] + [base_f]:
        for p in load(f):
            if len(p) < 4: continue
            if p[3] == 'deletefile': gone_mod.add(p[0])
            elif p[3] == 'delete': iv[p[0]].append((int(p[1]), int(p[2])))
            if p[3] in ('delete', 'replace'): lines[p[0]].append((int(p[1]), int(p[2])))
    deleted = set()
    for m, L in D.items():
        I = sorted(iv.get(m, ())); ss = [x for x, _ in I]
        for s, e, ns in L:
            if m in gone_mod: deleted.update(ns); continue
            k = bisect.bisect_right(ss, s) - 1
            if k >= 0 and I[k][0] <= s <= I[k][1]: deleted.update(ns)
    for m in lines: lines[m].sort()
    def overlaps(m, s, e, ins):
        for bs, be in lines.get(m, ()):
            if bs > max(s, e): break
            if ins:
                if bs <= s <= be: return True
            elif not (be < s or bs > e): return True
        return False
    base_touched = set()
    for p in base:
        if p[3] == 'subst' and len(p) > 5: base_touched.add(p[5].split()[0])
        elif p[3] in ('delete', 'replace'):
            d = decl_at(p[0], int(p[1]))
            if d: base_touched.update(d[2])
    text_tokens = set()
    for f in opts['--texts']:
        for p in load(f):
            if len(p) > 5 and p[3] in ('replace', 'insert_before'):
                text_tokens.update(TOK.findall(p[5].replace('\\n', '\n')))
    groups = {}; imports = collections.defaultdict(list); why = collections.Counter()
    def G(k):
        return groups.setdefault(k, {'rows': [], 'D': set(), 'T': set(), 'mods_subst': set(), 'kind': k[0], 'bad': None})
    for x in delta:
        act = x[3]; txt = x[5] if len(x) > 5 else ''
        if act == 'insert_before' and txt.strip().startswith('import '):
            imports[x[0]].append(x); continue
        if act == 'replace':
            mm = ALIAS.match(txt.replace('\\n', '\n'))
            d = decl_at(x[0], int(x[1]))
            g = G(('alias', x[0], int(x[1]))); g['rows'].append(x)
            if mm: g['T'].add(mm.group(2))
            else: g['bad'] = g['bad'] or 'replace row that is not an alias'
            if d: g['D'].update(d[2])
            continue
        if act == 'delete':
            d = decl_at(x[0], int(x[1]))
            if not d: G(('orphan', x[0], int(x[1])))['rows'].append(x); continue
            for n in d[2]:
                g = G(('redirect', n)); g['rows'].append(x); g['D'].add(n)
            continue
        if act == 'subst':
            old, newn = (txt.split() + ['', ''])[:2]
            g = G(('redirect', old)); g['rows'].append(x); g['D'].add(old)
            g['T'].add(newn[7:] if newn.startswith('_root_.') else newn); g['mods_subst'].add(x[0])
            continue
        G(('other', x[0], x[1], act))['rows'].append(x)
    # imports couple the groups of a module: v2's inserts are per module (one row may carry several imports, of
    # modules that provide the targets transitively), so the groups touching a module with v2 inserts stand or fall
    # together with those inserts (fixpoint: a redirect group touches every module with one of its rows)
    touch = collections.defaultdict(set)          # module -> group keys
    gmods = {}
    for k, g in groups.items():
        ms = set(x[0] for x in g['rows']); gmods[k] = ms
        for m in ms: touch[m].add(k)
    for m, rows in imports.items():
        if not touch.get(m): why['orphan import row'] += len(rows); continue
    bad = {}
    for k, g in groups.items():
        r = g['bad']
        if r is None and k[0] in ('orphan', 'other'): r = k[0] + ' row'
        if r is None and any(t in deleted for t in g['T']): r = 'target deleted by the base lists'
        if r is None and any(d in deleted for d in g['D']): r = 'duplicate deleted by the base lists'
        if r is None and any(d in base_touched for d in g['D']): r = 'duplicate already handled by the base dedup plan'
        if r is None:
            for x in g['rows']:
                if x[3] == 'subst': continue
                if overlaps(x[0], int(x[1]), int(x[2]), False): r = 'line rows overlap a base edit'; break
        if r is None and k[0] == 'redirect':
            shorts = set()
            for d in g['D']:
                ps = d.split('.'); shorts.update('.'.join(ps[i:]) for i in range(len(ps)))
            if shorts & text_tokens: r = 'deleted duplicate still named by another list'
        if r: bad[k] = r
    badmod = {}
    for m, rows in imports.items():
        if not touch.get(m): continue
        for x in rows:
            ms = [t for ln in x[5].replace('\\n', '\n').split('\n') for t in ln.split()[1:2] if ln.strip().startswith('import')]
            if any(M in gone_mod for M in ms): badmod[m] = 'imports a deleted module'
            elif overlaps(m, int(x[1]), int(x[2]), True): badmod[m] = 'import insert inside a base header rewrite'
    changed = True
    while changed:
        changed = False
        for k in list(groups):
            if k in bad: continue
            for m in gmods[k]:
                if m in badmod: bad[k] = 'coupled: ' + badmod[m]; changed = True; break
        for k, r in list(bad.items()):
            for m in gmods[k]:
                if m in imports and m not in badmod: badmod[m] = 'coupled to a dropped group'; changed = True
    kept = []
    for k, g in groups.items():
        if k in bad: why[bad[k].split(':')[0] if bad[k].startswith('coupled') else bad[k]] += 1; continue
        why['kept ' + k[0]] += 1; kept.extend(g['rows'])
    for m, rows in imports.items():
        if touch.get(m) and m not in badmod: kept.extend(rows)
    why['import rows kept'] = sum(len(r) for m, r in imports.items() if touch.get(m) and m not in badmod)
    seen = set()
    with open(out, 'w', encoding='utf-8') as fo:
        for x in kept:
            kx = key(x)
            if kx in seen: continue
            seen.add(kx); y = list(x); y[4] = owner
            fo.write('\t'.join(y) + '\n')
    print(f'dedup_delta: new rows {len(delta)} -> kept {len(seen)} rows; groups: ' + ', '.join(f'{k} {v}' for k, v in why.most_common()))

if __name__ == '__main__':
    main(sys.argv)

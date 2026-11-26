#!/usr/bin/python3 -I
"""refs_index.py OUT.pkl TSV... [--targets t1,t2,...] [--ilean-root BUILD/lib/lean] [--live-from-export SOLUTION.export]

Stage 1 of the closure pruner. Reads olean_refs / olean_meta output (an .olean reader, run with
OLEAN_REFS_RANGES=1 [OLEAN_REFS_HASH=1] over every project .olean, inside the read-only sandbox) and writes a compact
index for the planner:
  mods   : module -> (imports list)
  consts : module -> list of (const name, kind char)
  ranges : module -> list of (const name, line, col, endLine, endCol)      (declRangeExt, 1-based lines, 0-based cols)
  live   : set of project constant names in the constant closure of the targets (type + value + inductive/ctor/rec
           links, exactly olean_refs' 'uses' relation, i.e. the same relation lean4export follows)
  ext_live : number of non-project (Mathlib/core) constants reached
  nss    : module -> namespaces registered by the module (namespacesExt entries)
  hashes : const -> (type hash, value hash) (Expr.hash, if olean_refs ran with OLEAN_REFS_HASH=1)
The closure is computed over the CONSTANT graph only; it decides which declarations the kernel export of the targets
contains (lean4export exports exactly this closure), so it is the exact 'dead code' set at the kernel level.
"""
import sys, pickle, collections, time

def main():
    args = sys.argv[1:]
    targets = ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
               "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]
    if '--targets' in args:
        i = args.index('--targets'); targets = args[i + 1].split(','); del args[i:i + 2]
    live_export = None
    if '--live-from-export' in args:
        i = args.index('--live-from-export'); live_export = args[i + 1]; del args[i:i + 2]
    ilean_root = None
    if '--ilean-root' in args:
        i = args.index('--ilean-root'); ilean_root = args[i + 1]; del args[i:i + 2]
    out, files = args[0], args[1:]
    t0 = time.time()
    ids = {}; names = []
    def iid(s):
        i = ids.get(s)
        if i is None:
            i = len(names); ids[s] = i; names.append(s)
        return i
    owner = {}; uses = {}
    mods = {}; consts = collections.defaultdict(list); ranges = collections.defaultdict(list)
    hashes = {}; nss = {}
    for f in files:
        with open(f, encoding='utf-8', errors='replace') as fh:
            for line in fh:
                p = line.rstrip('\n').split('\t')
                t = p[0]
                if t == 'C':
                    c = iid(p[3]); owner[c] = p[1]
                    consts[p[1]].append((p[3], p[2]))
                    uses[c] = [iid(u) for u in p[4].split(' ')] if len(p) > 4 and p[4] else []
                elif t == 'M':
                    mods[p[1]] = p[3].split(' ') if len(p) > 3 and p[3] else []
                elif t == 'R':
                    ranges[p[1]].append((p[2], int(p[3]), int(p[4]), int(p[5]), int(p[6])))
                elif t == 'N':
                    nss[p[1]] = p[2].split(' ') if len(p) > 2 and p[2] else []
                elif t == 'H':
                    hashes[p[2]] = (int(p[3]), int(p[4]))
        print(f, 'consts', len(owner), round(time.time() - t0, 1), file=sys.stderr, flush=True)
    if ilean_root:
        # module-system files (`module` header) keep declRangeExt in the .olean.server part, which olean_refs does not
        # read: take the full declaration ranges from the .ilean 'decls' map instead (0-based LSP lines -> 1-based)
        import json, os
        n_il = 0
        for m in list(mods):
            if ranges.get(m): continue
            p = os.path.join(ilean_root, *m.split('.')) + '.ilean'
            if not os.path.exists(p): continue
            try:
                d = json.load(open(p, encoding='utf-8'))
            except Exception:
                continue
            for nm, r in (d.get('decls') or {}).items():
                if isinstance(r, list) and len(r) >= 4:
                    ranges[m].append((nm, r[0] + 1, r[1], r[2] + 1, r[3])); n_il += 1
        print('ranges from .ilean files:', n_il, file=sys.stderr, flush=True)
    seen = set(); st = [ids[t] for t in targets if t in ids]
    missing = [t for t in targets if t not in ids]
    while st:
        c = st.pop()
        if c in seen: continue
        seen.add(c)
        u = uses.get(c)
        if u: st.extend(u)
    live = set(names[c] for c in seen if c in owner)
    if live_export:
        # liveness from the solution export itself (= the closure of the targets, as lean4export wrote it): needed when
        # olean_refs cannot see every constant (module-system .olean.private parts); declarations that only the .ilean
        # ranges know are added as constants of their module
        import json
        nm = {0: ''}; exp_names = set()
        def collect(o):
            if isinstance(o, dict):
                for k2, v in o.items():
                    if k2 == 'name' and isinstance(v, int): exp_names.add(v)
                    elif k2 in ('ctors', 'all') and isinstance(v, list):
                        for x in v:
                            if isinstance(x, int): exp_names.add(x)
                            else: collect(x)
                    else: collect(v)
            elif isinstance(o, list):
                for x in o: collect(x)
        with open(live_export, encoding='utf-8') as fh:
            for line in fh:
                if line.startswith('{"in"'):
                    d = json.loads(line); i = d['in']
                    if 'str' in d: p = nm.get(d['str']['pre'], ''); nm[i] = (p + '.' if p else '') + d['str']['str']
                    elif 'num' in d: p = nm.get(d['num']['pre'], ''); nm[i] = (p + '.' if p else '') + str(d['num']['i'])
                elif line.startswith('{"il"') or line.startswith('{"ie"') or line.startswith('{"meta"'):
                    continue
                else:
                    collect(json.loads(line))
        en = set(nm.get(i, '') for i in exp_names)
        known = set(owner_names for owner_names in (names[c] for c in owner))
        added = 0
        for m, rl in ranges.items():
            for (rn, *_r) in rl:
                if rn not in known:
                    consts[m].append((rn, '?')); known.add(rn); added += 1
        live = set(n for n in known if n in en)
        print('live from export:', len(en), 'export names;', len(live), 'live project consts;', added,
              'constants added from ranges', file=sys.stderr, flush=True)
    ext = sum(1 for c in seen if c not in owner)
    print('modules', len(mods), 'project consts', len(owner), 'live project consts', len(live), 'ext live', ext,
          'missing targets', missing, file=sys.stderr, flush=True)
    with open(out, 'wb') as o:
        pickle.dump({'mods': mods, 'consts': dict(consts), 'ranges': dict(ranges), 'live': live, 'ext_live': ext,
                     'targets': targets, 'hashes': hashes, 'nss': nss}, o, protocol=4)

if __name__ == '__main__':
    main()

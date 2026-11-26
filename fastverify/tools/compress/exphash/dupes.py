#!/usr/bin/env python3
"""dupes.py DECLS_TSV [--modules ALLCONSTS_TSV] [--out DIR] [--top N]

Duplicate classes of an export analysed by exphash (decls.tsv):
  * same-statement theorems: rows of kind thm with equal (type_hk, level-parameter names) -> any member can replace any
    other at the kernel level (proof irrelevance); classes with >= 2 members are sharing candidates;
  * exact duplicates: equal statement AND equal value hash (thm/def);
  * definitions with equal type and value (copies of the same definition under different names).
Each class is split by provenance: auto-generated names (equation lemmas, congr lemmas, match/proof aux, instances'
auto names) vs hand-written names, and same-module vs cross-module (module map = allconsts.tsv: name, module, kind).
Writes DIR/thm_classes.tsv (one row per class), DIR/def_classes.tsv and DIR/dupes.json (summary)."""
import sys, os, re, json, argparse, collections

AUTO = re.compile(r'(\.eq_\d+$|\.eq_def$|\.eq_unfold$|\.congr_simp$|\._proof_\d+$|\.proof_\d+$|\.match_\d+|\._sunfold$|'
                  r'\._unary|\.induct$|\.mutual_induct$|_sparseCasesOn|\._simp_\d+|\.injEq$|\.inj$|\.sizeOf_spec$|'
                  r'\._auxLemma\.\d+$|\._closed_\d+|\.ext_iff$|\.ext$|_private\..*\.0\.|^_private\.)')
def is_auto(n):
    return bool(AUTO.search(n))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('decls')
    ap.add_argument('--modules')
    ap.add_argument('--out', default='.')
    ap.add_argument('--top', type=int, default=40)
    a = ap.parse_args()
    mod = {}
    if a.modules:
        with open(a.modules) as f:
            for line in f:
                p = line.rstrip('\n').split('\t')
                if len(p) >= 2:
                    mod[p[0]] = p[1]
    os.makedirs(a.out, exist_ok=True)
    thm = collections.defaultdict(list)
    exact = collections.defaultdict(list)
    defs = collections.defaultdict(list)
    n = collections.Counter()
    with open(a.decls) as f:
        hdr = f.readline().rstrip('\n').split('\t')
        ix = {k: i for i, k in enumerate(hdr)}
        for line in f:
            p = line.rstrip('\n').split('\t')
            k = p[ix['kind']]
            n[k] += 1
            name = p[ix['name']]
            proj = (name in mod) if mod else True
            rec = (name, int(p[ix['new_nodes']]), int(p[ix['new_bytes']]), int(p[ix['value_tsize']]), proj)
            if k == 'thm':
                key = (p[ix['type_hk']], p[ix['lvl_h']])
                thm[key].append(rec)
                exact[key + (p[ix['value_hk']],)].append(rec)
            elif k == 'def':
                defs[(p[ix['type_hk']], p[ix['lvl_h']], p[ix['value_hk']], p[ix['extra']])].append(rec)
    S = {'kinds': dict(n)}
    def summarize(classes, label):
        cls = [v for v in classes.values() if len(v) >= 2]
        tot = {'classes': len(cls), 'members': sum(len(v) for v in cls), 'redundant': sum(len(v) - 1 for v in cls)}
        # redundant cost = all members but the smallest (keep the cheapest proof)
        rn = rb = 0
        cat = collections.Counter()
        catred = collections.Counter()
        xmod = collections.Counter()
        for v in cls:
            v2 = sorted(v, key=lambda r: r[2])
            rn += sum(r[1] for r in v2[1:]); rb += sum(r[2] for r in v2[1:])
            na = sum(1 for r in v if is_auto(r[0]))
            c = 'all-auto' if na == len(v) else ('all-hand' if na == 0 else 'mixed')
            np_ = sum(1 for r in v if r[4])
            c += '/project' if np_ == len(v) else ('/library' if np_ == 0 else '/lib+project')
            cat[c] += 1; catred[c] += len(v) - 1
            if mod:
                ms = set(mod.get(r[0], '?') for r in v)
                xmod['same-module' if len(ms) == 1 else 'cross-module'] += 1
        tot.update({'redundant_new_nodes': rn, 'redundant_new_bytes': rb, 'categories': dict(cat),
                    'categories_redundant': dict(catred), 'module_spread': dict(xmod)})
        S[label] = tot
        return cls
    tc = summarize(thm, 'same_statement_thms')
    summarize(exact, 'exact_dup_thms')
    dc = summarize(defs, 'same_type_value_defs')
    with open(os.path.join(a.out, 'thm_classes.tsv'), 'w') as f:
        f.write('size\tauto\tproject\tmodules\tredundant_bytes\tmembers\n')
        for v in sorted(tc, key=lambda v: -sum(r[2] for r in v)):
            v2 = sorted(v, key=lambda r: r[2])
            ms = sorted(set(mod.get(r[0], '?') for r in v)) if mod else []
            f.write('%d\t%d\t%d\t%d\t%d\t%s\n' % (len(v), sum(is_auto(r[0]) for r in v), sum(r[4] for r in v), len(ms),
                    sum(r[2] for r in v2[1:]), ' '.join('%s:%d' % (r[0], r[2]) for r in v2)))
    with open(os.path.join(a.out, 'def_classes.tsv'), 'w') as f:
        f.write('size\tauto\tproject\tmembers\n')
        for v in sorted(dc, key=lambda v: -len(v)):
            f.write('%d\t%d\t%d\t%s\n' % (len(v), sum(is_auto(r[0]) for r in v), sum(r[4] for r in v), ' '.join(r[0] for r in v)))
    json.dump(S, open(os.path.join(a.out, 'dupes.json'), 'w'), indent=1)
    print(json.dumps(S, indent=1))

if __name__ == '__main__':
    main()

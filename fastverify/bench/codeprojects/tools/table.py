#!/usr/bin/env python3
"""table.py COLLECT.tsv [TAGPREFIX] : markdown table of the catalogue from bench/bigprojects/tools/collect.py rows.
Run names NAME-PRESET[-TAG]; rows grouped by project and configuration (reference / sound / sound-code / fast-exact /
sound-b0), median over repeats; 'fair' total = total - challenge build (the publisher's one-time cost); speed-up vs the
median official reference of the same project."""
import csv, statistics, sys, collections
rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
pref = sys.argv[2] if len(sys.argv) > 2 else ''
def f(x):
    try: return float(x)
    except (TypeError, ValueError): return None
groups = collections.defaultdict(list)
for r in rows:
    run = r['run']
    for pr in ('reference', 'sound', 'fast-exact'):
        k = '-' + pr
        if k in run:
            proj, tag = run.split(k, 1); tag = tag.lstrip('-')
            break
    else:
        continue
    if pref and not tag.startswith(pref): continue
    cfg = pr if pr != 'sound' else ('sound-code' if 'code' in tag else 'sound-b0' if 'b0' in tag else 'sound')
    tot = f(r['total']); ch = f(r.get('challenge')) or 0.0
    groups[(proj, cfg)].append(dict(verdict=r['verdict'], total=(tot - ch) if tot is not None else None,
                                    build=f(r['build']), export=f(r['export']), check=f(r['check']), opts=r['build_opts']))
def med(v):
    v = [x for x in v if x is not None]
    return statistics.median(v) if v else None
projs = sorted(set(p for p, _ in groups))
print('| project | config | runs | verdict | build | export | check | total (fair) | speed-up vs official |')
print('|---|---|---|---|---|---|---|---|---|')
for p in projs:
    ref = med([g['total'] for g in groups.get((p, 'reference'), [])])
    for cfg in ('reference', 'sound', 'sound-code', 'fast-exact', 'sound-b0'):
        g = groups.get((p, cfg))
        if not g: continue
        v = '/'.join(sorted(set(x['verdict'] for x in g)))
        t = med([x['total'] for x in g])
        su = f'{ref / t:.2f}x' if ref and t else ''
        fmt = lambda x: '' if x is None else f'{x:.1f}'
        print(f"| {p} | {cfg} | {len(g)} | {v} | {fmt(med([x['build'] for x in g]))} | {fmt(med([x['export'] for x in g]))} | "
              f"{fmt(med([x['check'] for x in g]))} | {fmt(t)} | {su} |")

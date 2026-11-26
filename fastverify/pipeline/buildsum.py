#!/usr/bin/env python3
"""O01: post-build summary from <log_dir> (modules.jsonl, graph.tsv[, tools.jsonl]): span, CPU, critical chain (walls
along the latest-finishing dependency path, with waiting gaps), concurrency profile. Runs in parallel with the export."""
import collections, json, sys
L = sys.argv[1]
recs = {}
for l in open(f'{L}/modules.jsonl'):
    r = json.loads(l)
    if r.get('retry_plain'): continue
    recs[r['module']] = r
deps = collections.defaultdict(list)
for l in open(f'{L}/graph.tsv'):
    a, b = l.split(); deps[a].append(b)
T0 = min(r['t0'] for r in recs.values()); T1 = max(r['t1'] for r in recs.values())
fin = lambda r: r.get('t_release', r['t1'])
cpu = 0.0
try:
    for l in open(f'{L}/tools.jsonl'):
        t = json.loads(l); cpu += t['utime'] + t['stime']
except OSError: pass
rel = [r['t1'] - r['t_release'] for r in recs.values() if 't_release' in r]
print(f'BUILDSUM span {T1 - T0:.1f} s units {len(recs)} cpu {cpu:.0f} s native {sum(1 for r in recs.values() if r.get("native"))} '
      f'early-released {len(rel)} (mean {sum(rel) / max(1, len(rel)):.2f} s before exit)')
end = max(recs, key=lambda m: fin(recs[m])); m = end; chain = []
while m:
    r = recs[m]; ds = [d for d in deps[m] if d in recs]
    p = max(ds, key=lambda d: fin(recs[d])) if ds else None
    gap = r['t0'] - (fin(recs[p]) if p else T0)
    chain.append((m, r['t0'] - T0, fin(r) - r['t0'], gap)); m = p
chain.reverse()
print(f'BUILDSUM chain {len(chain)} links, sum wall {sum(c[2] for c in chain):.1f} s, sum gaps {sum(c[3] for c in chain):.1f} s')
for m, t0, w, g in chain:
    if w >= 8 or g >= 2: print(f'  {t0:7.1f} +{w:6.1f} gap {g:5.1f}  {m}')
bins = collections.Counter()
for r in recs.values():
    a, b = r['t0'] - T0, r['t1'] - T0
    for k in range(int(a // 25), int(b // 25) + 1): bins[k] += max(0.0, min(b, (k + 1) * 25) - max(a, k * 25))
print('BUILDSUM running/25s: ' + ' '.join(f'{k * 25}:{bins[k] / 25:.0f}' for k in sorted(bins)))

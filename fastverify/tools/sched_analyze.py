#!/usr/bin/python3 -I
"""tools/sched_analyze.py SCHED_OUT [GRAPH_TSV] [REF_SCHED_OUT] [CLOSURE_K_JSON]
Per-run build analysis: makespan, sum of walls/cpu, work bound at J jobs, measured utilization per minute (needs 'start'),
critical path by walls (crit), tail profile, and (with REF) per-module wall ratio run/ref binned by closure size k (CLOSURE_K_JSON = {module: k})."""
import collections, json, sys
sf = sys.argv[1]; gf = sys.argv[2] if len(sys.argv) > 2 else None
r1f = sys.argv[3] if len(sys.argv) > 3 else None; kf = sys.argv[4] if len(sys.argv) > 4 else None
recs = []; start = None; J = 384
for l in open(sf):
    try: r = json.loads(l)
    except ValueError: continue
    if r.get('event') == 'start': start = r; J = r.get('jobs', J)
    if r.get('event') == 'module' and 'wall' in r: recs.append(r)
W = sum(r['wall'] for r in recs); C = sum(r.get('cpu', 0) or 0 for r in recs)
ends = [r['start'] + r['wall'] for r in recs if 'start' in r]
mk = max(ends) if ends else None
print(f"modules {len(recs)} jobs {J} sum wall {W:.0f} s, sum cpu {C:.0f} s, work bound {W / J:.0f} s, makespan {mk}")
if ends:
    T = int(mk) + 1; busy = [0.0] * (T // 60 + 1)
    for r in recs:
        s = r['start']; e = s + r['wall']; t = s
        while t < e:
            b = int(t // 60); nt = min(e, (b + 1) * 60); busy[b] += nt - t; t = nt
    print('utilization (avg busy slots per minute):')
    print('  ' + ' '.join(f'{b / 60:.0f}' for b in busy))
    idle = sum(max(0, J * 60 - b) for b in busy[:-1])
    print(f'  idle slot-seconds before the last minute: {idle:.0f} ({idle / J:.0f} s of makespan equivalent)')
if gf:
    walls = {r['module']: r['wall'] for r in recs}
    deps = collections.defaultdict(list)
    for l in open(gf):
        x = l.rstrip('\n').split('\t')
        if len(x) >= 2 and x[0] in walls and x[1] in walls: deps[x[0]].append(x[1])
    rdeps = collections.defaultdict(list); indeg = {m: 0 for m in walls}
    for m, ds in deps.items():
        for d in ds: rdeps[d].append(m); indeg[m] += 1
    q = [m for m in walls if indeg[m] == 0]; order = []
    while q:
        m = q.pop(); order.append(m)
        for x in rdeps[m]:
            indeg[x] -= 1
            if indeg[x] == 0: q.append(x)
    fin = {}; pred = {}
    for m in order:
        b = 0.0; bp = None
        for d in deps[m]:
            if fin[d] > b: b = fin[d]; bp = d
        fin[m] = b + walls[m]; pred[m] = bp
    end = max(fin, key=fin.get); ch = []; m = end
    while m: ch.append(m); m = pred[m]
    ch.reverse()
    big = sorted(ch, key=lambda m: -walls[m])[:8]
    print(f'critical path (walls) {fin[end]:.0f} s over {len(ch)} modules; heaviest on it: ' + ', '.join(f'{m.split(".")[-1]} {walls[m]:.0f}' for m in big))
if r1f:
    w1 = {}
    for l in open(r1f):
        try: r = json.loads(l)
        except ValueError: continue
        if r.get('event') == 'module': w1[r['module']] = r['wall']
    k = json.load(open(kf)) if kf else {}
    bins = collections.defaultdict(lambda: [0.0, 0.0, 0])
    for r in recs:
        m = r['module']
        if m not in w1: continue
        kk = k.get(m, 0); b = 0 if kk < 1000 else 1 if kk < 5000 else 2 if kk < 20000 else 3 if kk < 80000 else 4
        bins[b][0] += r['wall']; bins[b][1] += w1[m]; bins[b][2] += 1
    names = ['k<1k', '1k-5k', '5k-20k', '20k-80k', '>=80k']
    print('wall ratio vs run 1 by closure size: ' + '; '.join(f'{names[b]}: {v[0] / v[1]:.2f} (n={v[2]})' for b, v in sorted(bins.items())))

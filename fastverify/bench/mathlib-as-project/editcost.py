#!/usr/bin/env python3
"""editcost.py MATHLIB_SRC (--sched SCHED_OUT | --lakelog BUILD_LOG) [--threads T ...] : model of the re-verification cost
after editing ONE module of a library built from source. For every module m: the rebuild set = m + its transitive
importers inside the library; work W(m) = sum of the measured walls over that set; CP(m) = longest import chain from m
through the set (measured walls). Estimated rebuild time with T threads = max(CP(m), W(m)/T). Prints percentiles over all
modules (uniformly random edit) and over modules weighted by size. Import graph from the sources (direct imports)."""
import json, os, re, sys, statistics
src = sys.argv[1]; args = sys.argv[2:]
pat = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»\']+)')
def imports(path):
    res = []; inc = 0
    for ln in open(path, encoding='utf-8'):
        s = ln.strip()
        if inc:
            if '-/' in s: inc = 0
            continue
        if s.startswith('/-'):
            if '-/' not in s[2:]: inc = 1
            continue
        if not s or s.startswith('--') or s.startswith('module') or s.startswith('prelude'): continue
        m = pat.match(ln)
        if m: res.append(m.group(1)); continue
        break
    return res
mods = {}
for dp, dns, fns in os.walk(os.path.join(src, 'Mathlib')):
    for fn in fns:
        if fn.endswith('.lean'):
            p = os.path.join(dp, fn); name = os.path.relpath(p, src)[:-5].replace('/', '.')
            mods[name] = [x for x in imports(p) if x.startswith('Mathlib.')]
wall = {}
if '--sched' in args:
    for ln in open(args[args.index('--sched') + 1]):
        try: r = json.loads(ln)
        except Exception: continue
        if r.get('event') == 'module': wall[r['module']] = r['wall']
if '--lakelog' in args:
    def secs(t):
        s = 0.0
        for v, u in re.findall(r'([\d.]+)(ms|s|m|h)', t): s += float(v) * {'ms': 0.001, 's': 1, 'm': 60, 'h': 3600}[u]
        return s
    for ln in open(args[args.index('--lakelog') + 1], errors='replace'):
        m = re.search(r'Built (\S+) \(([^)]*)\)\s*$', ln)
        if m: wall[m.group(1)] = secs(m.group(2))
threads = [int(args[i + 1]) for i, a in enumerate(args) if a == '--threads'] or [64, 384]
mods = {m: [d for d in ds if d in mods] for m, ds in mods.items() if m in wall}
rdeps = {m: [] for m in mods}
for m, ds in mods.items():
    for d in ds:
        if d in rdeps: rdeps[d].append(m)
# topological order (dependencies first)
order = []; seen = set()
for m0 in mods:
    st = [(m0, 0)]
    while st:
        x, i = st.pop()
        if i == 0:
            if x in seen: continue
            seen.add(x)
        ds = mods[x]
        if i < len(ds):
            st.append((x, i + 1))
            if ds[i] not in seen: st.append((ds[i], 0))
        else: order.append(x)
# CP(m) = wall(m) + max CP over importers (longest chain upward); W(m) via bitsets of transitive importers
cp = {}
for m in reversed(order):
    cp[m] = wall[m] + max((cp[r] for r in rdeps[m]), default=0.0)
idx = {m: i for i, m in enumerate(order)}
reach = {}
for m in reversed(order):
    b = 1 << idx[m]
    for r in rdeps[m]: b |= reach[r]
    reach[m] = b
W = {}
wl = [wall[m] for m in order]
for m in order:
    b = reach[m]; s = 0.0; i = 0
    while b:
        low = b & -b; j = low.bit_length() - 1; s += wl[j]; b ^= low
    W[m] = s
n = len(order)
def pct(xs, q): xs = sorted(xs); return xs[min(len(xs) - 1, int(q * len(xs)))]
out = {"modules": n, "total_work_s": round(sum(wl), 1), "rebuild_set_size": {q: pct([bin(reach[m]).count('1') for m in order], q) for q in (0.5, 0.9, 0.99)}}
for T in threads:
    est = [max(cp[m], W[m] / T) for m in order]
    out[f"T{T}"] = {"median_s": round(pct(est, 0.5), 1), "p90_s": round(pct(est, 0.9), 1), "p99_s": round(pct(est, 0.99), 1),
                    "max_s": round(max(est), 1), "share_cp_bound": round(sum(1 for m in order if cp[m] >= W[m] / T) / n, 3)}
print(json.dumps(out))

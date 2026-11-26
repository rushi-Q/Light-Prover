#!/usr/bin/env python3
"""Fixed ibuild.py (fix for Lean 4 LEAN_PATH package-root shadowing):
Lean 4 resolves `import Foo.Bar` using the FIRST LEAN_PATH directory containing top-level dir `Foo/`.
Putting an empty OUT_LIB before BASE_LAKE/build/lib/lean caused creating OUT_LIB/Foo/... to shadow
the ENTIRE `Foo` package in BASE_LAKE! Fix: pre-populate OUT_LIB as a symlink mirror of
BASE_LAKE/build/lib/lean (and unlink/restore the target .olean/.ilean around each module build),
then pass OUT_LIB (not BASE_LAKE/build/lib/lean) + BASE_LAKE/packages/* in LEAN_PATH.
"""
import sys, os, json, time, subprocess, argparse, collections, threading, heapq

ap = argparse.ArgumentParser()
ap.add_argument('src'); ap.add_argument('modlist'); ap.add_argument('imports'); ap.add_argument('base_lake')
ap.add_argument('out_lib'); ap.add_argument('jobs', type=int)
ap.add_argument('--lean', default=os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'))
ap.add_argument('--extra', action='append', default=[])
ap.add_argument('--timeout', type=int, default=3600)
ap.add_argument('--costs', default=None)
a = ap.parse_args()

mods = [m for m in open(a.modlist).read().split() if m]
mset = set(mods)
imp = json.load(open(a.imports))
# Transitive dependencies restricted to mset (prevents edited dependents racing edited ancestors across unedited hops!)
trans_cache = {}
def reach_in_mset(u):
    if u in trans_cache: return trans_cache[u]
    seen = set(); found = set(); st = list(imp.get(u, {}).get('imports', []))
    while st:
        v = st.pop()
        if v in seen: continue
        seen.add(v)
        if v in mset and v != u:
            found.add(v)
        elif v in imp:
            st.extend(imp[v].get('imports', []))
    trans_cache[u] = sorted(found)
    return trans_cache[u]
deps = {m: reach_in_mset(m) for m in mods}
rdeps = collections.defaultdict(list)
for m, ds in deps.items():
    for d in ds:
        rdeps[d].append(m)
cost = {}
if a.costs:
    import gzip
    cost = json.load(gzip.open(a.costs))
prio = {}
order = []; seen = set()
for m0 in mods:
    if m0 in seen: continue
    st = [(m0, iter(rdeps[m0]))]; seen.add(m0)
    while st:
        m, it = st[-1]; nxt = None
        for d in it:
            if d not in seen: nxt = d; break
        if nxt is None: st.pop(); order.append(m)
        else: seen.add(nxt); st.append((nxt, iter(rdeps[nxt])))
for m in order:
    prio[m] = cost.get(m, 5.0) + max((prio[r] for r in rdeps[m]), default=0.0)

base = os.path.abspath(a.base_lake)
base_lib = os.path.join(base, 'build/lib/lean')
out_lib = os.path.abspath(a.out_lib)
# Ensure out_lib is symlink-populated if empty (caller may pre-populate via cp -rs)
if not os.path.exists(out_lib) or not os.listdir(out_lib):
    os.makedirs(out_lib, exist_ok=True)
    for dp, dns, fns in os.walk(base_lib):
        rel = os.path.relpath(dp, base_lib)
        dst_d = out_lib if rel == '.' else os.path.join(out_lib, rel)
        os.makedirs(dst_d, exist_ok=True)
        for fn in fns:
            if fn.endswith(('.olean', '.ilean')):
                dst_f = os.path.join(dst_d, fn)
                if not os.path.lexists(dst_f):
                    os.symlink(os.path.join(dp, fn), dst_f)

lp = [out_lib]
pk = os.path.join(base, 'packages')
if os.path.isdir(pk):
    for p in sorted(os.listdir(pk)):
        d = os.path.join(pk, p, '.lake/build/lib/lean')
        if os.path.isdir(d):
            lp.append(d)
env = dict(os.environ, LEAN_PATH=':'.join(lp))
RHOPTS = ['--tstack=400000', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3',
          '-Dpp.unicode.fun=true', '-DmaxHeartbeats=4000000', '-Dlinter.all=false']
pending = {m: len(deps[m]) for m in mods}
ready = [(-prio[m], m) for m in mods if pending[m] == 0]
heapq.heapify(ready)
lock = threading.Condition()
res = {}; T0 = time.time(); running = 0; done = 0
logd = os.path.join(os.path.dirname(out_lib), 'ibuild-logs')
os.makedirs(logd, exist_ok=True)

def build(m):
    rel = m.replace('.', '/')
    o = os.path.join(out_lib, rel + '.olean'); i = os.path.join(out_lib, rel + '.ilean')
    otmp = o + '.tmp'; itmp = i + '.tmp'
    os.makedirs(os.path.dirname(o), exist_ok=True)
    x = []
    if m.startswith(('GroundTheory.LocalFields.', 'GroundTheory.GlobalFields.')):
        x = ['-DsynthInstance.maxHeartbeats=400000']
    cmd = [a.lean] + RHOPTS + x + a.extra + ['-R', a.src, '-o', otmp, '-i', itmp, os.path.join(a.src, rel + '.lean')]
    t0 = time.time()
    with open(os.path.join(logd, m + '.log'), 'w') as lf:
        try:
            rc = subprocess.run(cmd, env=env, stdout=lf, stderr=subprocess.STDOUT, timeout=a.timeout).returncode
        except subprocess.TimeoutExpired:
            rc = 124
    if rc == 0 and os.path.exists(otmp):
        os.replace(otmp, o)
        if os.path.exists(itmp):
            os.replace(itmp, i)
    else:
        for f in (otmp, itmp):
            try: os.unlink(f)
            except OSError: pass
    return rc, time.time() - t0, t0 - T0

def worker():
    global running, done
    while True:
        with lock:
            while not ready and done + running < len(mods):
                lock.wait()
            if not ready:
                lock.notify_all(); return
            _, m = heapq.heappop(ready); running += 1
        rc, dt, st = build(m)
        with lock:
            res[m] = (rc, dt, st); running -= 1; done += 1
            for r in rdeps[m]:
                pending[r] -= 1
                if pending[r] == 0:
                    heapq.heappush(ready, (-prio[r], r))
            if done % 200 == 0 or done == len(mods):
                print(json.dumps({'done': done, 'of': len(mods), 'failed': sum(1 for v in res.values() if v[0]),
                                  'elapsed': round(time.time() - T0)}), flush=True)
            lock.notify_all()

ths = [threading.Thread(target=worker) for _ in range(a.jobs)]
for t in ths: t.start()
for t in ths: t.join()
with open(os.path.join(os.path.dirname(out_lib), 'ibuild.tsv'), 'w') as fh:
    for m in mods:
        rc, dt, st = res.get(m, (-1, 0, 0))
        fh.write(f'{m}\t{rc}\t{dt:.1f}\t{st:.1f}\n')
fails = [m for m in mods if res.get(m, (-1,))[0] != 0]
print(json.dumps({'modules': len(mods), 'failed': len(fails), 'wall_s': round(time.time() - T0),
                  'sum_module_s': round(sum(v[1] for v in res.values())), 'first_failures': fails[:20]}), flush=True)

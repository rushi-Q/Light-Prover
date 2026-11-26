# fakebuild.py PROJ_SRC MODS LP LOGDIR DURATION : emulate build-fast's plan.jsonl + sched.out for an already built tree
import sys, os, json, re, time, collections
src, modsf, lpf, logd, dur = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], float(sys.argv[5])
mods = [l.strip() for l in open(modsf) if l.strip()]
for extra in ('Main', 'Statements'):
    if os.path.exists(os.path.join(src, extra + '.lean')) and extra not in mods: mods.append(extra)
ms = set(mods); deps = {}
for m in mods:
    ds = []
    for ln in open(os.path.join(src, m.replace('.', '/') + '.lean'), errors='replace'):
        mm = re.match(r'\s*import\s+(\S+)', ln)
        if mm and mm.group(1) in ms: ds.append(mm.group(1))
        elif ln.strip() and not ln.startswith('import') and not ln.startswith('module') and not ln.startswith('--'): break
    deps[m] = ds
os.makedirs(logd, exist_ok=True)
with open(os.path.join(logd, 'plan.jsonl.part'), 'w') as f:
    f.write(json.dumps({'leanPath': open(lpf).read().strip(), 'nmods': len(mods)}) + '\n')
    for m in mods: f.write(json.dumps({'name': m, 'deps': deps[m], 'src': os.path.join(src, m.replace('.', '/') + '.lean')}) + '\n')
os.rename(os.path.join(logd, 'plan.jsonl.part'), os.path.join(logd, 'plan.jsonl'))
# topological order (Kahn, deterministic)
rd = collections.defaultdict(list); nd = {m: len(deps[m]) for m in mods}
for m in mods:
    for d in deps[m]: rd[d].append(m)
q = collections.deque(sorted(m for m in mods if nd[m] == 0)); order = []
while q:
    m = q.popleft(); order.append(m)
    for i in rd[m]:
        nd[i] -= 1
        if nd[i] == 0: q.append(i)
assert len(order) == len(mods), (len(order), len(mods))
t0 = time.time(); so = open(os.path.join(logd, 'sched.out'), 'w', buffering=1)
so.write(json.dumps({'event': 'start', 'mods': len(mods)}) + '\n')
for k, m in enumerate(order):
    target = t0 + dur * (k + 1) / len(order)
    w = target - time.time()
    if w > 0: time.sleep(w)
    so.write(json.dumps({'event': 'module', 'module': m, 'rc': 0, 'error_msg': False, 'missing': [], 'wall': 1.0, 'start': 0}) + '\n')
so.write(json.dumps({'event': 'summary'}) + '\n')
print(f'fake build done: {len(order)} modules in {time.time() - t0:.0f} s')

import json, os, re, sys, subprocess
V = os.environ.get("FV_SCRATCH") or sys.exit("FV_SCRATCH: node-local work root of the incremental benchmarks (required, see README.md)")
plan = f'{V}/mlbase/log/build-fast/plan.jsonl'
recs = [json.loads(l) for l in open(plan)][1:]
mods = {r['name']: r for r in recs if 'name' in r}
dep = {m: [] for m in mods}
for m, r in mods.items():
    for d in r['deps']: dep[d].append(m)
def nd(m):
    s = {m}; st = [m]
    while st:
        for d in dep[st.pop()]:
            if d not in s: s.add(d); st.append(d)
    return len(s) - 1
names = set()
subprocess.run(['python3', '-I', os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(__file__))), 'export-names.py'),
                os.path.realpath(f'{V}/mlbase/solution.export'), 'thm'], stdout=open(f'{V}/ml-names.tsv', 'w'))
for l in open(f'{V}/ml-names.tsv'):
    names.add(l.rstrip('\n').split('\t')[1])
src = f'{V}/ml/proj/qr'
pat = re.compile(r'^(theorem|lemma)\s+([^\s:({\[]+)', re.M)
out = []
for m, r in mods.items():
    if not m.startswith('Mathlib.'): continue
    f = r['src']
    try: t = open(f, encoding='utf-8').read()
    except OSError: continue
    # namespace-agnostic: last component match + require the full name to end with it and appear in export
    for mm in pat.finditer(t):
        last = mm.group(2).split('.')[-1]
        if not re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", last): continue
        # check a := by follows within 6 lines
        seg = t[mm.end(): mm.end() + 600]
        if ':= by\n' not in seg: continue
        cand = [n for n in names if n.endswith('.' + last) or n == last]
        if len(cand) == 1:
            out.append((m, last, cand[0])); break
res = []
for m, last, full in out:
    res.append((nd(m), m, last, full))
res.sort()
print(len(mods), 'modules;', len(res), 'candidates')
for lo, hi in [(0, 1), (2, 10), (50, 200), (500, 1500), (1500, 3000)]:
    c = [x for x in res if lo <= x[0] <= hi]
    print(lo, hi, len(c))
    for x in c[:2] + c[len(c)//2:len(c)//2+1] + c[-1:]: print('   ', x)

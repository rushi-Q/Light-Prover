import json, os, sys
V = os.environ.get("FV_SCRATCH") or sys.exit("FV_SCRATCH: node-local work root of the incremental benchmarks (required, see README.md)")
L=open(f'{V}/rh-plan.jsonl'); L.readline()
mods={}
for l in L:
    r=json.loads(l)
    if 'name' in r: mods[r['name']]=r['deps']
wall={}
for l in open(f'{V}/rh-sched.out'):
    if l.startswith('{"event": "module"'):
        x=json.loads(l); wall[x['module']]=x['wall']
dep={m:[] for m in mods}
for m,ds in mods.items():
    for d in ds: dep[d].append(m)
indeg={m:len(ds) for m,ds in mods.items()}
q=[m for m in mods if indeg[m]==0]; i=0
while i<len(q):
    for d in dep[q[i]]:
        indeg[d]-=1
        if indeg[d]==0: q.append(d)
    i+=1
cp={}
for m in reversed(q):
    cp[m]=wall.get(m,0)+max((cp[d] for d in dep[m]),default=0)
def nd(m):
    s={m};st=[m]
    while st:
        for d in dep[st.pop()]:
            if d not in s: s.add(d);st.append(d)
    return s
cands=json.load(open('edit_cands.json'))
out=[]
for n,mod,last,full in cands:
    if not full.startswith(('GlobalTheory','GroundTheory','ReciprocityTheory','CompanionTheory','Formalism','Bl.','Development','Lemmata','CrystallineSemistableComparison')): continue
    if mod not in mods: continue
    s=nd(mod)
    out.append((len(s)-1, round(cp[mod],1), round(sum(wall.get(x,0) for x in s)), round(wall.get(mod,0),1), mod, last, full))
out.sort()
for lo,hi in [(1,10),(11,100),(101,1000),(1001,10000),(10001,200000)]:
    c=[x for x in out if lo<=x[0]<=hi]
    print(lo,hi,len(c))
    for x in c[:2]+c[len(c)//2:len(c)//2+2]: print('   ',x)
json.dump(out,open('rh_edit_cands.json','w'))
print('min cp over all modules', min(cp.values()), 'Main wall', wall.get('Main'))

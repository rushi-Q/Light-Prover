import json,sys
L=open(sys.argv[1])
head=json.loads(L.readline())
mods={}
for l in L:
    r=json.loads(l)
    if 'name' in r: mods[r['name']]={'deps':r['deps'],'src':r['src']}
wall={}
for l in open(sys.argv[2]):
    if l.startswith('{"event": "module"'):
        x=json.loads(l); wall[x['module']]=x['wall']
dep={m:[] for m in mods}
for m,r in mods.items():
    for d in r['deps']: dep[d].append(m)
indeg={m:len(r['deps']) for m,r in mods.items()}
q=[m for m in mods if indeg[m]==0]; i=0
while i<len(q):
    for d in dep[q[i]]:
        indeg[d]-=1
        if indeg[d]==0: q.append(d)
    i+=1
# number of descendants via bitsets is too big; compute counts with sets only for sample? use reverse topo with python ints as bitsets
idx={m:k for k,m in enumerate(q)}
desc={}
import random
# critical path of rebuilding descendants: longest wall path starting at m (m + its descendants)
cp={}
for m in reversed(q):
    cp[m]=wall.get(m,0)+max((cp[d] for d in dep[m]),default=0)
# count descendants approx via bitset for all (175k x 175k bits = too big). Instead sample modules in closure of Main
anc=set(); st=['Main'] if 'Main' in mods else []
roots=[m for m in mods if not dep[m]]
print('modules',len(mods),'roots(no importers)',len(roots), roots[:5])
target='Main' if 'Main' in mods else None
def ndesc(m):
    seen={m}; st=[m]
    while st:
        for d in dep[st.pop()]:
            if d not in seen: seen.add(d); st.append(d)
    return seen
random.seed(5)
sample=random.sample(list(mods),3000)
res=[]
for m in sample:
    s=ndesc(m)
    res.append((len(s)-1, round(cp[m],1), round(sum(wall.get(x,0) for x in s)), round(wall.get(m,0),1), m))
buckets=[(1,3),(4,20),(50,300),(1000,5000),(10000,40000),(60000,200000)]
for lo,hi in buckets:
    c=sorted([r for r in res if lo<=r[0]<=hi], key=lambda r:r[1])
    print(f'descendants {lo}-{hi}: {len(c)} sampled; examples (ndesc, rebuild critical path s, rebuild work s, own wall s, module):')
    for r in c[:2]+c[len(c)//2:len(c)//2+2]+c[-1:]: print('   ',r)
import statistics
print('median ndesc', statistics.median([r[0] for r in res]), 'mean', statistics.mean([r[0] for r in res]))
print('B1 critical path (whole)', round(max(cp.values()),1))

import json, os, re, sys, random, collections
V = os.environ.get("FV_SCRATCH") or sys.exit("FV_SCRATCH: node-local work root of the incremental benchmarks (required, see README.md)")
BI = os.environ.get("FV_BENCH_INPUTS") or sys.exit("FV_BENCH_INPUTS: benchmark inputs root holding rh-mid/ (required)")
names=[l.rstrip('\n').split('\t') for l in open(f'{V}/rhmid-ref-names.tsv')]
thms=[n for k,n in names if k=='thm']
mathlib_roots=set()
# RH-specific roots: first component of RH source top dirs / namespaces
rh=[n for n in thms if not n.startswith(('_private.Mathlib','Mathlib','_private.Init','_private.Lean','_private.Std','Lean.','Std.','Init.','Batteries','Aesop','Qq','ProofWidgets')) ]
print('theorems',len(thms),'non-core-looking',len(rh))
# index sources: last component -> files with 'theorem LAST' or 'lemma LAST'
src=f'{BI}/rh-mid/pristine/src'
decl=collections.defaultdict(list)
pat=re.compile(r'^\s*(?:private\s+|protected\s+|@\[[^\]]*\]\s*)*(theorem|lemma)\s+([^\s:({\[]+)',re.M)
for root,ds,fs in os.walk(src):
    for f in fs:
        if f.endswith('.lean'):
            p=os.path.join(root,f)
            t=open(p,encoding='utf-8',errors='replace').read()
            for m in pat.finditer(t):
                decl[m.group(2).split('.')[-1]].append(os.path.relpath(p,src))
print('source theorem names',len(decl))
# plan for descendants
L=open('rhmid-plan.jsonl').read().splitlines()
recs=[json.loads(l) for l in L[1:]]; recs=[r for r in recs if 'name' in r]
mods={r['name']:r for r in recs}
dep={m:[] for m in mods}
for m,r in mods.items():
    for d in r['deps']: dep[d].append(m)
def nd(m):
    s={m};st=[m]
    while st:
        for d in dep[st.pop()]:
            if d not in s: s.add(d);st.append(d)
    return len(s)-1
cands=[]
seen=set()
random.seed(1)
random.shuffle(rh)
for n in rh:
    last=n.split('.')[-1]
    if last in seen or not re.match(r'^[A-Za-z_][A-Za-z0-9_\']*$',last): continue
    seen.add(last)
    fs=set(decl.get(last,[]))
    if len(fs)!=1: continue
    f=list(fs)[0]; mod=f[:-5].replace('/','.')
    if mod not in mods: continue
    cands.append((nd(mod),mod,last,n))
    if len(cands)>=1500: break
cands.sort()
for lo,hi in [(0,0),(1,3),(4,20),(40,120),(300,800),(1500,4000)]:
    c=[x for x in cands if lo<=x[0]<=hi]
    print(lo,hi,len(c))
    for x in c[:3]: print('   ',x)
json.dump(cands,open('edit_cands.json','w'))

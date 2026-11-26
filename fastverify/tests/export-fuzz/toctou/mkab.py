#!/usr/bin/env python3
"""mkab.py BASE.export CONFIG OUTDIR : two exports A, B of IDENTICAL size that differ only in one target theorem's line:
A: the target keeps its official statement, its proof := its own statement (ill-typed, axiom-free): comparison and axiom
   check pass, every kernel rejects.
B: the target's statement := True, proof := True.intro (kernel-valid): the comparison rejects.
No single version of the file contains a valid proof of the target's statement. Prints the byte offset and both lines."""
import json, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from xfuzz import Ex, canon
from seams import find_decl, find_const_expr
base, cfg, out = sys.argv[1:4]
ex = Ex(open(base, 'rb').read()); c = json.load(open(cfg))
for t in c['theorem_names']:
    i = find_decl(ex, t, 'thm'); d = ex.get(i)['thm']
    if not d['levelParams']: break
tru = find_const_expr(ex, 'True'); intro = find_const_expr(ex, 'True.intro')
assert tru is not None and intro is not None, 'True / True.intro not in the export'
# fresh const expressions for True / True.intro right before the target line, identical in A and B
tn = ex.get(ex.exprs[tru])['const']['name']; inn = ex.get(ex.exprs[intro])['const']['name']
e1 = ex.max_expr() + 1; e2 = e1 + 1
pre = canon({'ie': e1, 'const': {'name': tn, 'us': []}}) + canon({'ie': e2, 'const': {'name': inn, 'us': []}})
tru, intro = e1, e2
da = dict(d); da['value'] = d['type']
db = dict(d); db['type'] = tru; db['value'] = intro
la = canon({'thm': da})[:-1]; lb = canon({'thm': db})[:-1]
n = max(len(la), len(lb))
la = la[:-2] + b' ' * (n - len(la)) + la[-2:]; lb = lb[:-2] + b' ' * (n - len(lb)) + lb[-2:]
assert len(la) == len(lb)
body = ex.out(delete={i})
off = len(body) + len(pre)   # the target line moves to the end of the file (nothing depends on a theorem)
os.makedirs(out, exist_ok=True)
open(os.path.join(out, 'A.ndjson'), 'wb').write(body + pre + la + b'\n')
open(os.path.join(out, 'B.ndjson'), 'wb').write(body + pre + lb + b'\n')
json.dump({'target': t, 'offset': off, 'A': la.decode(), 'B': lb.decode()}, open(os.path.join(out, 'ab.json'), 'w'))
print(t, off, la, lb)

#!/usr/bin/env python3
"""chainapp.py BASE.export N OUT [K=2]: OUT = BASE.export (an honest lean4export export) + a chain of N kernel-valid
definitions x04c.d0 .. x04c.dN (chain3 shape: x04c.d(i+1) : Type := (fun _ : Type => x04c.d(i)) S, S shared, mentioning K
extra constants x04c.e*), appended with fresh dense indices. The chain is outside the theorems' closure (statement/axiom
comparison unaffected) but every replay kernel checks it."""
import json, sys
base, N, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]; K = int(sys.argv[4]) if len(sys.argv) > 4 else 2
PFX = sys.argv[5] if len(sys.argv) > 5 else 'x04c'   # namespace of the chain names (changes the NameSet order -> walk depth)
mn = ml = me = -1
import re
L1 = PROP = TYPE = xn = None
with open(base, 'rb') as f:
    f.readline()
    for line in f:
        m = re.match(rb'\{"il":(\d+),"succ":0\}$', line.rstrip())
        if m and L1 is None: L1 = int(m.group(1))
        m = re.match(rb'\{"ie":(\d+),"sort":(\d+)\}$', line.rstrip())
        if m and int(m.group(2)) == 0 and PROP is None: PROP = int(m.group(1))
        if m and L1 is not None and int(m.group(2)) == L1 and TYPE is None: TYPE = int(m.group(1))
        m = re.match(rb'\{"in":(\d+),"str":\{"pre":0,"str":"x"\}\}$', line.rstrip())
        if m and xn is None: xn = int(m.group(1))
        if line.startswith(b'{"in":'): mn = max(mn, int(line[6:line.index(b',')]))
        elif line.startswith(b'{"il":'): ml = max(ml, int(line[6:line.index(b',')]))
        else:
            j = line.find(b'"ie":')
            if j >= 0:
                k = j + 5; e = k
                while line[e:e+1].isdigit(): e += 1
                me = max(me, int(line[k:e]))
o = open(out, 'wb', buffering=1 << 24)
with open(base, 'rb') as f:
    while True:
        b = f.read(1 << 24)
        if not b: break
        o.write(b)
w = lambda s: o.write(s.encode())
ni, li, ei = mn + 1, ml + 1, me + 1
# reuse the base's own nodes (nanoda rejects structurally duplicate names/levels/exprs)
if L1 is None: w('{"il":%d,"succ":0}\n' % li); L1 = li
if PROP is None: w('{"ie":%d,"sort":0}\n' % ei); PROP = ei; ei += 1
if TYPE is None: w('{"ie":%d,"sort":%d}\n' % (ei, L1)); TYPE = ei; ei += 1
w('{"in":%d,"str":{"pre":0,"str":"%s"}}\n' % (ni, PFX)); NS = ni; ni += 1
w('{"in":%d,"str":{"pre":%d,"str":"x"}}\n' % (ni, NS)); xn = ni; ni += 1   # fresh binder name x04c.x
es = []
for k in range(K):
    w('{"in":%d,"str":{"pre":%d,"str":"e%d"}}\n' % (ni, NS, k))
    w('{"def":{"all":[%d],"hints":{"regular":1},"levelParams":[],"name":%d,"safety":"safe","type":%d,"value":%d}}\n' % (ni, ni, TYPE, PROP))
    w('{"ie":%d,"const":{"name":%d,"us":[]}}\n' % (ei, ni)); es.append(ei); ni += 1; ei += 1
body = es[0]                                # S = (fun _ .. _ => x04c.e0) e0 .. e(K-1) : Type (new nodes only)
for k in range(K):
    w('{"ie":%d,"lam":{"binderInfo":"default","body":%d,"name":%d,"type":%d}}\n' % (ei, body, xn, TYPE)); body = ei; ei += 1
for k in range(K):
    w('{"app":{"arg":%d,"fn":%d},"ie":%d}\n' % (es[K - 1 - k], body, ei)); body = ei; ei += 1
S = body; prev = PROP
for i in range(N + 1):
    w('{"ie":%d,"lam":{"binderInfo":"default","body":%d,"name":%d,"type":%d}}\n' % (ei, prev, xn, TYPE)); lam = ei; ei += 1
    w('{"app":{"arg":%d,"fn":%d},"ie":%d}\n' % (S, lam, ei)); val = ei; ei += 1
    w('{"in":%d,"str":{"pre":%d,"str":"d%d"}}\n' % (ni, NS, i))
    w('{"def":{"all":[%d],"hints":{"regular":%d},"levelParams":[],"name":%d,"safety":"safe","type":%d,"value":%d}}\n' % (ni, min(i + 2, 65535), ni, TYPE, val))
    w('{"ie":%d,"const":{"name":%d,"us":[]}}\n' % (ei, ni)); prev = ei; ni += 1; ei += 1
o.close()

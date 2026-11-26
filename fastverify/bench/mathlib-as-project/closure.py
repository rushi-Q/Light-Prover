#!/usr/bin/env python3
"""closure.py ROOTDIR MOD... : import closure (within ROOTDIR's modules) of the given modules; prints count, depth
(longest import chain), and optionally the list. Parses `[public] [meta] import [all] X` header lines."""
import os, re, sys, functools
root = sys.argv[1]; mods = sys.argv[2:]
pat = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»\']+)')
cache = {}
def imports(m):
    if m in cache: return cache[m]
    p = os.path.join(root, *m.split('.')) + '.lean'
    res = None
    if os.path.exists(p):
        res = []
        with open(p, encoding='utf-8') as f:
            in_comment = 0
            for ln in f:
                s = ln.strip()
                if in_comment:
                    if '-/' in s: in_comment = 0
                    continue
                if s.startswith('/-'):
                    if '-/' not in s[2:]: in_comment = 1
                    continue
                if not s or s.startswith('--') or s.startswith('module') or s.startswith('prelude'): continue
                mm = pat.match(ln)
                if mm: res.append(mm.group(1)); continue
                break
    cache[m] = res
    return res
seen = {}
sys.setrecursionlimit(100000)
def depth(m):
    if m in seen: return seen[m]
    seen[m] = 0
    ims = imports(m)
    d = 1 + max([depth(x) for x in ims if imports(x) is not None] or [0]) if ims is not None else 0
    seen[m] = d
    return d
clos = set(); st = list(mods)
while st:
    m = st.pop()
    if m in clos or imports(m) is None: continue
    clos.add(m); st.extend(imports(m))
print(len(clos), max(depth(m) for m in mods))
if os.environ.get('LIST'):
    for m in sorted(clos): print(m)

#!/usr/bin/env python3
"""Scan import headers of a Lean source tree; write module -> imports json."""
import os, sys, json, re
src = sys.argv[1]; out = sys.argv[2]
res = {}
lines_tot = 0
for root, dirs, files in os.walk(src):
    for f in files:
        if not f.endswith('.lean'): continue
        p = os.path.join(root, f)
        mod = os.path.relpath(p, src)[:-5].replace('/', '.')
        imps = []
        nl = 0
        with open(p, encoding='utf-8', errors='replace') as fh:
            data = fh.read()
        nl = data.count('\n')
        # header: lines until first non-import, non-comment, non-blank
        for ln in data.split('\n'):
            s = ln.strip()
            if s.startswith('import '):
                imps.extend(s[7:].split())
            elif s == '' or s.startswith('--') or s.startswith('module') or s.startswith('public import') or s.startswith('prelude'):
                if s.startswith('public import'): imps.extend(s[len('public import '):].split())
                continue
            elif s.startswith('/-'):
                continue
            else:
                break
        res[mod] = {'imports': imps, 'lines': nl, 'bytes': len(data.encode())}
json.dump(res, open(out, 'w'))
print(len(res), sum(v['lines'] for v in res.values()))

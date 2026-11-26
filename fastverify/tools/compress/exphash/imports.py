#!/usr/bin/env python3
"""imports.py SRC_ROOT OUT_TSV : module -> its direct imports (header `import` lines), one row per module."""
import os, sys
root, out = sys.argv[1], sys.argv[2]
with open(out, 'w') as o:
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if not d.startswith('.')]
        for f in fn:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            mod = os.path.relpath(p, root)[:-5].replace('/', '.')
            imps = []
            with open(p, encoding='utf-8', errors='replace') as fh:
                for line in fh:
                    s = line.strip()
                    if not s or s.startswith('--'):
                        continue
                    if s.startswith('import '):
                        imps.extend(s.split()[1:])
                    elif s.startswith('prelude') or s.startswith('module'):
                        continue
                    else:
                        break
            o.write(mod + '\t' + ' '.join(imps) + '\n')

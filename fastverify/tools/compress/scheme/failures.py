#!/usr/bin/env python3
"""c1_failures.py SCHED_OUT SRC_DIR OUT_TSV -- per failing module of a keep-going build: every error message (kind, first
line), the identifier it names, and the declaration enclosing the error line in the built source."""
import json, os, re, sys, collections
sched, src, out = sys.argv[1:4]
mods = [json.loads(l) for l in open(sched) if '"event": "module"' in l]
last = {}; alltxt = {}
for m in mods:
    last[m['module']] = m
    alltxt[m['module']] = alltxt.get(m['module'], '') + '\n' + (m.get('stdout_head', '') or '')
bad = sorted(n for n, m in last.items() if m.get('rc') != 0 or m.get('error_msg') or m.get('missing'))
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|example|alias)\s+([^\s:(\[{]+)?')
def decl_at(mod, line):
    p = os.path.join(src, mod.replace('.', '/') + '.lean')
    try:
        L = open(p, encoding='utf-8').read().split('\n')
    except OSError:
        return '?', '?'
    for i in range(min(line, len(L)) - 1, -1, -1):
        m = DECL.match(L[i])
        if m:
            return m.group(1), (m.group(2) or '')
    return '-', ''
cls = collections.Counter(); rows = []
for n in bad:
    m = last[n]; txt = alltxt[n]
    errs = []
    for ln in txt.split('\n'):
        ln = ln.strip()
        if not ln.startswith('{'):
            continue
        try:
            d = json.loads(ln)
        except Exception:
            continue
        if d.get('severity') != 'error':
            continue
        msg = d.get('data', '').split('\n')[0]
        line = (d.get('pos') or {}).get('line', 0)
        k = re.sub(r'`[^`]*`', '`X`', msg)[:80]
        ident = re.findall(r'`([^`]*)`', msg)
        errs.append((line, k, ident, msg))
    if not errs:
        k = 'missing-deps' if m.get('missing') else ('no-error-json:' + (txt[:60] or m.get('stderr_head', '')[:60]).replace('\t', ' ').replace('\n', ' '))
        rows.append((n, k, '', 0, '', '', ''))
        cls[k.split(':')[0]] += 1
        continue
    line, k, ident, msg = errs[0]
    dk, dn = decl_at(n, line)
    cls[k] += 1
    rows.append((n, k, ','.join(ident[:3]), line, dk, dn, msg[:300].replace('\t', ' ')))
with open(out, 'w') as f:
    for r in rows:
        f.write('\t'.join(map(str, r)) + '\n')
print('modules', len(last), 'failed', len(bad))
for k, v in cls.most_common(30):
    print(f'{v:6d}  {k}')

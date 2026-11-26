#!/usr/bin/env python3
"""summarize_sample.py SAMPLE_RES RECHECK_OUT EDITS_TSV -> JSON summary of a DHE module sample."""
import sys, json, collections, re
res, rech, ed = sys.argv[1:4]
E = collections.defaultdict(list)
for ln in open(ed, encoding='utf-8'):
    p = ln.rstrip('\n').split('\t', 5)
    E[p[0]].append((int(p[1]), int(p[2]), p[3]))
summ = {}
for ln in open(rech):
    m, rest = ln.rstrip('\n').split(' ', 1)
    if rest.startswith('SUMMARY') or rest.startswith('ERROR'):
        summ[m] = rest
S = collections.Counter(); secs = collections.defaultdict(float)
for ln in open(res):
    f = ln.split()
    m = f[1]; kv = dict(x.split('=', 1) for x in f[2:7])
    rcA, rcB = kv['rcA'], kv['rcB']
    if rcA != '0':
        v = 'orig-failed'
    elif rcB != '0':
        v = 'build-failed'
    else:
        sm = summ.get(m, '')
        d = dict(x.split('=') for x in sm.split()[1:]) if sm.startswith('SUMMARY') else {}
        if not d:
            v = 'dlc-error'
        elif d['different'] == '0' and d['onlyA'] == '0' and d['onlyB'] == '0':
            v = 'pass'
        else:
            v = 'different'
    S['modules'] += 1; S[v] += 1
    nd = sum(e - s + 1 for s, e, a in E[m] if a == 'delete'); nr = sum(1 for s, e, a in E[m] if a == 'replace')
    S['edits_' + v] += len(E[m]); S['dellines_' + v] += nd; S['replace_' + v] += nr
    if v == 'pass':
        secs['A'] += float(kv['secsA']); secs['B'] += float(kv['secsB'])
out = dict(S)
out['pass_rate_modules'] = round(S['pass'] / max(1, S['modules']), 4)
out['elab_s_pass_A'] = round(secs['A'], 1); out['elab_s_pass_B'] = round(secs['B'], 1)
print(json.dumps(out, indent=1, sort_keys=True))

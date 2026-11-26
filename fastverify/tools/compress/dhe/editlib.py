"""Team-P edit lists (module<TAB>start<TAB>end<TAB>action<TAB>owner<TAB>replacement, 1-based inclusive lines against the
ORIGINAL sources; replacement '\\n'-escaped): reading and applying (same semantics as dedup/apply_edits.py)."""
import collections

def unesc(s):
    out = []; i = 0
    while i < len(s):
        if s[i] == '\\' and i + 1 < len(s):
            out.append('\n' if s[i + 1] == 'n' else s[i + 1]); i += 2
        else:
            out.append(s[i]); i += 1
    return ''.join(out)

def read_edits(path):
    E = collections.defaultdict(list)
    raw = collections.defaultdict(list)
    for ln in open(path, encoding='utf-8'):
        p = ln.rstrip('\n').split('\t', 5)
        if len(p) < 5:
            continue
        mod, s, e, act, owner = p[:5]
        E[mod].append((int(s), int(e), act, owner, unesc(p[5]) if len(p) > 5 else ''))
        raw[mod].append(ln if ln.endswith('\n') else ln + '\n')
    return E, raw

def apply(lines, es):
    new = list(lines)
    for s, e, act, owner, txt in sorted(es, key=lambda t: (-t[0], -t[1])):
        if act == 'replace':
            new[s - 1:e] = txt.split('\n')
        elif act == 'delete':
            new[s - 1:e] = []
        elif act == 'insert_before':
            new[s - 1:s - 1] = txt.split('\n')
        else:
            raise ValueError(act)
    return new

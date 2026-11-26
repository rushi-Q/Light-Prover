#!/usr/bin/env python3
"""redirect_check.py SCAN_DIR PLAN_TSV SRC_DIR OUT_TSV

For every ALIAS/IMPORT member of a dupplan plan with binfo_eq = 1: can it be DELETED, with every reference to it
rewritten to its target? Safe-by-construction textual criterion:
  * every user constant (a constant whose type/value mentions the member) maps to a source declaration (auxiliary
    constants such as foo._proof_1 / foo.eq_1 / foo.match_1 map to the nearest ancestor name with a declaration range
    in the same module), and
  * that declaration's source text contains the member's FULL source name as a token (optionally `@`/`_root_.`
    prefixed) - full names resolve to the same constant wherever they are written (no namespace/open dependence), and
    with equal binder infos the positional arguments stay valid;
  * the member has no attribute (@[...] / `attribute [...] name` in its module): attributes can make tactics use it
    implicitly (simp, ext, instances), which no textual reference shows.
OUT_TSV: member, member_module, target, users (module:line,line;...), verdict (OK / reason).
"""
import sys, os, glob, re, collections

SCAN, PLAN, SRC, OUT = sys.argv[1:5]
ids = {}; names = []
def iid(s):
    i = ids.get(s)
    if i is None:
        i = len(names); ids[s] = i; names.append(s)
    return i
owner = {}; rng = {}; users = collections.defaultdict(list)
for f in sorted(glob.glob(SCAN + '/c*.tsv')):
    for ln in open(f, encoding='utf-8', errors='replace'):
        p = ln.rstrip('\n').split('\t')
        if p[0] != 'K':
            continue
        c = iid(p[3])
        if c in owner and int(p[8]) == 0:
            continue
        owner[c] = p[1]; rng[c] = (int(p[8]), int(p[9]))
        if len(p) > 10 and p[10]:
            for u in p[10].split(' '):
                users[iid(u)].append(c)
print('loaded', len(owner), flush=True)
children_with_range = collections.Counter()
for c in owner:
    if rng[c][0] > 0 and '.' in names[c]:
        n = names[c]
        if n.startswith('_private.'):
            i = n.find('.0.')
            n = n[i + 3:] if i > 0 else n
        parts = n.split('.')
        for k in range(1, len(parts)):
            children_with_range['.'.join(parts[:k])] += 1

def source_decl(c):
    """map a constant to a constant with a declaration range in the same module (itself or an ancestor name)"""
    if rng[c][0] > 0:
        return c
    n = names[c]; mod = owner[c]
    while '.' in n:
        n = n.rsplit('.', 1)[0]
        d = ids.get(n)
        if d is not None and d in owner and owner[d] == mod and rng[d][0] > 0:
            return d
    return None

def user_name(full):
    if full.startswith('_private.'):
        i = full.find('.0.')
        if i > 0:
            return full[i + 3:]
    return full

srccache = {}
def lines_of(mod):
    if mod not in srccache:
        if len(srccache) > 5000:
            srccache.clear()
        srccache[mod] = open(os.path.join(SRC, mod.replace('.', '/') + '.lean'), encoding='utf-8').read().split('\n')
    return srccache[mod]

S = collections.Counter()
out = open(OUT, 'w')
rows = [l.rstrip('\n').split('\t') for l in open(PLAN)][1:]
for r in rows:
    gi, act, name, mod, tgt, tmod = r[:6]
    if act not in ('ALIAS', 'IMPORT'):
        continue
    if len(r) < 16 or r[15] != '1':
        S['skip_binfo'] += 1; continue
    S['members'] += 1
    c = ids.get(name)
    if c is None or c not in owner:
        S['notfound'] += 1; continue
    un = user_name(name)
    if name.startswith('_private.'):
        verdict = 'private'  # private: users are in the same module; full name not usable from outside - still OK textually
    L = lines_of(mod)
    l1, l2 = rng[c]
    dtext = '\n'.join(L[max(0, l1 - 1):l2])
    short = un.rsplit('.', 1)[-1]
    if '@[' in dtext.split(':=')[0] or re.search(r'attribute\s*\[[^\]]*\]\s*[^\n]*\b' + re.escape(short) + r'\b', '\n'.join(L)):
        out.write(f'{name}\t{mod}\t{tgt}\t\tattribute\n'); S['attribute'] += 1; continue
    if children_with_range.get(un):
        out.write(f'{name}\t{mod}\t{tgt}\t\thas-children\n'); S['has-children'] += 1; continue
    # Check same-module textual references outside [l1,l2] (catches `:= rfl` / `simp only [short]` invisible in kernel used_constants)
    short_re = re.compile(r'(?<![\w.\'])(?:@|_root_\.)?' + re.escape(short) + r'(?![\w\'!?])')
    other_mod_text = '\n'.join(L[:max(0, l1 - 1)] + L[l2:])
    if short_re.search(other_mod_text):
        out.write(f'{name}\t{mod}\t{tgt}\t\tsame-mod-short-ref\n'); S['same-mod-short-ref'] += 1; continue
    tok = re.compile(r'(?<![\w.\'])(?:@|_root_\.)?' + re.escape(un) + r'(?![\w\'!?])')
    locs = []; ok = True; reason = 'OK'
    ulist = set()
    for u in users.get(c, []):
        d = source_decl(u)
        if d is None:
            ok = False; reason = 'aux-user-without-decl'; break
        ulist.add(d)
    if ok:
        for d in ulist:
            if d == c:
                continue
            um = owner[d]; ul1, ul2 = rng[d]
            UL = lines_of(um)
            hit = [k + 1 for k in range(ul1 - 1, ul2) if tok.search(UL[k])]
            if not hit:
                ok = False; reason = 'no-fullname-token'; break
            # Reject named-argument calls `(arg := ...)` on matched lines: alpha-equal target may have different binder names
            if any(re.search(r'\([A-Za-z_α-κμ-ϻ][A-Za-z0-9_\'₀-₉]*\s*:=', UL[ln - 1]) for ln in hit):
                ok = False; reason = 'named-arg-call'; break
            locs.append(f'{um}:{",".join(map(str, hit))}')
    if ok and not ulist - {c}:
        reason = 'OK-unused'
    S[reason] += 1
    out.write(f'{name}\t{mod}\t{tgt}\t{";".join(locs)}\t{reason}\n')
out.close()
for k, v in sorted(S.items()):
    print(k, v)

#!/usr/bin/env python3
"""dedup_filter.py PLAN EDITS SRC OUT [--no-import] [--deny FILE] [--jobs N] -- make the dedup edit list (team format)
safe against the failure classes seen in the full-RH build of the composite candidate C1:

  IMPORT   members whose target becomes visible only through an ADDED import (plan action IMPORT/SHARED), and every
           insert_before/newfile edit: an added import brings new names into scope ('Ambiguous term' in importers).
  SHORT    redirected (deleted) members referred to anywhere by a token other than their exact full name (`s`, `X.s`,
           `h.s`: short names inside the namespace, partial qualification, field notation) or mentioned by a module
           without a subst edit for them: the subst rewrites only full names ('Unknown identifier').
  NAMED    alias/redirect members whose short name occurs on a line with named-argument syntax `(x := ...)`: the
           target's binder NAMES differ ('Invalid argument name').
  DENY     member full names from a file (failure-driven repairs).

A dropped member keeps its original declaration: its replace/delete edits and every subst edit 'M T' are removed.
Targets are kept copies by construction (the dedup plan), so dropping members never invalidates other edits."""
import argparse, collections, os, re, sys
from multiprocessing import Pool
ap = argparse.ArgumentParser()
ap.add_argument('plan'); ap.add_argument('edits'); ap.add_argument('src'); ap.add_argument('out')
ap.add_argument('--no-import', action='store_true'); ap.add_argument('--deny', action='append', default=[])
ap.add_argument('--jobs', type=int, default=32)
a = ap.parse_args()
_LL = ("A-Za-z0-9_'!?"
       "α-κμ-ωΑ-ΟΡ΢Τ-Ωϊ-ϻἀ-῾"
       "℀-⅏\U0001d49c-\U0001d59f₀-₉ₐ-ₜᵢ-ᵪⱼ")
TOK = re.compile("[" + _LL + "]+(?:\\.[" + _LL + "]+)*")
NAMED = re.compile(r"\(\s*[A-Za-z_α-ω][A-Za-z0-9_'α-ω₀-₉]*\s*:=")

plan = {}
by_mod = collections.defaultdict(list)
for ln in open(a.plan, encoding='utf-8'):
    p = ln.rstrip('\n').split('\t')
    if p[0] == 'group' or len(p) < 13: continue
    act, name, mod = p[1], p[2], p[3]
    if act in ('KEEP', 'KEEP_BINFO'): continue
    plan[name] = (act, mod, int(p[11]), int(p[12]))
    by_mod[mod].append(name)
edits = [ln.rstrip('\n').split('\t', 5) for ln in open(a.edits, encoding='utf-8')]
member_of = {}            # edit index -> member name
subst_of = collections.defaultdict(list)   # member -> edit indices of its subst edits
subst_mods = collections.defaultdict(set)  # member -> modules with a subst for it
own_range = {}            # redirect member -> (module, s, e) of its deleted declaration
kind = {}                 # member -> 'alias' | 'redirect'
del_range = {}            # redirect member -> (module, s, e) of its delete edit
unmapped = 0
# a redirected member is identified by its SOURCE name (the OLD of its subst edits; its own-module subst edit carries
# the declaration's line range), an aliased member by its plan name; plan names of private members differ from the
# source names (`_private.<Module>.0.<name>`), so the delete edit is linked to the own-module subst by (module, end line)
for i, e in enumerate(edits):
    if e[3] == 'subst':
        old = e[5].split(' ', 1)[0]
        subst_of[old].append(i); subst_mods[old].add(e[0])
        if int(e[1]) > 0: own_range[old] = (e[0], int(e[1]), int(e[2]))
own_by_end = {(mod, t): old for old, (mod, s, t) in own_range.items()}
plan_of = {}
unmapped_edits = set()
for i, e in enumerate(edits):
    mod, s, t, act = e[0], int(e[1]), int(e[2]), e[3]
    if act not in ('replace', 'delete'): continue
    cands = [n for n in by_mod.get(mod, ()) if plan[n][3] == t or (s <= plan[n][2] and plan[n][3] <= t)]
    pn = cands[0] if len(cands) == 1 else None
    if act == 'delete' and (mod, t) in own_by_end:
        m = own_by_end[(mod, t)]
    elif pn is not None:
        m = pn
    else:
        unmapped += 1; unmapped_edits.add(i); continue     # ambiguous (e.g. @[to_additive] pairs): dropped below
    member_of[i] = m; kind[m] = 'alias' if act == 'replace' else 'redirect'
    if pn is not None: plan_of[m] = pn
    if act == 'delete': del_range[m] = (mod, s, t)
for m in own_range:
    kind[m] = 'redirect'
members = set(kind)
short = {m: m.rsplit('.', 1)[-1] for m in members}
names_by_short = collections.defaultdict(set)
for m, s in short.items(): names_by_short[s].add(m)
SHORTS = set(names_by_short)

CLOSE = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
TOKCH = re.compile("[" + _LL + ".@]")
def app_tokens(line, p):
    """tokens of the application whose argument list contains the named argument starting at p: walk left over
    arguments (tokens and balanced bracket groups) up to an unmatched opening bracket, an operator or the line start"""
    out = []; i = p - 1
    while i >= 0:
        ch = line[i]
        if ch.isspace(): i -= 1; continue
        if ch in CLOSE:
            depth = 0
            while i >= 0:
                if line[i] in CLOSE: depth += 1
                elif line[i] in CLOSE.values(): depth -= 1
                i -= 1
                if depth == 0: break
            continue
        if TOKCH.match(ch):
            j = i
            while j >= 0 and TOKCH.match(line[j]): j -= 1
            out.append(line[j + 1:i + 1].lstrip('@')); i = j; continue
        break
    return out
def scan(mod):
    """tokens of one original module whose last component is a member short name; + short names on named-arg lines"""
    p = os.path.join(a.src, mod.replace('.', '/') + '.lean')
    try: L = open(p, encoding='utf-8').read().split('\n')
    except OSError: return mod, [], []
    hits = []; named = []
    for k, line in enumerate(L, 1):
        toks = TOK.findall(line)
        for t in toks:
            c = t.rsplit('.', 1)[-1]
            if c in SHORTS: hits.append((k, t))
        for mo in NAMED.finditer(line):
            for t in app_tokens(line, mo.start()):
                c = t.rsplit('.', 1)[-1]
                if c in SHORTS: named.append(c)
    return mod, hits, named
mods = []
for root, _, files in os.walk(a.src):
    for f in files:
        if f.endswith('.lean'):
            mods.append(os.path.relpath(os.path.join(root, f), a.src)[:-5].replace('/', '.'))
unsafe = collections.defaultdict(set)
named_short = set()
with Pool(a.jobs) as pool:
    for mod, hits, named in pool.imap_unordered(scan, mods, chunksize=64):
        named_short.update(named)
        for k, t in hits:
            c = t.rsplit('.', 1)[-1]
            for m in names_by_short[c]:
                if kind[m] != 'redirect': continue
                r = own_range.get(m)
                if r and r[0] == mod and r[1] <= k <= r[2]: continue      # inside its own deleted declaration
                exact = t == m or t == '_root_.' + m
                if exact and mod in subst_mods[m]: continue               # rewritten by the subst
                unsafe[m].add('SHORT' if not exact else 'NOSUBST')
# DANGLING: a deleted declaration whose remaining previous non-blank line is a `... in` modifier (multi-line chains of
# `attribute [..] in` / `variable .. in` / `omit .. in` above the declaration: only the first one is part of the edit)
MODIN = re.compile(r'\bin\s*$')
dangling = set(); cache = {}
for m, (mod, s0, t0) in del_range.items():
    if mod not in cache:
        try: cache[mod] = open(os.path.join(a.src, mod.replace('.', '/') + '.lean'), encoding='utf-8').read().split('\n')
        except OSError: cache[mod] = []
    L = cache[mod]; k = s0 - 2
    while k >= 0 and not L[k].strip(): k -= 1
    if k >= 0 and MODIN.search(L[k]) and not L[k].lstrip().startswith('--'): dangling.add(m)
drop = {}
deny = set()
for f in a.deny:
    deny |= {l.strip() for l in open(f) if l.strip() and not l.startswith('#')}
for m in members:
    act = plan.get(plan_of.get(m, m), ('?',))[0]
    if a.no_import and act in ('IMPORT', 'SHARED'): drop[m] = 'IMPORT'
    elif m in unsafe: drop[m] = sorted(unsafe[m])[0]
    elif m in dangling: drop[m] = 'DANGLING'
    elif short[m] in named_short: drop[m] = 'NAMED'
    elif m in deny or short[m] in deny: drop[m] = 'DENY'
cnt = collections.Counter(); kept = collections.Counter(); lines_kept = 0; lines_dropped = 0
with open(a.out, 'w', encoding='utf-8') as fo:
    for i, e in enumerate(edits):
        act = e[3]
        if act in ('insert_before', 'newfile') and a.no_import:
            cnt['edit_dropped_' + act] += 1; continue
        if act == 'subst':
            m, nw = e[5].split(' ', 1)
            if m in drop: cnt['edit_dropped_subst'] += 1; continue
            if not nw.startswith('_root_.'):        # unambiguous target (a bare name resolves namespace-relative first)
                e = e[:5] + [m + ' _root_.' + nw]; cnt['subst_target_rooted'] += 1
        elif i in unmapped_edits:
            cnt['edit_dropped_unmapped_' + act] += 1; continue
        elif i in member_of and member_of[i] in drop:
            cnt['edit_dropped_' + act] += 1
            lines_dropped += int(e[2]) - int(e[1]) + 1
            continue
        if act in ('replace', 'delete'): lines_kept += int(e[2]) - int(e[1]) + 1
        kept[act] += 1
        fo.write('\t'.join(e) + '\n')
why = collections.Counter(drop.values())
bykind = collections.Counter((kind[m], drop[m]) for m in drop)
print('members', len(members), dict(collections.Counter(kind.values())), 'unmapped edits', unmapped)
print('dropped members', len(drop), dict(why)); print('by kind', dict(bykind))
print('edits kept', dict(kept), 'dropped', dict(cnt), 'replaced/deleted lines kept', lines_kept, 'dropped', lines_dropped)
with open(a.out + '.dropped.tsv', 'w') as f:
    for m, w in sorted(drop.items()): f.write(f'{m}\t{kind[m]}\t{plan.get(plan_of.get(m, m), ("?",))[0]}\t{w}\n')
# self-check: every kept own-module subst (a redirected member's declaration range) has its delete edit, and vice versa
K = [l.rstrip('\n').split('\t', 5) for l in open(a.out, encoding='utf-8')]
dels = {(e[0], int(e[2])) for e in K if e[3] == 'delete'}
owns = {(e[0], int(e[2])) for e in K if e[3] == 'subst' and int(e[1]) > 0}
bad = owns - dels
print('self-check: own-module substs without their delete:', len(bad))
if bad: sys.exit(3)

#!/usr/bin/env python3
"""seams.py BASE.export CONFIG.json OUTDIR : targeted cases against the seams of the trusted check (official
Lean.Replay semantics that a re-implementation could get wrong, parser corner cases, inductive block layout, record
fields the official replay does not compare, unsafe/partial skipping, NUL/getLine behaviour of the official reader).
Writes OUTDIR/<id>.ndjson + OUTDIR/manifest.tsv (id, op=seam, class=X, detail = 'PRED=<predicted official verdict>; what').
The prediction is informational: the official comparator run by runfuzz.py is the oracle."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xfuzz import Ex, canon

class B:
    """append-only builder of fresh names/exprs/levels after the base (dense indices)"""
    def __init__(self, ex):
        self.ex = ex; self.n = ex.max_name() + 1; self.e = ex.max_expr() + 1
        self.l = (max(ex.levels) + 1) if ex.levels else 1; self.lines = []
    def name(self, s, pre=0):
        i = self.n; self.n += 1; self.lines.append(canon({'in': i, 'str': {'pre': pre, 'str': s}})); return i
    def namenum(self, k, pre):
        i = self.n; self.n += 1; self.lines.append(canon({'in': i, 'num': {'i': k, 'pre': pre}})); return i
    def expr(self, kind, data):
        i = self.e; self.e += 1; self.lines.append(canon({'ie': i, kind: data})); return i
    def raw(self, line):
        self.lines.append(line if isinstance(line, bytes) else canon(line))

def find_decl(ex, name, kind=None):
    for i in ex.decls:
        if ex.decl_name(i) == name and (kind is None or ex.declkind[i] == kind):
            return i
    for i in ex.decls:   # constants inside inductive lines
        o = ex.get(i)
        if 'inductive' in o:
            for part in ('types', 'ctors', 'recs'):
                for x in o['inductive'][part]:
                    if ex.name_str(x['name']) == name:
                        return i
    return None

def find_const_expr(ex, name, us=()):
    for k, li in ex.exprs.items():
        o = ex.get(li)
        if 'const' in o and ex.name_str(o['const']['name']) == name and o['const']['us'] == list(us):
            return k
    return None

def closure_names(ex, targets):
    """names in the comparator's compareAt closure (types of theorem targets, then everything reachable)"""
    byname = {}
    for i in ex.decls:
        o = ex.get(i); k = next(iter(o))
        if k == 'inductive':
            for part in ('types', 'ctors', 'recs'):
                for x in o[k][part]:
                    byname[ex.name_str(x['name'])] = (part, x)
        else:
            byname[ex.name_str(o[k]['name'])] = (k, o[k])
    memo = {}
    def consts(e):
        if e in memo: return memo[e]
        out = set(); st = [e]; seen = set()
        while st:
            x = st.pop()
            if x in seen or x not in ex.exprs: continue
            seen.add(x); o = ex.get(ex.exprs[x]); kd = [y for y in o if y != 'ie'][0]; d = o[kd]
            if kd == 'const': out.add(ex.name_str(d['name']))
            elif kd == 'app': st += [d['fn'], d['arg']]
            elif kd in ('lam', 'forallE'): st += [d['type'], d['body']]
            elif kd == 'letE': st += [d['type'], d['value'], d['body']]
            elif kd == 'mdata': st.append(d['expr'])
            elif kd == 'proj': st.append(d['struct'])
        memo[e] = out; return out
    work = []
    for t in targets:
        if t in byname:
            work += list(consts(byname[t][1]['type']))
    # compareAt's worklist also starts with the kernel primitives, the permitted axioms and (with Quot.sound) the Quot names
    work += ['Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land',
             'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List', 'eagerReduce', 'Nat',
             'String', 'String.mk', 'Char', 'optParam', 'autoParam', 'semiOutParam', 'outParam',
             'propext', 'Quot.sound', 'Classical.choice', 'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind']
    seen = set(targets)
    while work:
        n = work.pop()
        if n in seen or n not in byname: continue
        seen.add(n); part, d = byname[n]
        work += list(consts(d['type']))
        if 'value' in d: work += list(consts(d['value']))
        if part == 'types': work += [ex.name_str(c) for c in d['ctors']] + [ex.name_str(a) for a in d['all']]
        if part == 'ctors': work.append(ex.name_str(d['induct']))
        if part == 'recs':
            for r in d['rules']: work.append(ex.name_str(r['ctor'])); work += list(consts(r['rhs']))
    return seen, byname

CASES = []
def case(cid, pred, what):
    def d(f):
        CASES.append((cid, pred, what, f)); return f
    return d

def thm_value_expr(ex, name):
    i = find_decl(ex, name, 'thm'); return ex.get(i)['thm']['value'], ex.get(i)['thm']['type'], i

# ---------------- A: unsafe / partial constants (the official replay skips them: `!ci.isUnsafe && !ci.isPartial`)
@case('A1-unsafe-def-illtyped-unused', 'ACCEPTED', 'unused unsafe def whose value does not have its type (official replay skips unsafe constants)')
def a1(ex, ctx):
    b = B(ex); nat = find_const_expr(ex, 'Nat'); n = b.name('V06unsafeBad'); prop = b.expr('sort', 0)
    b.raw({'def': {'all': [n], 'hints': {'regular': 1}, 'levelParams': [], 'name': n, 'safety': 'unsafe', 'type': nat, 'value': prop}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('A2-partial-def-illtyped-unused', 'ACCEPTED', 'unused partial def, ill-typed value (skipped like unsafe)')
def a2(ex, ctx):
    b = B(ex); nat = find_const_expr(ex, 'Nat'); n = b.name('V06partialBad'); prop = b.expr('sort', 0)
    b.raw({'def': {'all': [n], 'hints': {'regular': 1}, 'levelParams': [], 'name': n, 'safety': 'partial', 'type': nat, 'value': prop}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('A3-unsafe-axiom-false-unused', 'ACCEPTED', 'unused unsafe axiom False (skipped by the replay, outside the closure)')
def a3(ex, ctx):
    b = B(ex); fl = find_const_expr(ex, 'False'); n = b.name('V06unsafeAx')
    b.raw({'axiom': {'isUnsafe': True, 'levelParams': [], 'name': n, 'type': fl}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('A4-target-proof-via-unsafe-def', 'REJECTED', 'a target proved by an unsafe def that holds the honest proof (unsafe constant absent from the kernel env)')
def a4(ex, ctx):
    t = ctx['thm']; v, ty, i = thm_value_expr(ex, t); b = B(ex); n = b.name('V06unsafeProof')
    b.raw({'def': {'all': [n], 'hints': {'regular': 1}, 'levelParams': [], 'name': n, 'safety': 'unsafe', 'type': ty, 'value': v}})
    c = b.expr('const', {'name': n, 'us': []})
    o = json.loads(json.dumps(ex.get(i))); o['thm']['value'] = c
    return ex.out({i: canon(o)}, insert={i: b.lines})
@case('A5-target-proof-via-partial-def', 'REJECTED', 'a target proved by a partial def holding the honest proof')
def a5(ex, ctx):
    t = ctx['thm']; v, ty, i = thm_value_expr(ex, t); b = B(ex); n = b.name('V06partialProof')
    b.raw({'def': {'all': [n], 'hints': {'regular': 1}, 'levelParams': [], 'name': n, 'safety': 'partial', 'type': ty, 'value': v}})
    c = b.expr('const', {'name': n, 'us': []})
    o = json.loads(json.dumps(ex.get(i))); o['thm']['value'] = c
    return ex.out({i: canon(o)}, insert={i: b.lines})
@case('A6-target-proof-via-unsafe-opaque', 'REJECTED', 'a target proved by an unsafe opaque holding the honest proof')
def a6(ex, ctx):
    t = ctx['thm']; v, ty, i = thm_value_expr(ex, t); b = B(ex); n = b.name('V06unsafeOpaque')
    b.raw({'opaque': {'all': [n], 'isUnsafe': True, 'levelParams': [], 'name': n, 'type': ty, 'value': v}})
    c = b.expr('const', {'name': n, 'us': []})
    o = json.loads(json.dumps(ex.get(i))); o['thm']['value'] = c
    return ex.out({i: canon(o)}, insert={i: b.lines})
@case('A7-orphan-unsafe-ctor', 'ACCEPTED', 'extra constructor of an existing inductive, not in its ctors list, marked unsafe (skipped)')
def a7(ex, ctx):
    ind = ctx['ind']; i = find_decl(ex, ind); o = ex.get(i)['inductive']; c0 = o['ctors'][0]
    b = B(ex); n = b.name('V06orphanCtor', pre=c0['induct'])
    c = dict(c0); c['name'] = n; c['isUnsafe'] = True; c['cidx'] = 7
    b.raw({'inductive': {'ctors': [c], 'recs': [], 'types': []}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('A8-orphan-safe-ctor', 'REJECTED', 'extra SAFE constructor not generated by the kernel ("No such constructor")')
def a8(ex, ctx):
    ind = ctx['ind']; i = find_decl(ex, ind); o = ex.get(i)['inductive']; c0 = o['ctors'][0]
    b = B(ex); n = b.name('V06orphanCtor', pre=c0['induct'])
    c = dict(c0); c['name'] = n; c['cidx'] = 7
    b.raw({'inductive': {'ctors': [c], 'recs': [], 'types': []}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('A9-orphan-safe-rec', 'REJECTED', 'extra SAFE recursor (copy of an existing one under a new name) not generated by the kernel')
def a9(ex, ctx):
    ind = ctx['ind']; i = find_decl(ex, ind); o = ex.get(i)['inductive']; r0 = o['recs'][0]
    b = B(ex); n = b.name('V06orphanRec', pre=o['types'][0]['name'])
    r = json.loads(json.dumps(r0)); r['name'] = n
    b.raw({'inductive': {'ctors': [], 'recs': [r], 'types': []}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('A10-unsafe-inductive-nonpositive', 'ACCEPTED', 'fresh unsafe inductive with an ill-formed constructor type (skipped)')
def a10(ex, ctx):
    b = B(ex); n = b.name('V06UBad'); cn = b.name('mk', pre=n); t1 = b.expr('sort', 1)
    prop = b.expr('sort', 0)
    b.raw({'inductive': {'types': [{'all': [n], 'ctors': [cn], 'isRec': False, 'isReflexive': False, 'isUnsafe': True, 'levelParams': [],
            'name': n, 'numIndices': 0, 'numNested': 0, 'numParams': 0, 'type': t1}],
           'ctors': [{'cidx': 0, 'induct': n, 'isUnsafe': True, 'levelParams': [], 'name': cn, 'numFields': 0, 'numParams': 0, 'type': prop}],
           'recs': []}})
    return ex.out(insert={len(ex.lines): b.lines})

# ---------------- B: inductive record fields (InductiveVal is NOT compared with the kernel's by Lean.Replay)
def rec_lie(ex, ctx, which, field, f):
    seen, byname = ctx['closure']
    pool = [i for i in ex.decls if ex.declkind[i] == 'inductive' and
            ((ex.decl_name(i) in seen) == (which == 'closure')) and len(ex.get(i)['inductive']['types']) == 1]
    if not pool: return None
    i = pool[len(pool) // 2]; o = json.loads(json.dumps(ex.get(i))); t = o['inductive']['types'][0]
    t[field] = f(t[field]); return ex.out({i: canon(o)}), ex.decl_name(i)
for fld, f in [('isRec', lambda x: not x), ('isReflexive', lambda x: not x), ('numNested', lambda x: x + 1), ('numIndices', lambda x: x + 1)]:
    for which, pred in [('nonclosure', 'ACCEPTED'), ('closure', 'REJECTED')]:
        def mk(fld=fld, f=f, which=which):
            return lambda ex, ctx: rec_lie(ex, ctx, which, fld, f)
        case(f'B-{fld}-{which}', pred, f'inductive record field {fld} changed on a {which} inductive')(mk())

# ---------------- C: inductive block layout (the parser flattens types/ctors/recs: same meaning)
@case('C1-rec-own-line', 'ACCEPTED', 'one recursor of the mutual block moved to its own "inductive" line at the end')
def c1(ex, ctx):
    i = find_decl(ex, ctx['mutual']); o = json.loads(json.dumps(ex.get(i))); r = o['inductive']['recs'].pop()
    return ex.out({i: canon(o)}, insert={len(ex.lines): [canon({'inductive': {'ctors': [], 'recs': [r], 'types': []}})]})
@case('C2-block-split-lines', 'ACCEPTED', 'mutual block split into one line per type (each with its ctors and recs)')
def c2(ex, ctx):
    i = find_decl(ex, ctx['mutual']); o = ex.get(i)['inductive']; lines = []
    for t in o['types']:
        cs = [c for c in o['ctors'] if c['induct'] == t['name']]
        rs = [r for r in o['recs'] if ex.name_str(r['name']).startswith(ex.name_str(t['name']) + '.')]
        lines.append(canon({'inductive': {'ctors': cs, 'recs': rs, 'types': [t]}}))
    return ex.out(insert={i: lines}, delete={i})
@case('C3-nested-auxrec-at-end', 'ACCEPTED', 'auxiliary recursor of the nested inductive moved to the end of the file')
def c3(ex, ctx):
    i = find_decl(ex, ctx['nested']); o = json.loads(json.dumps(ex.get(i)))
    if len(o['inductive']['recs']) < 2: return None
    r = o['inductive']['recs'].pop()
    return ex.out({i: canon(o)}, insert={len(ex.lines): [canon({'inductive': {'ctors': [], 'recs': [r], 'types': []}})]})
@case('C4-rec-in-other-block-line', 'ACCEPTED', 'a recursor listed in the line of a different (later) inductive')
def c4(ex, ctx):
    i = find_decl(ex, ctx['ind']); j = find_decl(ex, ctx['nested'])
    oi = json.loads(json.dumps(ex.get(i))); oj = json.loads(json.dumps(ex.get(j)))
    r = oi['inductive']['recs'].pop(); oj['inductive']['recs'].append(r)
    return ex.out({i: canon(oi), j: canon(oj)})
@case('C5-ctor-in-other-block-line', 'ACCEPTED', 'a constructor listed in the line of a different (later) inductive')
def c5(ex, ctx):
    i = find_decl(ex, ctx['ind']); j = find_decl(ex, ctx['nested'])
    oi = json.loads(json.dumps(ex.get(i))); oj = json.loads(json.dumps(ex.get(j)))
    c = oi['inductive']['ctors'].pop(); oj['inductive']['ctors'].append(c)
    return ex.out({i: canon(oi), j: canon(oj)})
@case('D1-mutual-all-split', 'REJECTED', 'mutual inductive: each type claims all=[itself] (not declarable alone)')
def d1(ex, ctx):
    i = find_decl(ex, ctx['mutual']); o = json.loads(json.dumps(ex.get(i)))
    for t in o['inductive']['types']: t['all'] = [t['name']]
    return ex.out({i: canon(o)})
@case('D2-mutual-all-reordered', 'REJECTED?', 'mutual inductive: all list reversed on the first type only')
def d2(ex, ctx):
    i = find_decl(ex, ctx['mutual']); o = json.loads(json.dumps(ex.get(i)))
    t = o['inductive']['types'][0]; t['all'] = t['all'][::-1]
    return ex.out({i: canon(o)})

# ---------------- E: NUL bytes vs the official reader's getLine (fgets + strlen)
@case('E1-nul-line-tail-garbage', 'ACCEPTED', 'a line starting with NUL then garbage lines at the end: the official reader stops at the NUL line')
def e1(ex, ctx):
    return ex.out(insert={len(ex.lines): [b'\x00 the official reader stops here\n', b'not json at all\n', b'{"ie":0,"bvar":5}\n']})
@case('E2-nul-line-middle', 'REJECTED', 'a NUL line in the middle: the official reader drops everything after it (missing declarations)')
def e2(ex, ctx):
    return ex.out(insert={len(ex.lines) // 2: [b'\x00\n']})
@case('E3-nul-hidden-unused-axiom', 'ACCEPTED', 'an unused axiom item hidden behind NUL in the 63-byte fgets window: only the official reader sees it')
def e3(ex, ctx):
    b = B(ex); fl = find_const_expr(ex, 'False'); n = b.name('V06hid')
    name_line = b.lines[0][:-1]
    ax = canon({'axiom': {'isUnsafe': False, 'levelParams': [], 'name': n, 'type': fl}})
    pad = b'P' * (63 - len(name_line) - 1)
    return ex.out(insert={len(ex.lines): [name_line + b'\x00' + pad + ax]})
@case('E4-nul-hidden-target-proof', 'ACCEPTED?', 'the honest target theorem line hidden behind NUL after a short expression line (official: two lines)')
def e4(ex, ctx):
    t = ctx['thm']; i = find_decl(ex, t, 'thm'); b = B(ex)
    short = canon({'ie': b.e, 'bvar': 0})[:-1]; pad = b'P' * (63 - len(short) - 1)
    return ex.out({i: short + b'\x00' + pad + ex.lines[i]})

# ---------------- F: malformed hygienic names (macro scopes without the _@ marker)
@case('F1-hyg-marker-renamed', 'REJECTED(panic)', 'the "_@" name component renamed to "_X" (every hygienic binder name now has _hyg.N but no _@ marker)')
def f1(ex, ctx):
    for k, li in ex.names.items():
        o = ex.get(li)
        if 'str' in o and o['str']['str'] == '_@':
            o2 = json.loads(json.dumps(o)); o2['str']['str'] = '_X'; return ex.out({li: canon(o2)})
    return None

# ---------------- G: comparator target edge cases
@case('G1-target-all-empty', 'ACCEPTED?', 'a target theorem with all = []')
def g1(ex, ctx):
    i = find_decl(ex, ctx['thm'], 'thm'); o = json.loads(json.dumps(ex.get(i))); o['thm']['all'] = []
    return ex.out({i: canon(o)})
@case('G2-target-all-other', 'ACCEPTED?', 'a target theorem with all = [another name]')
def g2(ex, ctx):
    i = find_decl(ex, ctx['thm'], 'thm'); o = json.loads(json.dumps(ex.get(i))); o['thm']['all'] = [o['thm']['name'], 1]
    return ex.out({i: canon(o)})
@case('G3-target-stmt-mdata', 'REJECTED', 'target statement wrapped in an mdata node (structural compare)')
def g3(ex, ctx):
    i = find_decl(ex, ctx['thm'], 'thm'); o = json.loads(json.dumps(ex.get(i))); b = B(ex)
    m = b.expr('mdata', {'data': {}, 'expr': o['thm']['type']}); o['thm']['type'] = m
    return ex.out({i: canon(o)}, insert={i: b.lines})
@case('G4-target-proof-mdata', 'ACCEPTED', 'target proof wrapped in an mdata node (the kernel ignores mdata)')
def g4(ex, ctx):
    i = find_decl(ex, ctx['thm'], 'thm'); o = json.loads(json.dumps(ex.get(i))); b = B(ex)
    m = b.expr('mdata', {'data': {}, 'expr': o['thm']['value']}); o['thm']['value'] = m
    return ex.out({i: canon(o)}, insert={i: b.lines})
@case('G5-second-thm-bogus', 'REJECTED', 'an extra theorem with a target statement and a wrong proof (every declaration is replayed)')
def g5(ex, ctx):
    i = find_decl(ex, ctx['thm'], 'thm'); d = ex.get(i)['thm']; b = B(ex); n = b.name('V06copy')
    b.raw({'thm': {'all': [n], 'levelParams': d['levelParams'], 'name': n, 'type': d['type'], 'value': d['type']}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('G6-target-as-opaque', 'REJECTED', 'the target theorem exported as an opaque with the honest value')
def g6(ex, ctx):
    i = find_decl(ex, ctx['thm'], 'thm'); d = ex.get(i)['thm']
    return ex.out({i: canon({'opaque': {'all': d['all'], 'isUnsafe': False, 'levelParams': d['levelParams'], 'name': d['name'], 'type': d['type'], 'value': d['value']}})})
@case('G7-opaque-without-isUnsafe', 'ACCEPTED', 'an opaque line without the isUnsafe key (the official reader defaults it to false)')
def g7(ex, ctx):
    for i in ex.decls:
        if ex.declkind[i] == 'opaque':
            o = json.loads(json.dumps(ex.get(i))); o['opaque'].pop('isUnsafe', None); return ex.out({i: canon(o)})
    b = B(ex); nat = find_const_expr(ex, 'Nat'); z = b.expr('natVal', '0'); n = b.name('V06opq')
    b.raw({'opaque': {'all': [n], 'levelParams': [], 'name': n, 'type': nat, 'value': z}})
    return ex.out(insert={len(ex.lines): b.lines})

# ---------------- H: literals
def natlit_case(ex, ctx, f):
    for k, li in ex.exprs.items():
        o = ex.get(li)
        if 'natVal' in o and o['natVal'] not in ('0',):
            o2 = json.loads(json.dumps(o)); o2['natVal'] = f(o['natVal']); return ex.out({li: canon(o2)})
    return None
@case('H1-natlit-leading-zeros', 'ACCEPTED', 'a Nat literal written with leading zeros ("007"; String.toNat? accepts it)')
def h1(ex, ctx): return natlit_case(ex, ctx, lambda s: '00' + s)
@case('H2-natlit-underscore', 'ACCEPTED?', 'a Nat literal with a digit separator ("1_0" style)')
def h2(ex, ctx): return natlit_case(ex, ctx, lambda s: s[0] + '_' + s[1:] if len(s) > 1 else s + '_0')
@case('H3-natlit-plus', 'REJECTED?', 'a Nat literal with a leading "+"')
def h3(ex, ctx): return natlit_case(ex, ctx, lambda s: '+' + s)
@case('H4-strlit-nul-escape', 'ACCEPTED?', 'an unused String literal definition containing \\u0000 and a lone surrogate escape')
def h4(ex, ctx):
    sidx = find_const_expr(ex, 'String')
    if sidx is None: return None
    b = B(ex); n = b.name('V06strNul'); s = b.e; b.e += 1
    b.raw(('{"ie":%d,"strVal":"a\\u0000b\\ud800c"}\n' % s).encode())
    b.raw({'def': {'all': [n], 'hints': {'regular': 1}, 'levelParams': [], 'name': n, 'safety': 'safe', 'type': sidx, 'value': s}})
    return ex.out(insert={len(ex.lines): b.lines})

# ---------------- Q: quotient constants (the kernel adds them itself; the replay erases Quot.mk/lift/ind and post-checks)
def quot_lines(ex):
    return {ex.get(i)['quot']['kind']: i for i in ex.decls if ex.declkind[i] == 'quot'}
@case('Q1-quot-removed-mk-as-def', 'REJECTED', 'quot lines removed and Quot.mk exported as an (erased, never kernel-checked) definition')
def q1(ex, ctx):
    ql = quot_lines(ex)
    if 'ctor' not in ql: return None
    d = ex.get(ql['ctor'])['quot']; line = canon({'def': {'all': [d['name']], 'hints': {'regular': 1}, 'levelParams': d['levelParams'],
            'name': d['name'], 'safety': 'safe', 'type': d['type'], 'value': d['type']}})
    return ex.out({ql['ctor']: line}, delete={ql['type']})
@case('Q2-quot-lift-type-of-ind', 'REJECTED', 'the exported Quot.lift gets the type of Quot.ind (the kernel-added one differs: post-check)')
def q2(ex, ctx):
    ql = quot_lines(ex)
    if 'lift' not in ql or 'ind' not in ql: return None
    o = json.loads(json.dumps(ex.get(ql['lift']))); o['quot']['type'] = ex.get(ql['ind'])['quot']['type']
    pos = max(ql['lift'], ql['ind'])
    return ex.out({ql['lift']: b'', pos: ex.lines[pos] + canon(o)} if pos != ql['lift'] else {ql['lift']: canon(o)})
@case('Q3-quot-kinds-swapped', 'REJECTED', 'kinds of the exported Quot.lift and Quot.ind swapped')
def q3(ex, ctx):
    ql = quot_lines(ex)
    if 'lift' not in ql or 'ind' not in ql: return None
    a = json.loads(json.dumps(ex.get(ql['lift']))); b2 = json.loads(json.dumps(ex.get(ql['ind'])))
    a['quot']['kind'], b2['quot']['kind'] = 'ind', 'lift'
    return ex.out({ql['lift']: canon(a), ql['ind']: canon(b2)})
@case('Q4-quot-line-duplicated', 'REJECTED', 'the quot type line duplicated under a fresh name (a second quotient declaration)')
def q4(ex, ctx):
    ql = quot_lines(ex)
    if 'type' not in ql: return None
    b = B(ex); n = b.name('V06Quot2'); o = json.loads(json.dumps(ex.get(ql['type']))); o['quot']['name'] = n
    return ex.out(insert={len(ex.lines): b.lines + [canon(o)]})

# ---------------- K: definition holes (definition_names: only name/levelParams/type/safety compared, any body)
def hole_line(ex, ctx):
    for n in ctx.get('defs', []):
        i = find_decl(ex, n, 'def')
        if i is not None: return i
    return None
@case('K1-hole-other-body-same-theorems', 'ACCEPTED?', 'definition hole: body replaced by another closed term of the same type (theorems may break)')
def k1(ex, ctx):
    i = hole_line(ex, ctx)
    if i is None: return None
    o = json.loads(json.dumps(ex.get(i))); d = o['def']
    same = [j for j in ex.decls if j < i and ex.declkind[j] == 'def' and ex.get(j)['def']['type'] == d['type'] and j != i]
    if not same: return None
    d['value'] = ex.get(same[-1])['def']['value']; return ex.out({i: canon(o)})
@case('K2-hole-safety-partial', 'REJECTED', 'definition hole marked partial (safety is compared)')
def k2(ex, ctx):
    i = hole_line(ex, ctx)
    if i is None: return None
    o = json.loads(json.dumps(ex.get(i))); o['def']['safety'] = 'partial'; return ex.out({i: canon(o)})
@case('K3-hole-hints-opaque', 'ACCEPTED?', 'definition hole with reducibility hints "opaque" (hints are not compared for holes)')
def k3(ex, ctx):
    i = hole_line(ex, ctx)
    if i is None: return None
    o = json.loads(json.dumps(ex.get(i))); o['def']['hints'] = 'opaque'; return ex.out({i: canon(o)})
@case('K4-hole-body-uses-illegal-axiom', 'REJECTED', 'definition hole body := a fresh axiom of its type (holes are roots of the axiom check)')
def k4(ex, ctx):
    i = hole_line(ex, ctx)
    if i is None: return None
    o = json.loads(json.dumps(ex.get(i))); d = o['def']; b = B(ex); n = b.name('V06holeAx')
    b.raw({'axiom': {'isUnsafe': False, 'levelParams': d['levelParams'], 'name': n, 'type': d['type']}})
    c = b.expr('const', {'name': n, 'us': []}); d['value'] = c
    return ex.out({i: canon(o)}, insert={i: b.lines})
@case('K5-hole-as-theorem', 'REJECTED', 'definition hole exported as a theorem with the same type and value')
def k5(ex, ctx):
    i = hole_line(ex, ctx)
    if i is None: return None
    d = ex.get(i)['def']
    return ex.out({i: canon({'thm': {'all': d['all'], 'levelParams': d['levelParams'], 'name': d['name'], 'type': d['type'], 'value': d['value']}})})

# ---------------- L: log-line injection through declaration names (names are printed in kernel error messages; the
# wiring reads ccmp's combined output). Can only turn a rejection into "no verdict" (an ACCEPT needs ccmp rc=0).
def bogus_thm(ex, ctx, name):
    i = find_decl(ex, ctx['thm'], 'thm'); d = ex.get(i)['thm']; b = B(ex); n = b.name(name)
    b.raw({'thm': {'all': [n], 'levelParams': d['levelParams'], 'name': n, 'type': d['type'], 'value': d['type']}})
    return ex.out(insert={len(ex.lines): b.lines})
@case('L1-name-injects-error-line', 'REJECTED', 'an ill-typed extra theorem whose name contains a newline + "error: Lean default exited with 2" (injected first error line)')
def l1(ex, ctx): return bogus_thm(ex, ctx, 'V06inj\nerror: Lean default exited with 2\n')
@case('L2-name-injects-stack-overflow', 'REJECTED', 'an ill-typed extra theorem named "Stack overflow detected" (the wiring maps that text to no verdict)')
def l2(ex, ctx): return bogus_thm(ex, ctx, 'Stack overflow detected')
@case('L3-name-injects-gruszka-decline', 'REJECTED', 'ill-typed extra theorem whose name injects "error: gruszka (second kernel) exited with 2"')
def l3(ex, ctx): return bogus_thm(ex, ctx, 'x\nerror: gruszka (second kernel) exited with 2\n')
@case('L4-name-injects-success-lines', 'REJECTED', 'ill-typed extra theorem whose name injects the success lines ("Your solution is okay!", both kernels accept)')
def l4(ex, ctx): return bogus_thm(ex, ctx, 'x\nLean default kernel accepts the solution\ngruszka (second kernel) kernel accepts the solution\nYour solution is okay!\n')

def main():
    base, cfg, out = sys.argv[1], sys.argv[2], sys.argv[3]
    prefix = sys.argv[4] if len(sys.argv) > 4 else ''
    ex = Ex(open(base, 'rb').read()); c = json.load(open(cfg))
    ctx = {'thm': c['theorem_names'][0], 'targets': c['theorem_names'], 'defs': c.get('definition_names', [])}
    ctx['closure'] = closure_names(ex, c['theorem_names'])
    inds = [i for i in ex.decls if ex.declkind[i] == 'inductive']
    single = [i for i in inds if len(ex.get(i)['inductive']['types']) == 1 and ex.get(i)['inductive']['ctors']]
    ctx['ind'] = ex.decl_name(single[0])
    mut = [i for i in inds if len(ex.get(i)['inductive']['types']) > 1]
    ctx['mutual'] = ex.decl_name(mut[-1]) if mut else ctx['ind']
    nest = [i for i in inds if ex.get(i)['inductive']['types'][0]['numNested'] > 0]
    ctx['nested'] = ex.decl_name(nest[-1]) if nest else ex.decl_name(single[-1])
    os.makedirs(out, exist_ok=True); man = open(os.path.join(out, 'manifest.tsv'), 'a')
    for cid, pred, what, f in CASES:
        try:
            res = f(ex, ctx)
        except Exception as e:
            print(f'{cid}: skipped ({type(e).__name__}: {e})', file=sys.stderr); continue
        if res is None:
            print(f'{cid}: not applicable', file=sys.stderr); continue
        if isinstance(res, tuple):
            res, det = res; what2 = f'{what} [{det}]'
        else:
            what2 = what
        mid = prefix + cid
        open(os.path.join(out, mid + '.ndjson'), 'wb').write(res)
        man.write(f'{mid}\tseam\tX\tPRED={pred}; {what2}\n')
    man.close()

if __name__ == '__main__':
    main()

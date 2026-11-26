#!/usr/bin/env python3
"""xfuzz.py: structure-aware mutation of Lean 4 NDJSON exports (lean4export format 3.1.0).

  xfuzz.py gen BASE.export OUTDIR --ops OP[,OP...]|all --per-op N --seed S
      writes OUTDIR/<id>.ndjson for every mutant and OUTDIR/manifest.tsv (id, op, class, detail)
  xfuzz.py list            prints the operators (class, name, what it does, expected effect)

Operators work on the raw lines; a touched line is re-serialized canonically (sorted keys, no spaces, like Json.compress)
unless the operator's purpose is a non-canonical form. Untouched lines stay byte-identical. Every mutant is deterministic
in (base, op, seed, k)."""
import json, os, random, sys, hashlib, collections

def canon(o):
    return (json.dumps(o, sort_keys=True, separators=(',', ':'), ensure_ascii=False) + '\n').encode()

def ser(o, keyorder=None, sep=(',', ':'), dupfirst=None):
    """custom serializer: keyorder(dict)->list of keys; dupfirst: (key, value) emitted first in the TOP object"""
    def s(x, top=False):
        if isinstance(x, dict):
            ks = keyorder(x) if keyorder else sorted(x)
            parts = []
            if top and dupfirst is not None:
                parts.append(json.dumps(dupfirst[0], ensure_ascii=False) + sep[1] + s(dupfirst[1]))
            parts += [json.dumps(k, ensure_ascii=False) + sep[1] + s(x[k]) for k in ks]
            return '{' + sep[0].join(parts) + '}'
        if isinstance(x, list):
            return '[' + sep[0].join(s(v) for v in x) + ']'
        return json.dumps(x, ensure_ascii=False)
    return (s(o, True) + '\n').encode()

class Ex:
    def __init__(self, data):
        self.lines = data.split(b'\n')
        if self.lines and self.lines[-1] == b'':
            self.lines.pop()
        self.lines = [l + b'\n' for l in self.lines]
        self.obj = {}
        self.names, self.levels, self.exprs, self.decls = {}, {}, {}, []
        for i, l in enumerate(self.lines):
            if i == 0:
                continue
            try:
                o = self.get(i)
            except Exception:
                continue
            if not isinstance(o, dict):
                continue
            if 'in' in o:
                self.names[o['in']] = i
            elif 'il' in o:
                self.levels[o['il']] = i
            elif 'ie' in o:
                self.exprs[o['ie']] = i
            else:
                self.decls.append(i)
        self.declkind = {i: next(iter(self.get(i))) for i in self.decls}
    def get(self, i):
        if i not in self.obj:
            self.obj[i] = json.loads(self.lines[i])
        return self.obj[i]
    def name_str(self, idx, depth=0):
        if idx == 0 or depth > 50:
            return ''
        o = self.get(self.names[idx])
        if 'str' in o:
            p = self.name_str(o['str']['pre'], depth + 1)
            return (p + '.' if p else '') + o['str']['str']
        p = self.name_str(o['num']['pre'], depth + 1)
        return (p + '.' if p else '') + str(o['num']['i'])
    def decl_name(self, i):
        o = self.get(i); k = next(iter(o)); d = o[k]
        if k == 'inductive':
            return self.name_str(d['types'][0]['name'])
        return self.name_str(d['name'])
    def out(self, repl=None, insert=None, delete=None, tail=b''):
        """repl: {line: bytes}; insert: {line: [bytes,...]} inserted BEFORE line (len(lines) = append); delete: set"""
        repl = repl or {}; insert = insert or {}; delete = delete or set()
        res = []
        for i, l in enumerate(self.lines):
            for x in insert.get(i, []):
                res.append(x)
            if i in delete:
                continue
            res.append(repl.get(i, l))
        for x in insert.get(len(self.lines), []):
            res.append(x)
        return b''.join(res) + tail
    def max_expr(self):
        return max(self.exprs) if self.exprs else -1
    def max_name(self):
        return max(self.names) if self.names else 0

OPS = {}
def before(pool, line):
    """indices of `pool` (idx -> defining line) whose defining line is before `line`"""
    return sorted(k for k, li in pool.items() if li < line)
def pick(r, pool, line, extra=()):
    c = before(pool, line) + list(extra)
    return r.choice(c) if c else None
def op(cls, doc):
    def d(f):
        OPS[f.__name__] = (cls, doc, f); return f
    return d

def rnd_line(r, ex, pool):
    return r.choice(sorted(pool)) if pool else None

def data_lines(ex):
    return list(range(1, len(ex.lines)))

def target_decls(ex, targets):
    res = []
    for i in ex.decls:
        if ex.declkind[i] in ('thm', 'def', 'axiom', 'opaque') and ex.decl_name(i) in targets:
            res.append(i)
    return res

# ---------------------------------------------------------------- S: syntax / byte level
@op('S', 'one line re-serialized with spaces after , and : (valid JSON, non-canonical) -> same meaning')
def S_ws(r, ex, ctx):
    i = r.choice(data_lines(ex)); return ex.out({i: ser(ex.get(i), sep=(', ', ': '))}), f'line {i}'
@op('S', 'random whitespace (space/tab/CR/LF-free) inserted between JSON tokens of one line -> same meaning')
def S_ws_rand(r, ex, ctx):
    i = r.choice(data_lines(ex)); s = ser(ex.get(i)).decode().rstrip('\n'); out = []; instr = False; esc = False
    for c in s:
        out.append(c)
        if instr:
            if esc: esc = False
            elif c == '\\': esc = True
            elif c == '"': instr = False
        elif c == '"': instr = True
        if not instr and c in ',:{[' and r.random() < 0.5:
            out.append(r.choice([' ', '\t', '\r', '  ']))
    return ex.out({i: (''.join(out) + '\n').encode()}), f'line {i}'
@op('S', 'keys of every object of one line in random order -> same meaning (official TreeMap sorts)')
def S_keyperm(r, ex, ctx):
    i = r.choice(data_lines(ex))
    def ko(d):
        k = list(d); r.shuffle(k); return k
    return ex.out({i: ser(ex.get(i), keyorder=ko)}), f'line {i}'
@op('S', 'duplicate top-level key, first copy bogus, last copy real (JSON last-wins) -> same meaning in Lean Json')
def S_dupkey_lastwins(r, ex, ctx):
    i = r.choice(data_lines(ex)); o = ex.get(i); k = r.choice(sorted(o))
    bogus = 999999 if isinstance(o[k], int) else {"x": 1}
    return ex.out({i: ser(o, dupfirst=(k, bogus))}), f'line {i} key {k}'
@op('S', 'duplicate top-level key, first copy real, last copy bogus -> meaning changes (last wins)')
def S_dupkey_firstreal(r, ex, ctx):
    i = r.choice(data_lines(ex)); o = ex.get(i); k = r.choice(sorted(o))
    bogus = (o[k] + 1) if isinstance(o[k], int) else ({"x": 1} if isinstance(o[k], dict) else 0)
    s = ser(o).decode().rstrip('\n')
    s = s[:-1] + ',' + json.dumps(k) + ':' + json.dumps(bogus) + '}'
    return ex.out({i: (s + '\n').encode()}), f'line {i} key {k}'
NUMFMTS = ['{}.0', '{}e0', '{}E+0', '{}0e-1', '0{}', '-{}', '{} ', '+{}', '{}.', '0x{}', '{}e00']
@op('S', 'one integer of one line written in another JSON number syntax (5.0, 5e0, 50e-1, 05, -5, ...)')
def S_numfmt(r, ex, ctx):
    i = r.choice(data_lines(ex)); s = ex.lines[i].decode('utf-8', 'surrogateescape')
    import re
    ms = [m for m in re.finditer(r'(?<=[:\[,])(\d+)(?=[,\]}])', s)]
    if not ms:
        return None
    m = r.choice(ms); f = r.choice(NUMFMTS); v = m.group(1)
    rep = f.format(v) if f != '-{}' else ('-' + v)
    s2 = s[:m.start()] + rep + s[m.end():]
    return s2.encode('utf-8', 'surrogateescape'), f'line {i} {v} -> {rep}'
@op('S', 'a name/string literal re-written with \\u escapes (same string) or with a lone surrogate / escaped slash')
def S_escape(r, ex, ctx):
    pool = [i for i in data_lines(ex) if b'"str":"' in ex.lines[i] or b'"strVal"' in ex.lines[i]]
    if not pool:
        return None
    i = r.choice(pool); s = ex.lines[i].decode()
    key = '"str":"' if '"str":"' in s else '"strVal":"'
    a = s.index(key) + len(key); b = a
    while s[b] != '"':
        b += 2 if s[b] == '\\' else 1
    body = s[a:b]
    mode = r.choice(['uall', 'uone', 'lone_hi', 'lone_lo', 'slash', 'pair'])
    if mode == 'uall':
        nb = ''.join('\\u%04x' % ord(c) if ord(c) < 0x10000 else c for c in json.loads('"' + body + '"'))
    elif mode == 'uone' and body:
        c = body[0]; nb = ('\\u%04X' % ord(c) if ord(c) < 0x10000 else c) + body[1:]
    elif mode == 'lone_hi':
        nb = body + '\\ud800'
    elif mode == 'lone_lo':
        nb = body + '\\udc00'
    elif mode == 'slash':
        nb = body + '\\/'
    else:
        nb = body + '\\ud83d\\ude00'
    return ex.out({i: (s[:a] + nb + s[b:]).encode()}), f'line {i} {mode}'
@op('S', 'CRLF line ends on random lines (CR is JSON whitespace) -> same meaning')
def S_crlf(r, ex, ctx):
    ls = r.sample(data_lines(ex), min(20, len(ex.lines) - 1))
    return ex.out({i: ex.lines[i][:-1] + b'\r\n' for i in ls}), f'{len(ls)} lines'
@op('S', 'line terminators/whitespace variants: lone CR, form feed, vertical tab, NBSP, BOM at a data line start')
def S_badws(r, ex, ctx):
    i = r.choice(data_lines(ex)); w = r.choice([b'\r', b'\x0c', b'\x0b', '\u00a0'.encode(), '\ufeff'.encode()])
    pos = r.choice(['start', 'end'])
    l = ex.lines[i]
    return ex.out({i: (w + l) if pos == 'start' else (l[:-1] + w + b'\n')}), f'line {i} {w!r} {pos}'
@op('S', 'blank line inserted (middle / end) or final newline removed')
def S_blank(r, ex, ctx):
    m = r.choice(['mid', 'end', 'nofinal', 'twofinal'])
    if m == 'mid':
        i = r.choice(data_lines(ex)); return ex.out(insert={i: [b'\n']}), f'blank before line {i}'
    if m == 'end':
        return ex.out(insert={len(ex.lines): [b'\n']}), 'blank at end'
    if m == 'nofinal':
        return ex.out()[:-1], 'no final newline'
    return ex.out() + b'\n\n', 'two extra newlines'
@op('S', 'line starting with NUL inserted (official getLine/fgets returns "" there = EOF for the official reader)')
def S_nul_linestart(r, ex, ctx):
    m = r.choice(['end', 'mid'])
    i = len(ex.lines) if m == 'end' else r.choice(data_lines(ex))
    junk = r.choice([b'\x00\n', b'\x00garbage\n', b'\x00{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}\n'])
    return ex.out(insert={i: [junk]}), f'NUL line before line {i} ({m})'
@op('S', 'NUL byte after the JSON object of one line, followed by junk (official fgets/strlen truncates the line)')
def S_nul_midline(r, ex, ctx):
    i = r.choice(data_lines(ex)); l = ex.lines[i][:-1]
    junk = r.choice([b'', b'junk', b'x' * 100, b'{"bad":1}'])
    return ex.out({i: l + b'\x00' + junk + b'\n'}), f'line {i} junk {len(junk)}'
@op('S', 'item hidden behind NUL in the fgets 63-byte window: official sees 2 lines, other parsers 1 invalid line')
def S_nul_hide(r, ex, ctx):
    # take an expression line L1 (< 60 bytes) and the NEXT line L2; emit L1 NUL pad L2 on one line
    pool = [i for i in data_lines(ex)[:-1] if len(ex.lines[i]) < 60]
    if not pool:
        return None
    i = r.choice(pool); l1 = ex.lines[i][:-1]; l2 = ex.lines[i + 1]
    pad = b'P' * (63 - len(l1) - 1)
    return ex.out({i: l1 + b'\x00' + pad + l2}, delete={i + 1}), f'lines {i},{i+1} merged behind NUL'
@op('S', 'raw control character (TAB/0x01/0x1f) inside a JSON string (invalid JSON)')
def S_ctrl(r, ex, ctx):
    pool = [i for i in data_lines(ex) if b'"str":"' in ex.lines[i]]
    if not pool:
        return None
    i = r.choice(pool); l = ex.lines[i]; a = l.index(b'"str":"') + 7
    c = r.choice([b'\t', b'\x01', b'\x1f', b'\x7f'])
    return ex.out({i: l[:a] + c + l[a:]}), f'line {i} ctrl {c!r}'
@op('S', 'invalid UTF-8 inside a name string (overlong, lone continuation, surrogate encoding, truncated sequence)')
def S_badutf8(r, ex, ctx):
    pool = [i for i in data_lines(ex) if b'"str":"' in ex.lines[i]]
    if not pool:
        return None
    i = r.choice(pool); l = ex.lines[i]; a = l.index(b'"str":"') + 7
    c = r.choice([b'\xc0\x80', b'\x80', b'\xed\xa0\x80', b'\xe2\x82', b'\xff', b'\xf4\x90\x80\x80'])
    return ex.out({i: l[:a] + c + l[a:]}), f'line {i} bytes {c!r}'
@op('S', 'trailing garbage / second object / non-object JSON value on one line')
def S_garbage(r, ex, ctx):
    i = r.choice(data_lines(ex)); l = ex.lines[i][:-1]
    m = r.choice(['tail', 'twoobj', 'array', 'number', 'string', 'null', 'comma'])
    nl = {'tail': l + b'x', 'twoobj': l + l, 'array': b'[' + l + b']', 'number': b'5', 'string': b'"x"', 'null': b'null',
          'comma': l + b','}[m]
    return ex.out({i: nl + b'\n'}), f'line {i} {m}'
@op('S', 'metadata line dropped / duplicated / replaced by garbage / first item moved to line 0')
def S_meta(r, ex, ctx):
    m = r.choice(['drop', 'dup', 'garbage', 'empty', 'item0', 'nul'])
    if m == 'drop':
        return ex.out(delete={0}), m
    if m == 'dup':
        return ex.out(insert={1: [ex.lines[0]]}), m
    if m == 'garbage':
        return ex.out({0: b'this is not json\n'}), m
    if m == 'empty':
        return ex.out({0: b'\n'}), m
    if m == 'nul':
        return ex.out({0: b'\x00\n'}), m
    return ex.out({0: b''}), m   # item 1 becomes the first (skipped) line
@op('S', 'file truncated at a random byte offset')
def S_truncate(r, ex, ctx):
    b = ex.out(); k = r.randrange(len(ex.lines[0]), len(b)); return b[:k], f'cut at {k}/{len(b)}'
@op('S', 'an unused extra definition holding a string literal longer than the 8 MiB read block (chunk carry path)')
def S_longline(r, ex, ctx):
    n = ex.max_name() + 1; e = ex.max_expr() + 1
    size = r.choice([8 * 1024 * 1024 + 7, 9 * 1024 * 1024, 17 * 1024 * 1024])
    lines = [canon({"in": n, "str": {"pre": 0, "str": "V06LongStringDef"}})]
    # need String type: find expr const String
    sidx = None
    for k, li in ex.exprs.items():
        o = ex.get(li)
        if 'const' in o and ex.name_str(o['const']['name']) == 'String' and o['const']['us'] == []:
            sidx = k; break
    if sidx is None:
        return None
    lines.append(canon({"ie": e, "strVal": "a" * size}))
    lines.append(canon({"def": {"all": [n], "hints": {"regular": 1}, "levelParams": [], "name": n, "safety": "safe", "type": sidx, "value": e}}))
    return ex.out(insert={len(ex.lines): lines}), f'string of {size} bytes'

# ---------------------------------------------------------------- I: index level
def remap_refs(o, emap=None, nmap=None, lmap=None):
    """rewrite every index reference in an item object (not its own binding index)"""
    E = (lambda x: emap.get(x, x)) if emap else (lambda x: x)
    N = (lambda x: nmap.get(x, x)) if nmap else (lambda x: x)
    L = (lambda x: lmap.get(x, x)) if lmap else (lambda x: x)
    o = json.loads(json.dumps(o))
    if 'in' in o:
        o['in'] = N(o['in'])
        d = o.get('str') or o.get('num'); d['pre'] = N(d['pre'])
    elif 'il' in o:
        o['il'] = L(o['il'])
        if 'succ' in o: o['succ'] = L(o['succ'])
        if 'max' in o: o['max'] = [L(x) for x in o['max']]
        if 'imax' in o: o['imax'] = [L(x) for x in o['imax']]
        if 'param' in o: o['param'] = N(o['param'])
    elif 'ie' in o:
        o['ie'] = E(o['ie'])
        k = [x for x in o if x != 'ie'][0]; d = o[k]
        if k == 'sort': o[k] = L(d)
        elif k == 'const': d['name'] = N(d['name']); d['us'] = [L(x) for x in d['us']]
        elif k == 'app': d['fn'] = E(d['fn']); d['arg'] = E(d['arg'])
        elif k in ('lam', 'forallE'): d['name'] = N(d['name']); d['type'] = E(d['type']); d['body'] = E(d['body'])
        elif k == 'letE': d['name'] = N(d['name']); d['type'] = E(d['type']); d['value'] = E(d['value']); d['body'] = E(d['body'])
        elif k == 'proj': d['typeName'] = N(d['typeName']); d['struct'] = E(d['struct'])
        elif k == 'mdata': d['expr'] = E(d['expr'])
    else:
        k = next(iter(o)); d = o[k]
        def cv(c):
            c['name'] = N(c['name']); c['levelParams'] = [N(x) for x in c['levelParams']]; c['type'] = E(c['type'])
            if 'value' in c: c['value'] = E(c['value'])
            if 'all' in c: c['all'] = [N(x) for x in c['all']]
        if k == 'inductive':
            for t in d['types']:
                cv(t); t['ctors'] = [N(x) for x in t['ctors']]
            for c in d['ctors']:
                cv(c); c['induct'] = N(c['induct'])
            for rc in d['recs']:
                cv(rc)
                for ru in rc['rules']:
                    ru['ctor'] = N(ru['ctor']); ru['rhs'] = E(ru['rhs'])
        else:
            cv(d)
    return o

@op('I', 'all expression indices renumbered monotonically with gaps (i -> 2i+1): sparse but valid -> same meaning')
def I_sparse(r, ex, ctx):
    emap = {k: 2 * k + 1 for k in ex.exprs}
    return ex.out({i: canon(remap_refs(ex.get(i), emap=emap)) for i in data_lines(ex)}), 'exprs i->2i+1'
@op('I', 'name indices renumbered by a random permutation, lines kept in order (non-monotone, defined before use) -> same meaning')
def I_perm_names(r, ex, ctx):
    ks = sorted(ex.names); vs = ks[:]; r.shuffle(vs); nmap = dict(zip(ks, vs))
    return ex.out({i: canon(remap_refs(ex.get(i), nmap=nmap)) for i in data_lines(ex)}), 'names permuted'
@op('I', 'level indices renumbered by a random permutation -> same meaning')
def I_perm_levels(r, ex, ctx):
    ks = sorted(ex.levels); vs = ks[:]; r.shuffle(vs); lmap = dict(zip(ks, vs))
    return ex.out({i: canon(remap_refs(ex.get(i), lmap=lmap)) for i in data_lines(ex)}), 'levels permuted'
@op('I', 'an expression index bound twice (second line with other content)')
def I_rebind(r, ex, ctx):
    k = r.choice(sorted(ex.exprs)); j = r.choice(sorted(ex.exprs))
    o = json.loads(json.dumps(ex.get(ex.exprs[j]))); o['ie'] = k
    pos = r.choice([ex.exprs[k] + 1, len(ex.lines)])
    return ex.out(insert={pos: [canon(o)]}), f'ie {k} rebound with content of {j}'
@op('I', 'an expression line moved after its first use (forward reference)')
def I_forward(r, ex, ctx):
    k = r.choice(sorted(ex.exprs)); li = ex.exprs[k]
    users = [i for i in range(li + 1, min(len(ex.lines), li + 4000)) if f':{k},'.encode() in ex.lines[i] or f':{k}}}'.encode() in ex.lines[i] or f'[{k},'.encode() in ex.lines[i] or f',{k}]'.encode() in ex.lines[i] or f'[{k}]'.encode() in ex.lines[i]]
    if not users:
        return None
    u = users[0]
    return ex.out(insert={u + 1: [ex.lines[li]]}, delete={li}), f'ie {k} moved after line {u}'
HUGE = [2 ** 32, 2 ** 63, 2 ** 64, 10 ** 18, 10 ** 18 - 1, 2 ** 64 * 3, 10 ** 30]
@op('I', 'one index reference replaced by k + 2^32 / 2^63 / 2^64 / 10^18 / ... (aliasing if any reader wraps)')
def I_huge(r, ex, ctx):
    i = r.choice(data_lines(ex)); s = ex.lines[i].decode('utf-8', 'surrogateescape')
    import re
    ms = [m for m in re.finditer(r'(?<=[:\[,])(\d+)(?=[,\]}])', s)]
    if not ms:
        return None
    m = r.choice(ms); h = r.choice(HUGE); v = int(m.group(1)) + h
    return (s[:m.start()] + str(v) + s[m.end():]).encode('utf-8', 'surrogateescape'), f'line {i} {m.group(1)} -> {v}'
@op('I', 'an expression duplicated under a fresh index and one reference redirected to the copy -> same meaning')
def I_alias(r, ex, ctx):
    k = r.choice(sorted(ex.exprs)); li = ex.exprs[k]; new = ex.max_expr() + 1
    o = json.loads(json.dumps(ex.get(li))); o['ie'] = new
    nl = set(ex.names.values())
    users = [i for i in range(li + 1, len(ex.lines)) if i not in nl][:4000]
    users = [i for i in users if (f':{k},'.encode() in ex.lines[i] or f':{k}}}'.encode() in ex.lines[i])]
    if not users:
        return None
    u = r.choice(users); s = ex.lines[u].decode()
    s2 = s.replace(f':{k},', f':{new},', 1) if f':{k},' in s else s.replace(f':{k}}}', f':{new}}}', 1)
    return ex.out({u: s2.encode()}, insert={u: [canon(o)]}), f'ie {k} aliased as {new} in line {u}'

# ---------------------------------------------------------------- D: declaration level
@op('D', 'one declaration line deleted')
def D_delete(r, ex, ctx):
    i = r.choice(ex.decls); return ex.out(delete={i}), f'deleted {ex.declkind[i]} {ex.decl_name(i)}'
@op('D', 'one declaration line duplicated (at the end)')
def D_dup(r, ex, ctx):
    i = r.choice(ex.decls); return ex.out(insert={len(ex.lines): [ex.lines[i]]}), f'dup {ex.decl_name(i)}'
@op('D', 'declaration lines moved to the end of the file in reverse/random order (constOrder changes) -> same meaning')
def D_reorder(r, ex, ctx):
    ds = list(ex.decls); m = r.choice(['reverse', 'shuffle'])
    if m == 'reverse': ds.reverse()
    else: r.shuffle(ds)
    return ex.out(insert={len(ex.lines): [ex.lines[i] for i in ds]}, delete=set(ex.decls)), m
@op('D', 'declaration kind changed (thm->def/opaque/axiom, def->thm/opaque/axiom, opaque->def, axiom->thm)')
def D_kind(r, ex, ctx):
    pool = [i for i in ex.decls if ex.declkind[i] in ('thm', 'def', 'opaque', 'axiom')]
    i = r.choice(pool); o = ex.get(i); k = ex.declkind[i]; d = json.loads(json.dumps(o[k]))
    tgt = r.choice([x for x in ('thm', 'def', 'opaque', 'axiom') if x != k])
    if 'value' not in d:
        d['value'] = pick(r, ex.exprs, i)
    if 'all' not in d:
        d['all'] = [d['name']]
    if tgt == 'axiom':
        nd = {'name': d['name'], 'levelParams': d['levelParams'], 'type': d['type'], 'isUnsafe': False}
    elif tgt == 'thm':
        nd = {k2: d[k2] for k2 in ('name', 'levelParams', 'type', 'value', 'all')}
    elif tgt == 'def':
        nd = {k2: d[k2] for k2 in ('name', 'levelParams', 'type', 'value', 'all')}
        nd['hints'] = r.choice(['opaque', 'abbrev', {'regular': 1}]); nd['safety'] = 'safe'
    else:
        nd = {k2: d[k2] for k2 in ('name', 'levelParams', 'type', 'value', 'all')}; nd['isUnsafe'] = False
    return ex.out({i: canon({tgt: nd})}), f'{k}->{tgt} {ex.decl_name(i)}'
@op('D', 'levelParams edited (drop / add fresh / swap / rename) on one declaration')
def D_lparams(r, ex, ctx):
    pool = [i for i in ex.decls if ex.declkind[i] != 'inductive']
    i = r.choice(pool); o = json.loads(json.dumps(ex.get(i))); k = ex.declkind[i]; d = o[k]
    lp = d['levelParams']; m = r.choice(['drop', 'add', 'swap', 'rename'])
    other = pick(r, ex.names, i)
    if m == 'drop' and lp: lp.pop(r.randrange(len(lp)))
    elif m == 'swap' and len(lp) >= 2: lp[0], lp[1] = lp[1], lp[0]
    elif m == 'rename' and lp: lp[r.randrange(len(lp))] = other
    else: lp.append(other); m = 'add'
    return ex.out({i: canon(o)}), f'{m} {ex.decl_name(i)}'
@op('D', 'the `all` list of one declaration edited (drop / add a name / reorder)')
def D_all(r, ex, ctx):
    pool = [i for i in ex.decls if ex.declkind[i] in ('thm', 'def', 'opaque')]
    i = r.choice(pool); o = json.loads(json.dumps(ex.get(i))); d = o[ex.declkind[i]]
    m = r.choice(['drop', 'add', 'dup'])
    if m == 'drop': d['all'] = []
    elif m == 'add': d['all'].append(pick(r, ex.names, i))
    else: d['all'] = d['all'] * 2
    return ex.out({i: canon(o)}), f'{m} {ex.decl_name(i)}'
@op('D', 'definition safety / hints / isUnsafe flags changed on one declaration')
def D_flags(r, ex, ctx):
    i = r.choice(ex.decls); o = json.loads(json.dumps(ex.get(i))); k = ex.declkind[i]; d = o[k]
    if k == 'def':
        m = r.choice(['safety', 'hints'])
        if m == 'safety': d['safety'] = r.choice([x for x in ('safe', 'unsafe', 'partial') if x != d['safety']]); det = d['safety']
        else: d['hints'] = r.choice(['opaque', 'abbrev', {'regular': 0}, {'regular': 4294967297}]); det = str(d['hints'])
    elif k in ('axiom', 'opaque'):
        d['isUnsafe'] = not d.get('isUnsafe', False); det = 'isUnsafe'
    elif k == 'inductive':
        part = r.choice(['types', 'ctors', 'recs']); x = r.choice(d[part]); x['isUnsafe'] = not x['isUnsafe']; det = part + '.isUnsafe'
    elif k == 'quot':
        d['kind'] = r.choice([x for x in ('type', 'ctor', 'lift', 'ind') if x != d['kind']]); det = 'kind ' + d['kind']
    else:
        return None
    return ex.out({i: canon(o)}), f'{k} {ex.decl_name(i)} {det}'
@op('D', 'inductive record field edited (numParams/numIndices/numNested +-1, isRec/isReflexive flip, ctors/all lists)')
def D_induct(r, ex, ctx):
    pool = [i for i in ex.decls if ex.declkind[i] == 'inductive']
    if not pool: return None
    i = r.choice(pool); o = json.loads(json.dumps(ex.get(i))); t = r.choice(o['inductive']['types'])
    f = r.choice(['numParams', 'numIndices', 'numNested', 'isRec', 'isReflexive', 'ctors_rev', 'ctors_drop', 'all_drop'])
    if f in ('isRec', 'isReflexive'): t[f] = not t[f]
    elif f == 'ctors_rev': t['ctors'] = t['ctors'][::-1]
    elif f == 'ctors_drop': t['ctors'] = t['ctors'][:-1]
    elif f == 'all_drop': t['all'] = t['all'][:-1]
    else: t[f] = max(0, t[f] + r.choice([-1, 1]))
    return ex.out({i: canon(o)}), f'{ex.decl_name(i)} {f}'
@op('D', 'constructor record field edited (cidx, numFields, numParams, induct, type)')
def D_ctor(r, ex, ctx):
    pool = [i for i in ex.decls if ex.declkind[i] == 'inductive' and ex.get(i)['inductive']['ctors']]
    if not pool: return None
    i = r.choice(pool); o = json.loads(json.dumps(ex.get(i))); c = r.choice(o['inductive']['ctors'])
    f = r.choice(['cidx', 'numFields', 'numParams', 'induct', 'type'])
    if f == 'induct': c[f] = pick(r, ex.names, i)
    elif f == 'type': c[f] = pick(r, ex.exprs, i)
    else: c[f] = max(0, c[f] + r.choice([-1, 1]))
    return ex.out({i: canon(o)}), f'{ex.decl_name(i)} ctor {f}'
@op('D', 'recursor record edited (numMotives/numMinors/numIndices/numParams, k flip, rules reordered, rule nfields/ctor/rhs)')
def D_rec(r, ex, ctx):
    pool = [i for i in ex.decls if ex.declkind[i] == 'inductive' and ex.get(i)['inductive']['recs']]
    if not pool: return None
    i = r.choice(pool); o = json.loads(json.dumps(ex.get(i))); rc = r.choice(o['inductive']['recs'])
    f = r.choice(['numMotives', 'numMinors', 'numIndices', 'numParams', 'k', 'rules_rev', 'nfields', 'rule_ctor', 'rule_rhs', 'rules_drop'])
    if f == 'k': rc['k'] = not rc['k']
    elif f == 'rules_rev': rc['rules'] = rc['rules'][::-1]
    elif f == 'rules_drop': rc['rules'] = rc['rules'][:-1]
    elif f in ('nfields', 'rule_ctor', 'rule_rhs'):
        if not rc['rules']: return None
        ru = r.choice(rc['rules'])
        if f == 'nfields': ru['nfields'] = max(0, ru['nfields'] + r.choice([-1, 1]))
        elif f == 'rule_ctor': ru['ctor'] = pick(r, ex.names, i)
        else: ru['rhs'] = pick(r, ex.exprs, i)
    else: rc[f] = max(0, rc[f] + r.choice([-1, 1]))
    return ex.out({i: canon(o)}), f'{ex.decl_name(i)} rec {f}'
@op('D', 'type and value of one theorem/definition swapped, or value replaced by another declaration\'s value')
def D_tv(r, ex, ctx):
    pool = [i for i in ex.decls if ex.declkind[i] in ('thm', 'def', 'opaque')]
    i = r.choice(pool); o = json.loads(json.dumps(ex.get(i))); d = o[ex.declkind[i]]
    if r.random() < 0.5:
        d['type'], d['value'] = d['value'], d['type']; m = 'swap'
    else:
        j = r.choice([x for x in pool if x < i] or [i]); d['value'] = ex.get(j)[ex.declkind[j]]['value']; m = 'value of ' + ex.decl_name(j)
    return ex.out({i: canon(o)}), f'{ex.decl_name(i)} {m}'

# ---------------------------------------------------------------- E: expression level
def expr_pool(ex, kinds):
    return [k for k, li in ex.exprs.items() if any(f'"{kd}"'.encode() in ex.lines[li][:60] for kd in kinds)]
@op('E', 'one expression node mutated: bvar +-1, sort level, const name/levels, app fn/arg swap or arg replaced, lam<->forallE, binder info/name, letE nondep/value, proj idx/typeName, nat/str literal')
def E_node(r, ex, ctx):
    k = r.choice(sorted(ex.exprs)); li = ex.exprs[k]; o = json.loads(json.dumps(ex.get(li)))
    kind = [x for x in o if x != 'ie'][0]; d = o[kind]; det = kind
    lt = [x for x in ex.exprs if x < k]
    if kind == 'bvar': o['bvar'] = max(0, d + r.choice([-1, 1]))
    elif kind == 'sort': o['sort'] = pick(r, ex.levels, li, [0]); det += ' level'
    elif kind == 'const':
        m = r.choice(['name', 'us_drop', 'us_add', 'us_swap'])
        if m == 'name': d['name'] = pick(r, ex.names, li)
        elif m == 'us_drop' and d['us']: d['us'].pop()
        elif m == 'us_swap' and len(d['us']) >= 2: d['us'] = d['us'][::-1]
        else: d['us'].append(pick(r, ex.levels, li, [0])); m = 'us_add'
        det += ' ' + m
    elif kind == 'app':
        m = r.choice(['swap', 'arg', 'fn'])
        if m == 'swap': d['fn'], d['arg'] = d['arg'], d['fn']
        elif lt: d[m] = r.choice(lt)
        det += ' ' + m
    elif kind in ('lam', 'forallE'):
        m = r.choice(['flip', 'bi', 'name', 'type', 'body'])
        if m == 'flip': o = {'ie': k, ('forallE' if kind == 'lam' else 'lam'): d}
        elif m == 'bi': d['binderInfo'] = r.choice([x for x in ('default', 'implicit', 'strictImplicit', 'instImplicit') if x != d['binderInfo']])
        elif m == 'name': d['name'] = pick(r, ex.names, li)
        elif lt: d[m] = r.choice(lt)
        det += ' ' + m
    elif kind == 'letE':
        m = r.choice(['nondep', 'value', 'type'])
        if m == 'nondep': d['nondep'] = not d['nondep']
        elif lt: d[m] = r.choice(lt)
        det += ' ' + m
    elif kind == 'proj':
        m = r.choice(['idx', 'typeName'])
        if m == 'idx': d['idx'] = max(0, d['idx'] + r.choice([-1, 1, 1000]))
        else: d['typeName'] = pick(r, ex.names, li)
        det += ' ' + m
    elif kind == 'natVal':
        o['natVal'] = str(max(0, int(d) + r.choice([-1, 1, 2 ** 64])))
    elif kind == 'strVal':
        o['strVal'] = d + r.choice(['x', '\u0000', '\ud7ff'])
    elif kind == 'mdata':
        o['mdata']['data'] = {'k': {'ofNat': 1}}
    return ex.out({li: canon(o)}), f'ie {k} {det}'
@op('E', 'an expression used by a declaration wrapped in an mdata node (kernel ignores mdata; comparison does not)')
def E_mdata(r, ex, ctx):
    i = r.choice(ex.decls); o = json.loads(json.dumps(ex.get(i))); k = ex.declkind[i]
    if k == 'inductive': return None
    d = o[k]; f = r.choice([x for x in ('type', 'value') if x in d]); new = ex.max_expr() + 1
    md = canon({'ie': new, 'mdata': {'data': {}, 'expr': d[f]}}); d[f] = new
    return ex.out({i: canon(o)}, insert={i: [md]}), f'{ex.decl_name(i)} {f} wrapped'
@op('E', 'a level line mutated (succ<->max, param renamed, max operands swapped, imax<->max)')
def E_level(r, ex, ctx):
    if not ex.levels: return None
    k = r.choice(sorted(ex.levels)); li = ex.levels[k]; o = json.loads(json.dumps(ex.get(li)))
    kind = [x for x in o if x != 'il'][0]
    if kind == 'param': o['param'] = pick(r, ex.names, li)
    elif kind in ('max', 'imax'):
        m = r.choice(['swap', 'flip'])
        if m == 'swap': o[kind] = o[kind][::-1]
        else: o = {'il': k, ('imax' if kind == 'max' else 'max'): o[kind]}
    else: o = {'il': k, 'max': [o['succ'], o['succ']]}
    return ex.out({li: canon(o)}), f'il {k} {kind}'
@op('E', 'a name string edited (affects every use of that name: constants, binders, level params)')
def E_name(r, ex, ctx):
    k = r.choice(sorted(ex.names)); li = ex.names[k]; o = json.loads(json.dumps(ex.get(li)))
    if 'str' in o: o['str']['str'] = o['str']['str'] + r.choice(['\'', 'x', '\u200b'])
    else: o['num']['i'] += 1
    return ex.out({li: canon(o)}), f'in {k} {ex.name_str(k)}'

# ---------------------------------------------------------------- C: comparator level (needs ctx targets)
def thm_type(ex, i):
    return ex.get(i)[ex.declkind[i]]['type']
@op('C', 'a target theorem\'s statement replaced by another target\'s statement')
def C_stmt_swap(r, ex, ctx):
    ts = target_decls(ex, ctx['targets'])
    if len(ts) < 2: return None
    a, b = r.sample(ts, 2); o = json.loads(json.dumps(ex.get(a))); o[ex.declkind[a]]['type'] = thm_type(ex, b)
    return ex.out({a: canon(o)}), f'{ex.decl_name(a)} gets type of {ex.decl_name(b)}'
@op('C', 'a fresh axiom with a target\'s statement added, the target proved by it (kernel-valid, illegal axiom)')
def C_axiom_used(r, ex, ctx):
    ts = [i for i in target_decls(ex, ctx['targets']) if ex.declkind[i] == 'thm']
    if not ts: return None
    a = r.choice(ts); d = ex.get(a)['thm']; n = ex.max_name() + 1; e = ex.max_expr() + 1
    us = []  # level params of the target as levels
    lines = [canon({'in': n, 'str': {'pre': 0, 'str': r.choice(['V06fake', 'V06fake', 'V06fake', 'propext'])}})]
    lvl_lines = []; L = (max(ex.levels) + 1) if ex.levels else 1
    for p in d['levelParams']:
        lvl_lines.append(canon({'il': L, 'param': p})); us.append(L); L += 1
    lines += lvl_lines
    lines.append(canon({'axiom': {'isUnsafe': False, 'levelParams': d['levelParams'], 'name': n, 'type': d['type']}}))
    lines.append(canon({'ie': e, 'const': {'name': n, 'us': us}}))
    o = json.loads(json.dumps(ex.get(a))); o['thm']['value'] = e
    return ex.out({a: canon(o)}, insert={a: lines}), f'{ex.decl_name(a)} := axiom'
@op('C', 'a fresh unused axiom of type False added (outside the closure of the targets)')
def C_axiom_unused(r, ex, ctx):
    fl = None
    for k, li in ex.exprs.items():
        o = ex.get(li)
        if 'const' in o and ex.name_str(o['const']['name']) == 'False': fl = k; break
    if fl is None: return None
    n = ex.max_name() + 1
    return ex.out(insert={len(ex.lines): [canon({'in': n, 'str': {'pre': 0, 'str': 'V06unusedFalse'}}),
        canon({'axiom': {'isUnsafe': False, 'levelParams': [], 'name': n, 'type': fl}})]}), 'unused axiom False'
@op('C', 'a target removed from the export or renamed')
def C_target_missing(r, ex, ctx):
    ts = target_decls(ex, ctx['targets'])
    if not ts: return None
    a = r.choice(ts)
    if r.random() < 0.5:
        return ex.out(delete={a}), f'deleted {ex.decl_name(a)}'
    o = json.loads(json.dumps(ex.get(a))); n = ex.max_name() + 1; o[ex.declkind[a]]['name'] = n
    if 'all' in o[ex.declkind[a]]: o[ex.declkind[a]]['all'] = [n]
    return ex.out({a: canon(o)}, insert={a: [canon({'in': n, 'str': {'pre': 0, 'str': 'V06renamed'}})]}), f'renamed {ex.decl_name(a)}'
@op('C', 'a definition in the closure of a target statement gets another body (a value of another def of the same type if any, else random)')
def C_def_closure(r, ex, ctx):
    ts = target_decls(ex, ctx['targets'])
    defs = [i for i in ex.decls if ex.declkind[i] == 'def']
    if not ts or not defs: return None
    # constants used by target types (one level deep, by scanning expr lines)
    used = set()
    def walk(k, depth=0):
        if depth > 200 or k not in ex.exprs: return
        o = ex.get(ex.exprs[k]); kind = [x for x in o if x != 'ie'][0]; d = o[kind]
        if kind == 'const': used.add(d['name']); return
        if kind == 'app': walk(d['fn'], depth + 1); walk(d['arg'], depth + 1)
        elif kind in ('lam', 'forallE'): walk(d['type'], depth + 1); walk(d['body'], depth + 1)
        elif kind == 'letE': walk(d['type'], depth + 1); walk(d['value'], depth + 1); walk(d['body'], depth + 1)
        elif kind == 'mdata': walk(d['expr'], depth + 1)
        elif kind == 'proj': walk(d['struct'], depth + 1)
    for t in ts: walk(thm_type(ex, t))
    cand = [i for i in defs if ex.get(i)['def']['name'] in used]
    if not cand: return None
    a = r.choice(cand); o = json.loads(json.dumps(ex.get(a))); d = o['def']
    same = [j for j in defs if j != a and ex.get(j)['def']['type'] == d['type']]
    same = [j for j in same if j < a]
    d['value'] = ex.get(r.choice(same))['def']['value'] if same else pick(r, ex.exprs, a)
    return ex.out({a: canon(o)}), f'{ex.decl_name(a)} body changed'

# ---------------------------------------------------------------- R: re-serialization (meaning-preserving encodings)
def line_refs(o):
    """(names, levels, exprs) referenced by an item object (excluding its own binding index)"""
    N, L, E = set(), set(), set()
    def cv(c):
        N.add(c['name']); N.update(c['levelParams']); E.add(c['type'])
        if 'value' in c: E.add(c['value'])
        if 'all' in c: N.update(c['all'])
    if 'in' in o:
        d = o.get('str') or o.get('num'); N.add(d['pre'])
    elif 'il' in o:
        for k in ('succ',):
            if k in o: L.add(o[k])
        for k in ('max', 'imax'):
            if k in o: L.update(o[k])
        if 'param' in o: N.add(o['param'])
    elif 'ie' in o:
        k = [x for x in o if x != 'ie'][0]; d = o[k]
        if k == 'sort': L.add(d)
        elif k == 'const': N.add(d['name']); L.update(d['us'])
        elif k == 'app': E.update([d['fn'], d['arg']])
        elif k in ('lam', 'forallE'): N.add(d['name']); E.update([d['type'], d['body']])
        elif k == 'letE': N.add(d['name']); E.update([d['type'], d['value'], d['body']])
        elif k == 'proj': N.add(d['typeName']); E.add(d['struct'])
        elif k == 'mdata': E.add(d['expr'])
    else:
        k = next(iter(o)); d = o[k]
        if k == 'inductive':
            for t in d['types']: cv(t); N.update(t['ctors'])
            for c in d['ctors']: cv(c); N.add(c['induct'])
            for rc in d['recs']:
                cv(rc)
                for ru in rc['rules']: N.add(ru['ctor']); E.add(ru['rhs'])
        else:
            cv(d)
    N.discard(0); L.discard(0)
    return N, L, E
@op('R', 'all data lines in a random topological order (every index still defined before use) -> same meaning')
def R_toposhuffle(r, ex, ctx):
    import heapq
    n = len(ex.lines); deps = {}; users = collections.defaultdict(list); indeg = {}
    for i in range(1, n):
        o = ex.get(i); N, L, E = line_refs(o)
        ds = set(ex.names[x] for x in N if x in ex.names) | set(ex.levels[x] for x in L if x in ex.levels) | set(ex.exprs[x] for x in E if x in ex.exprs)
        ds.discard(i); indeg[i] = len(ds)
        for d in ds: users[d].append(i)
    pq = [(r.random(), i) for i in range(1, n) if indeg[i] == 0]; heapq.heapify(pq); order = []
    while pq:
        _, i = heapq.heappop(pq); order.append(i)
        for u in users[i]:
            indeg[u] -= 1
            if indeg[u] == 0: heapq.heappush(pq, (r.random(), u))
    if len(order) != n - 1: return None
    return ex.lines[0] + b''.join(ex.lines[i] for i in order), f'{len(order)} lines reordered'
@op('R', 'shared subexpressions un-shared: 50 random multiply-used expressions copied once per user -> same meaning')
def R_unshare(r, ex, ctx):
    cnt = collections.Counter(); first_user = {}
    for i in range(1, len(ex.lines)):
        o = ex.get(i)
        if 'ie' in o:
            for e in line_refs(o)[2]: cnt[e] += 1
    shared = [e for e, c in cnt.items() if c >= 2 and e in ex.exprs]
    if not shared: return None
    pick = set(r.sample(shared, min(50, len(shared)))); nxt = ex.max_expr() + 1
    repl = {}; ins = collections.defaultdict(list)
    for i in range(1, len(ex.lines)):
        o = ex.get(i)
        if 'ie' not in o: continue
        k = [x for x in o if x != 'ie'][0]; d = o[k]
        refs = {'app': ('fn', 'arg'), 'lam': ('type', 'body'), 'forallE': ('type', 'body'), 'letE': ('type', 'value', 'body'),
                'proj': ('struct',), 'mdata': ('expr',)}.get(k, ())
        o2 = None
        for f in refs:
            if d[f] in pick:
                if o2 is None: o2 = json.loads(json.dumps(o))
                cp = json.loads(json.dumps(ex.get(ex.exprs[d[f]]))); cp['ie'] = nxt
                ins[i].append(canon(cp)); o2[k][f] = nxt; nxt += 1
        if o2 is not None: repl[i] = canon(o2)
    return ex.out(repl, insert=dict(ins)), f'{len(pick)} shared exprs unshared'

def renumber_dense(ex2):
    """renumber names/levels/exprs of a parsed export densely in file order (canonical numbering, FastParse fast path)"""
    nmap, lmap, emap = {0: 0}, {0: 0}, {}
    for i in range(1, len(ex2.lines)):
        o = ex2.get(i)
        if 'in' in o: nmap[o['in']] = len(nmap)
        elif 'il' in o: lmap[o['il']] = len(lmap)
        elif 'ie' in o: emap[o['ie']] = len(emap)
    return ex2.lines[0] + b''.join(canon(remap_refs(ex2.get(i), emap=emap, nmap=nmap, lmap=lmap)) for i in range(1, len(ex2.lines)))
@op('R', 'random topological order + dense renumbering in the new order (canonical-looking, different file) -> same meaning')
def R_topo_dense(r, ex, ctx):
    res = R_toposhuffle(r, ex, ctx)
    if res is None: return None
    return renumber_dense(Ex(res[0])), 'toposhuffle + dense renumbering'
@op('R', 'un-sharing + dense renumbering -> same meaning, fast-path parse')
def R_unshare_dense(r, ex, ctx):
    res = R_unshare(r, ex, ctx)
    if res is None: return None
    return renumber_dense(Ex(res[0])), res[1] + ' + dense renumbering'

# ---------------------------------------------------------------- P: proof-only (kernel-level) mutations
# Mutations restricted to declarations OUTSIDE the comparator's statement closure and to expression lines reachable only
# from them: the comparison cannot see these, so the kernels must catch every ill-typed result.
def proof_only(ex, ctx):
    if 'po' in ctx: return ctx['po']
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from seams import closure_names
    seen, byname = closure_names(ex, sorted(ctx['targets']))
    ctx['closure'] = seen
    tg = set(ctx['targets'])
    # proof-only declarations: outside the closure, plus the target theorems / definition holes (only their TYPES are compared)
    decls = [i for i in ex.decls if ex.declkind[i] in ('thm', 'def', 'opaque') and
             (ex.decl_name(i) not in seen or (ex.decl_name(i) in tg and ex.declkind[i] in ('thm', 'def')))]
    def reach(roots):
        st = list(roots); out = set()
        while st:
            x = st.pop()
            if x in out or x not in ex.exprs: continue
            out.add(x); o = ex.get(ex.exprs[x]); k = [y for y in o if y != 'ie'][0]; d = o[k]
            if k == 'app': st += [d['fn'], d['arg']]
            elif k in ('lam', 'forallE'): st += [d['type'], d['body']]
            elif k == 'letE': st += [d['type'], d['value'], d['body']]
            elif k == 'mdata': st.append(d['expr'])
            elif k == 'proj': st.append(d['struct'])
        return out
    cl_roots = []
    for i in ex.decls:
        o = ex.get(i); k = next(iter(o))
        if k == 'inductive':
            for part in ('types', 'ctors', 'recs'):
                for x in o[k][part]:
                    cl_roots.append(x['type'])
                    for ru in x.get('rules', []): cl_roots.append(ru['rhs'])
        elif ex.decl_name(i) in seen:
            cl_roots.append(o[k]['type'])
            if 'value' in o[k] and not (ex.decl_name(i) in tg and k in ('thm', 'def')): cl_roots.append(o[k]['value'])
    cl = reach(cl_roots)
    po_roots = []
    for i in decls:
        d = ex.get(i)[ex.declkind[i]]; po_roots.append(d['type']); po_roots.append(d['value'])
    pe = sorted(reach(po_roots) - cl)
    ctx['po'] = (decls, pe); return ctx['po']
@op('P', 'one expression node reachable only from proof-only declarations mutated (as E_node; the comparison cannot see it)')
def P_node(r, ex, ctx):
    decls, pe = proof_only(ex, ctx)
    if not pe: return None
    sub = Ex.__new__(Ex); sub.__dict__ = dict(ex.__dict__); sub.exprs = {k: ex.exprs[k] for k in pe}
    res = E_node(r, sub, ctx)
    if res is None: return None
    return res[0], 'proof-only ' + res[1]
@op('P', 'a proof-only declaration: value replaced by its type / another proof-only value, type and value swapped, kind changed, or deleted')
def P_decl(r, ex, ctx):
    decls, pe = proof_only(ex, ctx)
    if not decls: return None
    i = r.choice(decls); o = json.loads(json.dumps(ex.get(i))); k = ex.declkind[i]; d = o[k]
    m = r.choice(['value_is_type', 'other_value', 'swap', 'to_axiom', 'delete', 'lparams_drop'])
    if m == 'value_is_type': d['value'] = d['type']
    elif m == 'other_value':
        cand = [j for j in decls if j < i and j != i]
        if not cand: return None
        j = r.choice(cand); d['value'] = ex.get(j)[ex.declkind[j]]['value']
    elif m == 'swap': d['type'], d['value'] = d['value'], d['type']
    elif m == 'to_axiom': o = {'axiom': {'isUnsafe': False, 'levelParams': d['levelParams'], 'name': d['name'], 'type': d['type']}}
    elif m == 'delete': return ex.out(delete={i}), f'proof-only {ex.decl_name(i)} deleted'
    else:
        if not d['levelParams']: return None
        d['levelParams'] = d['levelParams'][:-1]
    return ex.out({i: canon(o)}), f'proof-only {k} {ex.decl_name(i)} {m}'

def main():
    if len(sys.argv) >= 2 and sys.argv[1] == 'list':
        for n, (c, d, _) in OPS.items():
            print(f'{c}\t{n}\t{d}')
        return
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd'); ap.add_argument('base'); ap.add_argument('out')
    ap.add_argument('--ops', default='all'); ap.add_argument('--per-op', type=int, default=5)
    ap.add_argument('--seed', type=int, default=1); ap.add_argument('--targets', default='')
    a = ap.parse_args()
    data = open(a.base, 'rb').read(); ex = Ex(data)
    ctx = {'targets': set(t for t in a.targets.split(',') if t)}
    ops = list(OPS) if a.ops == 'all' else a.ops.split(',')
    os.makedirs(a.out, exist_ok=True)
    man = open(os.path.join(a.out, 'manifest.tsv'), 'a')
    bh = hashlib.sha256(data).hexdigest()[:12]
    WHOLE = {'I_sparse', 'I_perm_names', 'I_perm_levels', 'R_toposhuffle', 'R_unshare', 'R_topo_dense', 'R_unshare_dense', 'D_reorder'}
    for name in ops:
        cls, _, f = OPS[name]
        made = 0; tries = 0
        per = min(a.per_op, 2) if (name in WHOLE and len(ex.lines) > 200000) else a.per_op   # whole-file rewrites are slow on big bases
        while made < per and tries < per * 5:
            tries += 1
            r = random.Random(f'{bh}:{name}:{a.seed}:{tries}')
            try:
                res = f(r, ex, ctx)
            except (IndexError, KeyError, ValueError) as e:
                res = None
            if res is None:
                continue
            blob, det = res
            mid = f'{name}-{a.seed}-{tries}'
            with open(os.path.join(a.out, mid + '.ndjson'), 'wb') as fh:
                fh.write(blob)
            man.write(f'{mid}\t{name}\t{cls}\t{det}\n'); made += 1
    man.close()

if __name__ == '__main__':
    main()

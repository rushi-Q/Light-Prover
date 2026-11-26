#!/usr/bin/env python3
"""Tiny lean4export-3.1.0-format writer for expdiff's regression tests (no kernel validity needed:
expdiff never type-checks). Expressions: ('sort',0) ('c',name) ('app',f,a) ('lam',n,ty,body,bi)
('pi',n,ty,body,bi) ('bv',k) ('let',n,ty,val,body). Declarations: ('axiom',name,type), ('thm',name,type,value),
('def',name,type,value)."""
import json, sys

class W:
    def __init__(self):
        self.lines = [json.dumps({"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                                           "format": {"version": "3.1.0"},
                                           "lean": {"githash": "test", "version": "4.33.1"}}}, separators=(',', ':'))]
        self.names = {(): 0}
        self.exprs = {}
    def emit(self, obj):
        self.lines.append(json.dumps(obj, separators=(',', ':'), sort_keys=True, ensure_ascii=False))
    def name(self, s):
        comps = tuple(s.split('.'))
        for k in range(1, len(comps) + 1):
            if comps[:k] not in self.names:
                i = len(self.names)
                self.names[comps[:k]] = i
                if comps[k - 1].isdigit():
                    self.emit({"in": i, "num": {"pre": self.names[comps[:k - 1]], "i": int(comps[k - 1])}})
                else:
                    self.emit({"in": i, "str": {"pre": self.names[comps[:k - 1]], "str": comps[k - 1]}})
        return self.names[comps]
    def expr(self, e):
        if e in self.exprs:
            return self.exprs[e]
        k = e[0]
        if k == 'sort':
            obj = {"sort": 0}
        elif k == 'c':
            obj = {"const": {"name": self.name(e[1]), "us": []}}
        elif k == 'app':
            f = self.expr(e[1]); a = self.expr(e[2])
            obj = {"app": {"fn": f, "arg": a}}
        elif k in ('lam', 'pi'):
            n = self.name(e[1]); t = self.expr(e[2]); b = self.expr(e[3])
            bi = e[4] if len(e) > 4 else "default"
            obj = {("lam" if k == 'lam' else "forallE"): {"name": n, "type": t, "body": b, "binderInfo": bi}}
        elif k == 'bv':
            obj = {"bvar": e[1]}
        elif k == 'let':
            n = self.name(e[1]); t = self.expr(e[2]); v = self.expr(e[3]); b = self.expr(e[4])
            obj = {"letE": {"name": n, "type": t, "value": v, "body": b, "nondep": False}}
        else:
            raise ValueError(e)
        i = len(self.exprs)
        obj["ie"] = i
        self.exprs[e] = i
        self.emit(obj)
        return i
    def decl(self, d):
        kind, name = d[0], d[1]
        n = self.name(name)
        t = self.expr(d[2])
        if kind == 'axiom':
            self.emit({"axiom": {"name": n, "levelParams": [], "type": t, "isUnsafe": False}})
        elif kind == 'thm':
            v = self.expr(d[3])
            self.emit({"thm": {"name": n, "levelParams": [], "type": t, "value": v, "all": [n]}})
        elif kind == 'def':
            v = self.expr(d[3])
            self.emit({"def": {"name": n, "levelParams": [], "type": t, "value": v, "hints": {"regular": 1},
                               "safety": "safe", "all": [n]}})

P, Q, p = ('c', 'P'), ('c', 'Q'), ('c', 'p')
PROP = ('sort', 0)
idQ = ('lam', 'y', Q, ('bv', 0))
QQ = ('pi', 'y', Q, Q)
BASE = [('axiom', 'P', PROP), ('axiom', 'Q', PROP), ('axiom', 'p', P)]
OLD = BASE + [
    ('thm', 't1', P, p),
    ('thm', 't2', ('pi', 'h', P, P), ('lam', 'h', P, ('bv', 0))),
    ('thm', 't3', P, ('let', 'x', QQ, idQ, p)),                      # dead let
    ('thm', 't4', ('pi', 'h', Q, P), ('lam', 'h', Q, p)),            # unused hypothesis
    ('thm', 't5', P, ('app', ('lam', 'z', QQ, p), idQ)),              # dead beta redex
    ('thm', 't6', P, ('app', ('lam', 'w', P, ('bv', 0)), p)),         # used beta redex (not dead)
    ('def', 'd1', PROP, P),
    ('thm', 'N.t8', P, ('app', ('c', 't2'), ('c', 't1'))),
    ('thm', 'top', P, ('app', ('c', 't2'), ('app', ('c', 't4'), ('c', 'q')))),
]
OLD.insert(3, ('axiom', 'q', Q))
NEW = BASE + [('axiom', 'q', Q),
    ('thm', 't1', P, p),                                              # identical
    ('thm', 't2', ('pi', 'k', P, P), ('lam', 'k', P, ('bv', 0))),     # alpha-equal (binder renamed)
    ('thm', 't3', P, p),                                              # value changed (dead let removed)
    ('thm', 't4', ('pi', 'h', P, P), ('lam', 'h', P, p)),             # STATEMENT changed
    ('thm', 't6', P, ('app', ('lam', 'w', P, ('bv', 0)), p)),         # identical; t5 removed
    ('def', 'd1', PROP, P),
    ('thm', 'M.t8', P, ('app', ('c', 't2'), ('c', 't1'))),            # renamed N.t8 -> M.t8
    ('thm', 't7', P, p),                                              # added
    ('thm', 'top', P, ('app', ('c', 't2'), ('app', ('c', 't4'), ('c', 'p')))),
]

# module merge: the private names' module part changes (A -> M), contents identical
PRIV_OLD = BASE + [('thm', '_private.Mod.A.0.p1', P, p), ('thm', 'q1', P, ('c', '_private.Mod.A.0.p1')),
                   ('thm', '_private.Mod.B.0.p2', P, ('c', '_private.Mod.A.0.p1'))]
PRIV_NEW = BASE + [('thm', '_private.Mod.M.0.p1', P, p), ('thm', 'q1', P, ('c', '_private.Mod.M.0.p1')),
                   ('thm', '_private.Mod.M.0.p2', P, ('c', '_private.Mod.M.0.p1'))]

if __name__ == '__main__':
    which, out = sys.argv[1], sys.argv[2]
    w = W()
    for d in {'old': OLD, 'new': NEW, 'privold': PRIV_OLD, 'privnew': PRIV_NEW}[which]:
        w.decl(d)
    open(out, 'w').write('\n'.join(w.lines) + '\n')

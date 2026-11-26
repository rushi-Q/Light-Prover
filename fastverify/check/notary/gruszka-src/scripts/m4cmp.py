#!/usr/bin/env python3
"""Per-declaration instructions, Gruszka (SK_DECL_INSTR=1: DI lines) vs
Pestka (temporary wrapper in generated Rust: PJ = deferred check, PB =
building), joined by declaration name. Usage:
  m4cmp.py GR.err PK.err OUT.csv [TOP]"""
import sys, collections
gr, pk, out = sys.argv[1], sys.argv[2], sys.argv[3]
top = int(sys.argv[4]) if len(sys.argv) > 4 else 25
g = collections.OrderedDict()
for l in open(gr, errors='replace'):
    if l.startswith('DI\t'):
        _, i, n, ins, ns = l.rstrip('\n').split('\t')
        g[n] = g.get(n, 0) + int(ins)
p = collections.defaultdict(int)
for l in open(pk, errors='replace'):
    if l.startswith('PJ\t') or l.startswith('PB\t'):
        _, n, ins, ns = l.rstrip('\n').split('\t')
        p[n] += int(ins)
rows = []
for n, gi in g.items():
    pi = p.get(n)
    if pi is None: continue
    rows.append((n, gi, pi))
with open(out, 'w') as f:
    f.write('name,gruszka_instr,pestka_instr,ratio,excess\n')
    for n, gi, pi in rows:
        f.write('"%s",%d,%d,%.3f,%d\n' % (n.replace('"', '""'), gi, pi, gi / max(pi, 1), gi - pi))
G = sum(r[1] for r in rows); P = sum(r[2] for r in rows)
print('matched %d of %d gruszka / %d pestka decls; gruszka %.2f G, pestka %.2f G, ratio %.2f' % (len(rows), len(g), len(p), G/1e9, P/1e9, G/max(P,1)))
print('-- top by excess (gruszka - pestka), M instr')
for n, gi, pi in sorted(rows, key=lambda r: -(r[1]-r[2]))[:top]:
    print('%9.1f %9.1f %9.1f  x%-7.1f %s' % ((gi-pi)/1e6, gi/1e6, pi/1e6, gi/max(pi,1), n))
print('-- top by ratio (gruszka >= 5 M)')
for n, gi, pi in sorted([r for r in rows if r[1] >= 5e6], key=lambda r: -r[1]/max(r[2],1))[:top]:
    print('%9.1f %9.1f %9.1f  x%-7.1f %s' % ((gi-pi)/1e6, gi/1e6, pi/1e6, gi/max(pi,1), n))
ex = sorted([r[1]-r[2] for r in rows], reverse=True)
pos = sum(x for x in ex if x > 0)
for k in (10, 100, 1000):
    print('top %d excess: %.1f G (%.0f%% of positive excess %.1f G)' % (k, sum(ex[:k])/1e9, 100*sum(ex[:k])/pos, pos/1e9))

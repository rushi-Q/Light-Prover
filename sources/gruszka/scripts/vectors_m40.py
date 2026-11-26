# Milestone 40 vectors (python3 scripts/vectors_m40.py tests/adv/bad_m33_eta_major_indexed.ndjson tests/adv): closed recursor applications that reach the ground
# machine (SK_GROUND=2), built on tests/adv/bad_m33_eta_major_indexed.ndjson
# (Nat, OfNat, the indexed Idx, Eq) with its last theorem dropped.
import json, sys
src, out = sys.argv[1], sys.argv[2]
lines = open(src).read().splitlines()
assert '"thm"' in lines[-1]
base = lines[:-1]
names = {}; mi = 0; me = 0
for l in base:
    o = json.loads(l)
    if 'in' in o:
        mi = max(mi, o['in'])
        if 'str' in o:
            names[o['in']] = o['str']['str'] if not o['str']['pre'] else names.get(o['str']['pre'], '?') + '.' + o['str']['str']
    if 'ie' in o: me = max(me, o['ie'])
inv = {v: k for k, v in names.items()}
NAT, IDX, IDXREC, IDXMK = inv['Nat'], inv['Idx'], inv['Idx.rec'], inv['Idx.mk']
EQ, EQREFL, EQREC = inv['Eq'], inv['Eq.refl'], inv['Eq.rec']
OFNAT, OFNATREC, OFNATOF, INST = inv['OfNat'], inv['OfNat.rec'], inv['OfNat.ofNat'], inv['instOfNatNat']
class W:
    def __init__(s): s.lines = list(base); s.n = mi; s.e = me
    def name(s, t):
        s.n += 1; s.lines.append(json.dumps({"in": s.n, "str": {"pre": 0, "str": t}})); return s.n
    def ex(s, **kw):
        s.e += 1; d = dict(kw); d["ie"] = s.e; s.lines.append(json.dumps(d)); return s.e
    def c(s, n, us=()): return s.ex(const={"name": n, "us": list(us)})
    def app(s, f, *a):
        for x in a: f = s.ex(app={"fn": f, "arg": x})
        return f
    def lam(s, n, t, b): return s.ex(lam={"name": n, "type": t, "body": b, "binderInfo": "default"})
    def bv(s, i): return s.ex(bvar=i)
    def lit(s, k): return s.ex(natVal=str(k))
    def axiom(s, n, t): s.lines.append(json.dumps({"axiom": {"name": n, "type": t, "levelParams": [], "isUnsafe": False}}))
    def thm(s, n, t, v): s.lines.append(json.dumps({"thm": {"name": n, "type": t, "value": v, "levelParams": [], "all": [n]}}))
    def save(s, p): open(p, 'w').write('\n'.join(s.lines) + '\n')
Z, U1 = 0, 1  # level ids: zero, succ zero
def eq5(w, lhs):
    return w.app(w.c(EQ, [U1]), w.c(NAT), lhs, w.lit(5)), w.app(w.c(EQREFL, [U1]), w.c(NAT), w.lit(5))
# Idx.rec (indexed, one constructor, not a structure): a closed stuck major
# of an index no constructor has (bad: no eta); Idx.mk itself (good: iota)
for kind in ('bad', 'good'):
    w = W(); x = w.name('x'); t = w.name('t')
    motive = w.lam(x, w.c(NAT), w.lam(t, w.app(w.c(IDX), w.bv(0)), w.c(NAT)))
    if kind == 'bad':
        ax = w.name('axIdx3'); w.axiom(ax, w.app(w.c(IDX), w.lit(3)))
        lhs = w.app(w.c(IDXREC, [U1]), motive, w.lit(5), w.lit(3), w.c(ax))
    else:
        zero = w.app(w.c(OFNATOF, [Z]), w.c(NAT), w.lit(0), w.app(w.c(INST), w.lit(0)))
        lhs = w.app(w.c(IDXREC, [U1]), motive, w.lit(5), zero, w.c(IDXMK))
    ty, pf = eq5(w, lhs); w.thm(w.name('closedIdxRec'), ty, pf)
    w.save(f'{out}/{kind}_m40_ground_rec_indexed_closed.ndjson')
# OfNat.rec (a structure) on a closed stuck major: structure eta, accepted
w = W(); t = w.name('t'); y = w.name('y')
ax = w.name('axOfNat7'); w.axiom(ax, w.app(w.c(OFNAT, [Z]), w.c(NAT), w.lit(7)))
motive = w.lam(t, w.app(w.c(OFNAT, [Z]), w.c(NAT), w.lit(7)), w.c(NAT))
minor = w.lam(y, w.c(NAT), w.lit(5))
lhs = w.app(w.c(OFNATREC, [U1, Z]), w.c(NAT), w.lit(7), motive, minor, w.c(ax))
ty, pf = eq5(w, lhs); w.thm(w.name('closedStructEta'), ty, pf)
w.save(f'{out}/good_m40_ground_struct_eta_closed.ndjson')
# Eq.rec (K-like) on a closed proof: of 0 = 1 (bad: K needs the major's
# type to be refl's), of 0 = 0 (good)
for kind, b in (('bad', 1), ('good', 0)):
    w = W(); bb = w.name('b'); t = w.name('t')
    h = w.name('h0eq%d' % b); w.axiom(h, w.app(w.c(EQ, [U1]), w.c(NAT), w.lit(0), w.lit(b)))
    motive = w.lam(bb, w.c(NAT), w.lam(t, w.app(w.c(EQ, [U1]), w.c(NAT), w.lit(0), w.bv(0)), w.c(NAT)))
    lhs = w.app(w.c(EQREC, [U1, U1]), w.c(NAT), w.lit(0), motive, w.lit(5), w.lit(b), w.c(h))
    ty, pf = eq5(w, lhs); w.thm(w.name('closedK'), ty, pf)
    w.save(f'{out}/{kind}_m40_ground_k_closed.ndjson')

# Writes small adversarial lean4export 3.1 files to tests/adv/, with the
# expected outcome in the file name prefix (good_ / bad_).
import json, os
META = '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"x","version":"4.34.1"}}}'

class W:
    def __init__(s): s.lines = [META]; s.n = 0; s.e = 0; s.l = 0; s.names = {}
    def name(s, txt, pre=0, dup=False):
        if txt in s.names and not dup and pre == 0: return s.names[txt]
        s.n += 1; s.lines.append(json.dumps({"in": s.n, "str": {"pre": pre, "str": txt}})); s.names.setdefault(txt, s.n); return s.n
    def ex(s, **kw):
        kw["ie"] = s.e; s.lines.append(json.dumps(kw)); s.e += 1; return s.e - 1
    def sort(s, l): return s.ex(sort=l)
    def succ(s, l): s.l += 1; s.lines.append(json.dumps({"il": s.l, "succ": l})); return s.l
    def const(s, n, us=()): return s.ex(const={"name": n, "us": list(us)})
    def app(s, f, a): return s.ex(app={"fn": f, "arg": a})
    def pi(s, n, t, b, bi="default"): return s.ex(forallE={"name": n, "type": t, "body": b, "binderInfo": bi})
    def lam(s, n, t, b, bi="default"): return s.ex(lam={"name": n, "type": t, "body": b, "binderInfo": bi})
    def bvar(s, i): return s.ex(bvar=i)
    def axiom(s, n, ty, lp=()): s.lines.append(json.dumps({"axiom": {"name": n, "type": ty, "levelParams": list(lp), "isUnsafe": False}}))
    def thm(s, n, ty, v, lp=()): s.lines.append(json.dumps({"thm": {"name": n, "type": ty, "value": v, "levelParams": list(lp), "all": [n]}}))
    def defn(s, n, ty, v, lp=(), h="opaque", safety="safe"):
        s.lines.append(json.dumps({"def": {"name": n, "type": ty, "value": v, "levelParams": list(lp), "all": [n], "hints": h, "safety": safety}}))
    def save(s, path): open(path, "w").write("\n".join(s.lines) + "\n")

out = os.path.join(os.path.dirname(__file__), "..", "tests", "adv")
os.makedirs(out, exist_ok=True)

def base():
    w = W(); prop = w.sort(0)
    f = w.name("False"); w.axiom(f, prop)  # False as an axiom Prop
    return w, prop, f

# 1. forward reference in MAIN: theorem A : False := B ; theorem B : False := A
w, prop, f = base(); F = w.const(f)
a = w.name("A"); b = w.name("B")
ca = w.const(a); cb = w.const(b)
w.thm(a, F, cb); w.thm(b, F, ca); w.save(f"{out}/bad_circular_theorems.ndjson")

# 2. forward reference to a later axiom
w, prop, f = base(); F = w.const(f)
a = w.name("A"); b = w.name("B"); cb = w.const(b)
w.thm(a, F, cb); w.axiom(b, F); w.save(f"{out}/bad_forward_ref.ndjson")

# 3. duplicate name records: X declared via record 1, used via a second record of the same name
w, prop, f = base()
x1 = w.name("X"); x2 = w.name("X", dup=True)
w.axiom(x1, prop)
t = w.name("t"); cx = w.const(x2); idt = w.pi(t, cx, cx)
y = w.name("Y"); lamv = w.lam(t, cx, w.bvar(0)); w.thm(y, idt, lamv)
w.save(f"{out}/good_duplicate_name_records.ndjson")

# 4. open declaration value (loose bvar)
w, prop, f = base()
n = w.name("open"); v = w.bvar(0); w.defn(n, prop, v); w.save(f"{out}/bad_open_value.ndjson")

# 5. open declaration type
w, prop, f = base()
n = w.name("openTy"); w.axiom(n, w.bvar(0)); w.save(f"{out}/bad_open_type.ndjson")

# 6. looping ill-typed definition before a failing one: omega := (fun x => x x) (fun x => x x)
w, prop, f = base()
x = w.name("x"); sx = w.lam(x, prop, w.app(w.bvar(0), w.bvar(0)))
om = w.app(sx, sx); n = w.name("omega"); w.defn(n, prop, om, h={"regular": 1})
g = w.name("useOmega"); co = w.const(n); w.thm(g, co, w.const(f)); w.save(f"{out}/bad_omega_first.ndjson")

# 7. a failing theorem whose proof would need a later theorem's unfolding (stale/cycle)
w, prop, f = base()
t = w.name("T"); w.axiom(t, prop); ct = w.const(t)
p = w.name("p"); q = w.name("q"); cq = w.const(q); cp = w.const(p)
w.thm(p, ct, cq); w.thm(q, ct, cp); w.save(f"{out}/bad_mutual_proofs.ndjson")

# 8. universe parameter named twice
w, prop, f = base()
u = w.name("u"); n = w.name("dupU"); w.axiom(n, prop, lp=(u, u)); w.save(f"{out}/bad_dup_universe.ndjson")

# 9. undeclared universe parameter in a type
w, prop, f = base()
u = w.name("u"); w.l += 1; w.lines.append(json.dumps({"il": w.l, "param": u}))
s = w.sort(w.l); n = w.name("undeclU"); w.axiom(n, s); w.save(f"{out}/bad_undeclared_universe.ndjson")

# 10. self-referencing (non-unsafe) definition
w, prop, f = base()
n = w.name("selfDef"); c = w.const(n); w.defn(n, prop, c); w.save(f"{out}/bad_self_definition.ndjson")
print("written to", os.path.abspath(out))

# 11. forward reference in MAIN: the const B is shared by two theorems, so it stays in MAIN
w, prop, f = base(); F = w.const(f)
a = w.name("A"); a2 = w.name("A2"); b = w.name("B")
cb = w.const(b); ca = w.const(a)
w.thm(a, F, cb); w.thm(a2, F, cb); w.thm(b, F, ca); w.save(f"{out}/bad_forward_ref_main.ndjson")

# 12. forward reference in a MAIN type
w, prop, f = base()
a = w.name("A"); b = w.name("B"); cb = w.const(b)
w.axiom(a, cb); w.axiom(b, prop); w.save(f"{out}/bad_forward_ref_type.ndjson")

# ---- vectors for the caches kept across declarations (milestone 2)

def lvl_param(w, name):
    w.l += 1; w.lines.append(json.dumps({"il": w.l, "param": name})); return w.l

# 13. a closed type with a universe parameter checked in X.{u}, then used by
# Y without u: the earlier check must not be reused
w, prop, f = base()
u = w.name("u"); lu = lvl_param(w, u)
a = w.name("a"); su = w.sort(lu); T = w.pi(a, su, su)
x = w.name("X"); w.axiom(x, T, lp=(u,))
y = w.name("Y"); w.axiom(y, T)
w.save(f"{out}/bad_checked_universe.ndjson")

# 14. the same, but Y declares u too: accepted
w, prop, f = base()
u = w.name("u"); lu = lvl_param(w, u)
a = w.name("a"); su = w.sort(lu); T = w.pi(a, su, su)
x = w.name("X"); w.axiom(x, T, lp=(u,))
y = w.name("Y"); w.axiom(y, T, lp=(u,))
w.save(f"{out}/good_checked_universe.ndjson")

# 15. a term using an unsafe constant, checked in an unsafe definition, then
# the same term as the value of a safe definition
w, prop, f = base()
uu = w.name("U"); w.lines.append(json.dumps({"axiom": {"name": uu, "type": prop, "levelParams": [], "isUnsafe": True}}))
cu = w.const(uu)
x = w.name("X"); w.defn(x, prop, cu, safety="unsafe")
y = w.name("Y"); w.defn(y, prop, cu)
w.save(f"{out}/bad_checked_unsafe.ndjson")

# 16. an equality between closed terms found true in an earlier declaration
# (E (G P) = E (G2 P), G and G2 identities: a stored closed-pair fact),
# then a theorem whose type differs only in an argument (E (G Q)): the fact
# must not be applied to the other pair
w, prop, f = base()
p = w.name("P"); w.axiom(p, prop); cp = w.const(p)
q = w.name("Q"); w.axiom(q, prop); cq = w.const(q)
e = w.name("E"); a = w.name("a"); w.axiom(e, w.pi(a, prop, prop)); ce = w.const(e)
x = w.name("x"); idl = w.lam(x, prop, w.bvar(0))
g = w.name("G"); w.defn(g, w.pi(a, prop, prop), idl, h={"regular": 1}); cg = w.const(g)
g2 = w.name("G2"); w.defn(g2, w.pi(a, prop, prop), idl, h={"regular": 1}); cg2 = w.const(g2)
h1 = w.name("h1"); w.axiom(h1, w.app(ce, w.app(cg2, cp)))
ch1 = w.const(h1); ty1 = w.app(ce, w.app(cg, cp))
t1 = w.name("t1"); w.thm(t1, ty1, ch1)
t2 = w.name("t2"); w.thm(t2, w.app(ce, w.app(cg, cq)), ch1)
w.save(f"{out}/bad_closed_pair_cache.ndjson")
# and the reuse itself is fine: t2 repeats t1's statement
w.lines.pop(); w.thm(t2, ty1, ch1)
w.save(f"{out}/good_closed_pair_cache.ndjson")

# 17. duplicate name records with different structure: X : Prop, then a
# second X : Prop -> Prop, then a use that needs the second shape
w, prop, f = base()
x1 = w.name("X"); w.axiom(x1, prop)
x2 = w.name("X", dup=True); a = w.name("a"); w.axiom(x2, w.pi(a, prop, prop))
y = w.name("Y"); w.axiom(y, w.app(w.const(x2), prop))
w.save(f"{out}/bad_duplicate_name_shapes.ndjson")
print("cache vectors written")

# 18. a fact must not travel back in file order: with namespace order
# (SK_ORDER=ns) A.w (declaration 4) is checked before B.y (declaration 2) on
# one worker; both have the value A.K, declared at 3. B.y must be rejected.
w, prop, f = base()
a1 = w.name("A.first"); w.axiom(a1, prop)
k = w.name("A.K"); ck = w.const(k)
by = w.name("B.y"); w.defn(by, prop, ck)
w.axiom(k, prop)
aw = w.name("A.w"); w.defn(aw, prop, ck)
w.save(f"{out}/bad_fact_back_in_order.ndjson")

# ---- vectors for the argument skips (milestone 3)

def nat_like(w):
    # N : Type, n1 n2 : N (different axioms)
    one = w.succ(0); ty = w.sort(one)
    N = w.name("N"); w.axiom(N, ty); cN = w.const(N)
    n1 = w.name("n1"); w.axiom(n1, cN); n2 = w.name("n2"); w.axiom(n2, cN)
    return one, cN, w.const(n1), w.const(n2)

# 19. G.{u} (α : Sort u) (a : α) : Prop. At u = 1 the argument a is data
# and must be compared: G N n1 -> G N n2 is not the identity's type.
def g_axiom(w):
    u = w.name("u"); lu = lvl_param(w, u)
    al = w.name("α"); a = w.name("a"); g = w.name("G")
    prop = w.sort(0)
    w.axiom(g, w.pi(al, w.sort(lu), w.pi(a, w.bvar(0), prop)), lp=(u,))
    return g
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
g = g_axiom(w); cg = w.const(g, [one])
h = w.name("h")
ty = w.pi(h, w.app(w.app(cg, cN), c1), w.app(w.app(cg, cN), c2))
w.thm(w.name("t"), ty, w.lam(h, w.app(w.app(cg, cN), c1), w.bvar(0)))
w.save(f"{out}/bad_data_arg_compared.ndjson")

# 20. the same at u = 0 with two proofs of P: proof irrelevance, accepted
w, prop, f = base()
P = w.name("P"); w.axiom(P, prop); cP = w.const(P)
p1 = w.name("p1"); w.axiom(p1, cP); p2 = w.name("p2"); w.axiom(p2, cP)
g = g_axiom(w); cg = w.const(g, [0])
h = w.name("h")
ty = w.pi(h, w.app(w.app(cg, cP), w.const(p1)), w.app(w.app(cg, cP), w.const(p2)))
w.thm(w.name("t"), ty, w.lam(h, w.app(w.app(cg, cP), w.const(p1)), w.bvar(0)))
w.save(f"{out}/good_proof_arg_skipped.ndjson")

# 21. K a b := a. K n1 n1 and K n2 n1 differ in the argument K reads:
# leaving out b (never read) must still compare a.
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
Q = w.name("Q"); x = w.name("x"); w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
a = w.name("a"); b = w.name("b"); K = w.name("K")
w.defn(K, w.pi(a, cN, w.pi(b, cN, cN)), w.lam(a, cN, w.lam(b, cN, w.bvar(1))), h={"regular": 1}); cK = w.const(K)
h = w.name("h")
lhs = w.app(cQ, w.app(w.app(cK, c1), c1)); rhs = w.app(cQ, w.app(w.app(cK, c2), c1))
w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
w.save(f"{out}/bad_unused_arg_reads_first.ndjson")
# and K n1 n1 against K n1 n2: b is never read, accepted
w.lines.pop()
rhs = w.app(cQ, w.app(w.app(cK, c1), c2))
w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
w.save(f"{out}/good_unused_arg_left_out.ndjson")
print("argument-skip vectors written")

# ---- casesOn read directly (milestone 3). Base: Arena tutorial 064
# (Bool, TwoBool with mk b1 b2, TwoBool.rec), without its last definition.
def from_base(path):
    w = W(); w.lines = [l.rstrip("\n") for l in open(path)]
    for l in w.lines[1:]:
        d = json.loads(l)
        if "in" in d: w.n = max(w.n, d["in"]); w.names.setdefault(d["str"]["str"] if "str" in d else "", d["in"])
        if "ie" in d: w.e = max(w.e, d["ie"] + 1)
        if "il" in d: w.l = max(w.l, d["il"])
    return w
base_path = os.path.join(os.path.dirname(__file__), "..", "tests", "adv-base", "twobool.base")
def twobool_cases(expect_true):
    w = from_base(base_path)
    BOOL, FALSE, TRUE, TB, MK, REC, U = 1, 2, 3, 10, 11, 14, 5
    lu = 2  # level param u
    cB = w.const(BOOL); cTB = w.const(TB); prop = w.sort(0)
    m = w.name("motive"); t = w.name("t"); k = w.name("k"); b1 = w.name("b1"); b2 = w.name("b2")
    # type: (motive : TB -> Sort u) -> (t : TB) -> ((b1 b2 : Bool) -> motive (mk b1 b2)) -> motive t
    mty = w.pi(t, cTB, w.sort(lu))
    kty = w.pi(b1, cB, w.pi(b2, cB, w.app(w.bvar(3), w.app(w.app(w.const(MK), w.bvar(1)), w.bvar(0)))))
    ty = w.pi(m, mty, w.pi(t, cTB, w.pi(k, kty, w.app(w.bvar(2), w.bvar(1)))))
    # value: fun motive t k => TB.rec.{u} motive (fun b1 b2 => k b1 b2) t
    kty_v = w.pi(b1, cB, w.pi(b2, cB, w.app(w.bvar(3), w.app(w.app(w.const(MK), w.bvar(1)), w.bvar(0)))))
    wrap = w.lam(b1, cB, w.lam(b2, cB, w.app(w.app(w.bvar(2), w.bvar(1)), w.bvar(0))))
    body = w.app(w.app(w.app(w.const(REC, [lu]), w.bvar(2)), wrap), w.bvar(1))
    val = w.lam(m, mty, w.lam(t, cTB, w.lam(k, kty_v, body)))
    cs = w.name("TwoBool.cases2"); w.defn(cs, ty, val, lp=(U,), h="abbrev")
    q = w.name("Q"); x = w.name("x"); w.axiom(q, w.pi(x, cB, prop)); cq = w.const(q)
    return w, cq, None, cs
for good in (True, False):
    w, cq, _, cs = twobool_cases(good)
    mot = w.lam(w.name("t"), w.const(10), w.const(1))
    pick = w.lam(w.name("b1"), w.const(1), w.lam(w.name("b2"), w.const(1), w.bvar(0)))
    mk = w.app(w.app(w.const(11), w.const(3)), w.const(2))
    lhs = w.app(cq, w.app(w.app(w.app(w.const(cs, [1]), mot), mk), pick))
    rhs = w.app(cq, w.const(2 if good else 3))
    h = w.name("h")
    w.thm(w.name("t2"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_cases_direct_second_field.ndjson")
print("casesOn vectors written")

# matcher-like: sel x := cases2.{1} (fun _ => Bool) x (fun a b => b); read
# through its casesOn (only the major premise and the minor picked)
for good in (True, False):
    w, cq, _, cs = twobool_cases(good)
    cB = w.const(1); cTB = w.const(10)
    x = w.name("x"); a = w.name("a"); b = w.name("b"); t = w.name("t")
    mot = w.lam(t, cTB, cB)
    pick = w.lam(a, cB, w.lam(b, cB, w.bvar(0)))
    selv = w.lam(x, cTB, w.app(w.app(w.app(w.const(cs, [1]), mot), w.bvar(0)), pick))
    sel = w.name("sel"); w.defn(sel, w.pi(x, cTB, cB), selv, h={"regular": 2})
    mk = w.app(w.app(w.const(11), w.const(3)), w.const(2))
    lhs = w.app(cq, w.app(w.const(sel), mk))
    rhs = w.app(cq, w.const(2 if good else 3))
    h = w.name("h")
    w.thm(w.name("t3"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_match_direct_second_field.ndjson")
print("matcher vectors written")

# ---- variables shared by type (milestone 3): two binders of one type in
# scope at once must stay two variables
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
Q = w.name("Q"); x = w.name("x"); y = w.name("y"); h = w.name("h")
w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
ty = w.pi(x, cN, w.pi(y, cN, w.pi(h, w.app(cQ, w.bvar(1)), w.app(cQ, w.bvar(1)))))
val = w.lam(x, cN, w.lam(y, cN, w.lam(h, w.app(cQ, w.bvar(1)), w.bvar(0))))
w.thm(w.name("t"), ty, val)
w.save(f"{out}/bad_two_vars_one_type.ndjson")
# lambdas compared under one variable per binder: fun x y => x vs fun x y => y
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
R = w.name("R"); g = w.name("g"); h = w.name("h"); x = w.name("x"); y = w.name("y")
w.axiom(R, w.pi(g, w.pi(x, cN, w.pi(y, cN, cN)), prop)); cR = w.const(R)
fst = w.lam(x, cN, w.lam(y, cN, w.bvar(1))); snd = w.lam(x, cN, w.lam(y, cN, w.bvar(0)))
lhs = w.app(cR, fst); rhs = w.app(cR, snd)
w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
w.save(f"{out}/bad_two_lambdas_two_vars.ndjson")
# and a binder opened twice in one declaration: accepted
w.lines.pop()
w.thm(w.name("t"), w.pi(h, lhs, w.app(cR, w.lam(x, cN, w.lam(y, cN, w.bvar(1))))), w.lam(h, lhs, w.bvar(0)))
w.save(f"{out}/good_lambda_opened_again.ndjson")
print("variable vectors written")

# ---- closure congruence by identity and known equalities (milestone 4):
# two thunks of one term with different environment entries are not
# taken equal unless the entries are; the comparison after decides.
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
Q = w.name("Q"); x = w.name("x"); h = w.name("h")
w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
F = w.name("F"); w.axiom(F, w.pi(x, cN, cN)); cF = w.const(F)
g = w.name("g"); w.defn(g, w.pi(x, cN, cN), w.lam(x, cN, w.app(cF, w.bvar(0))), h={"regular": 1}); cg = w.const(g)
lhs = w.app(cQ, w.app(cg, c1))
w.thm(w.name("t"), w.pi(h, lhs, w.app(cQ, w.app(cg, c2))), w.lam(h, lhs, w.bvar(0)))
w.save(f"{out}/bad_congruence_entries_differ.ndjson")
# entries equal by unfolding a definition: c := n1, accepted
w.lines.pop()
c = w.name("c"); w.defn(c, cN, c1, h={"regular": 1})
w.thm(w.name("t"), w.pi(h, lhs, w.app(cQ, w.app(cg, w.const(c)))), w.lam(h, lhs, w.bvar(0)))
w.save(f"{out}/good_congruence_entries_by_delta.ndjson")
# entries that are proofs of one proposition: equal by proof irrelevance
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
Q = w.name("Q"); x = w.name("x"); h = w.name("h"); p = w.name("p")
w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
P = w.name("P"); w.axiom(P, prop); cP = w.const(P)
p1 = w.name("p1"); w.axiom(p1, cP); p2 = w.name("p2"); w.axiom(p2, cP)
H = w.name("H"); w.axiom(H, w.pi(p, cP, cN)); cH = w.const(H)
gp = w.name("gp"); w.defn(gp, w.pi(p, cP, cN), w.lam(p, cP, w.app(cH, w.bvar(0))), h={"regular": 1}); cgp = w.const(gp)
lhs = w.app(cQ, w.app(cgp, w.const(p1)))
w.thm(w.name("t"), w.pi(h, lhs, w.app(cQ, w.app(cgp, w.const(p2)))), w.lam(h, lhs, w.bvar(0)))
w.save(f"{out}/good_congruence_proof_entries.ndjson")
print("congruence vectors written")

# ---- projection application reduced before unfolding the other side
# (milestone 4, Lean's try_unfold_proj_app): Q (F true) against
# Q (mk true false).1 (good) and .2 (bad), F b := b
for good in (True, False):
    w, cq, _, cs = twobool_cases(good)
    cB = w.const(1); b = w.name("b")
    F = w.name("F"); w.defn(F, w.pi(b, cB, cB), w.lam(b, cB, w.bvar(0)), h={"regular": 1})
    mk = w.app(w.app(w.const(11), w.const(3)), w.const(2))
    pr = w.ex(proj={"typeName": 10, "idx": 0 if good else 1, "struct": mk})
    lhs = w.app(cq, w.app(w.const(F), w.const(3)))
    rhs = w.app(cq, pr)
    h = w.name("h")
    w.thm(w.name("t4"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_proj_app_first.ndjson")
print("projection vectors written")

# ---- structural equality as the first shortcut (milestone 4, Pestka's
# sameTerm/quickParts on values): constants compared at their levels,
# variables standing for values compared with terms
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
Q = w.name("Q"); x = w.name("x"); h = w.name("h")
w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
u = w.name("u"); v = w.name("v"); lu = lvl_param(w, u); lv = lvl_param(w, v)
H = w.name("H"); w.axiom(H, w.pi(x, cN, cN), lp=(u,))
g = w.name("g"); w.defn(g, w.pi(x, cN, cN), w.lam(x, cN, w.app(w.const(H, [lu]), w.bvar(0))), lp=(u,), h={"regular": 1})
lhs = w.app(cQ, w.app(w.const(g, [lu]), c1))
w.thm(w.name("t"), w.pi(h, lhs, w.app(cQ, w.app(w.const(g, [lv]), c1))), w.lam(h, lhs, w.bvar(0)), lp=(u, v))
w.save(f"{out}/bad_struct_levels_differ.ndjson")
w.lines.pop()
w.thm(w.name("t"), w.pi(h, lhs, w.app(cQ, w.app(w.const(g, [lu]), c1))), w.lam(h, lhs, w.bvar(0)), lp=(u, v))
w.save(f"{out}/good_struct_levels_same.ndjson")
# (fun y => Q (F y)) n1 against Q (F n2): the variable stands for n1
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); h = w.name("h"); y = w.name("y")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    F = w.name("F"); w.axiom(F, w.pi(x, cN, cN)); cF = w.const(F)
    lhs = w.app(w.lam(y, cN, w.app(cQ, w.app(cF, w.bvar(0)))), c1)
    rhs = w.app(cQ, w.app(cF, c1 if good else c2))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_struct_var_vs_term.ndjson")
print("structural equality vectors written")

# ---- canonical first-order thunks (milestone 5, proposal 1): an argument
# `H.{u} x` becomes the neutral value H.{u} [x] at once. The level list and
# the environment entries are part of what it is.
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); h = w.name("h")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    u = w.name("u"); v = w.name("v"); lu = lvl_param(w, u); lv = lvl_param(w, v)
    H = w.name("H"); w.axiom(H, w.pi(x, cN, cN), lp=(u,))
    K = w.name("K"); w.axiom(K, w.pi(x, cN, cN)); cK = w.const(K)
    g = w.name("g"); w.defn(g, w.pi(x, cN, cN), w.lam(x, cN, w.app(cK, w.app(w.const(H, [lu]), w.bvar(0)))), lp=(u,), h={"regular": 1})
    lhs = w.app(cQ, w.app(w.const(g, [lu]), c1))
    rhs = w.app(cQ, w.app(w.const(g, [lu if good else lv]), c1))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)), lp=(u, v))
    w.save(f"{out}/{'good' if good else 'bad'}_p1_levels_in_thunk.ndjson")
# the same term under two environments: (fun y => Q (K (F y))) n1 against n2
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); h = w.name("h"); y = w.name("y")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    F = w.name("F"); w.axiom(F, w.pi(x, cN, cN)); cF = w.const(F)
    K = w.name("K"); w.axiom(K, w.pi(x, cN, cN)); cK = w.const(K)
    body = w.lam(y, cN, w.app(cQ, w.app(cK, w.app(cF, w.bvar(0)))))
    lhs = w.app(body, c1); rhs = w.app(body, c1 if good else c2)
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_p1_entries_differ.ndjson")
# an argument naming a constant declared later is rejected (unknown
# constant), not declined by an early evaluation: t : P := C p (B n1)
w, prop, f = base()
one, cN, c1, c2 = nat_like(w)
P = w.name("P"); w.axiom(P, prop); cP = w.const(P)
p = w.name("p"); w.axiom(p, cP)
x = w.name("x"); y = w.name("y")
C = w.name("C"); w.axiom(C, w.pi(x, cP, w.pi(y, cN, cP))); cC = w.const(C)
B = w.name("B"); cB = w.const(B)
w.defn(w.name("t"), cP, w.app(w.app(cC, w.const(p)), w.app(cB, c1)), h={"regular": 1})
w.axiom(B, w.pi(x, cN, cN))
w.save(f"{out}/bad_p1_later_constant_in_arg.ndjson")
print("milestone 5 vectors written")

# ---- an inductive family whose type reaches its indices only after delta
# (mathlib's Presieve.ofArrows : Presieve X, Presieve X := ⦃Y⦄ → (Y ⟶ X) →
# Prop): Eq from Arena tutorial 043 with type {α} → α → Rel α, Rel α :=
# α → Prop. Lean and Pestka whnf the type before each binder: one index.
def eq_via_def(nidx):
    lines = [l.rstrip("\n") for l in open(os.path.join(os.path.dirname(__file__), "..", "tests", "adv-base", "eqtype.base"))]
    i = next(k for k, l in enumerate(lines) if l.startswith('{"inductive"'))
    new = [
        '{"in":16,"str":{"pre":0,"str":"Rel"}}',
        '{"il":3,"succ":0}',
        '{"il":4,"max":[1,3]}',
        '{"ie":42,"sort":4}',
        '{"forallE":{"binderInfo":"default","body":42,"name":3,"type":0},"ie":43}',
        '{"forallE":{"binderInfo":"default","body":3,"name":8,"type":1},"ie":44}',
        '{"ie":45,"lam":{"binderInfo":"default","body":44,"name":3,"type":0}}',
        '{"def":{"all":[16],"hints":"abbrev","levelParams":[2],"name":16,"safety":"safe","type":43,"value":45}}',
        '{"const":{"name":16,"us":[1]},"ie":46}',
        '{"app":{"arg":2,"fn":46},"ie":47}',
        '{"forallE":{"binderInfo":"default","body":47,"name":4,"type":1},"ie":48}',
        '{"forallE":{"binderInfo":"implicit","body":48,"name":3,"type":0},"ie":49}',
    ]
    ind = json.loads(lines[i])
    ind["inductive"]["types"][0]["type"] = 49
    ind["inductive"]["types"][0]["numIndices"] = nidx
    return lines[:i] + new + [json.dumps(ind, separators=(",", ":"))] + lines[i + 1:]
open(f"{out}/good_indices_after_delta.ndjson", "w").write("\n".join(eq_via_def(1)) + "\n")
open(f"{out}/bad_indices_after_delta_count.ndjson", "w").write("\n".join(eq_via_def(0)) + "\n")
print("inductive type vectors written")

# ---- projections of one field compare their structures lazily (milestone
# 6, Lean's lazy_delta_proj_reduction, Pestka's eqProj): S b := mk true b
# (abbrev, unfolded without comparing arguments); under variables b c,
# (S b).1 = (S c).1 holds (good) and (S b).2 = (S c).2 does not (bad)
for good in (True, False):
    w, cq, _, cs = twobool_cases(good)
    cB = w.const(1); cTB = w.const(10); b = w.name("b"); c = w.name("c"); h = w.name("h")
    S = w.name("S"); w.defn(S, w.pi(b, cB, cTB), w.lam(b, cB, w.app(w.app(w.const(11), w.const(3)), w.bvar(0))), h="abbrev")
    i = 0 if good else 1
    pb = w.ex(proj={"typeName": 10, "idx": i, "struct": w.app(w.const(S), w.bvar(0))})
    pc = w.ex(proj={"typeName": 10, "idx": i, "struct": w.app(w.const(S), w.bvar(1))})
    pc2 = w.ex(proj={"typeName": 10, "idx": i, "struct": w.app(w.const(S), w.bvar(2))})
    pb1 = w.ex(proj={"typeName": 10, "idx": i, "struct": w.app(w.const(S), w.bvar(1))})
    # (b c : Bool) -> Q (S b).i -> Q (S c).i  :=  fun b c h => h
    ty = w.pi(b, cB, w.pi(c, cB, w.pi(h, w.app(cq, pb1), w.app(cq, pc))))
    val = w.lam(b, cB, w.lam(c, cB, w.lam(h, w.app(cq, pb1), w.bvar(0))))
    w.thm(w.name("t5"), ty, val)
    w.save(f"{out}/{'good' if good else 'bad'}_proj_structs_lazy.ndjson")
print("milestone 6 vectors written")

# ---- closed pairs kept across declarations by name (milestone 8). I := id
# on N (one unfolding). t1 : Q (I n1) -> Q n1 stores the closed pair
# (Q (I n1), Q n1); a later theorem compares another pair with the same
# heads, (Q (I n2), Q n1) (bad), or the same pair again (good). Then the
# same with variables, whose pairs must never be kept: t3 : (a : N) ->
# Q (I a) -> Q a, t4 : (a b : N) -> Q (I a) -> Q b (bad), and t4 with a let
# whose value differs (let a := n2 in Q (I a) -> Q n1, bad).
def closed_pair_base():
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    I = w.name("I"); w.defn(I, w.pi(x, cN, cN), w.lam(x, cN, w.bvar(0)), h={"regular": 1}); cI = w.const(I)
    h = w.name("h")
    def imp(t, a, b):
        lhs = w.app(cQ, a); rhs = w.app(cQ, b)
        w.thm(w.name(t), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    imp("t1", w.app(cI, c1), c1)
    return w, cN, cQ, cI, c1, c2, h, imp
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
imp("t2", w.app(cI, c2), c1); w.save(f"{out}/bad_named_pair_other.ndjson")
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
imp("t2", w.app(cI, c1), c1); w.save(f"{out}/good_named_pair_reused.ndjson")
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
a = w.name("a"); b = w.name("b")
lhs = w.app(cQ, w.app(cI, w.bvar(0))); rhs = w.app(cQ, w.bvar(0))
w.thm(w.name("t3"), w.pi(a, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1)))), w.lam(a, cN, w.lam(h, lhs, w.bvar(0))))
lhs4 = w.app(cQ, w.app(cI, w.bvar(1)))
w.thm(w.name("t4"), w.pi(a, cN, w.pi(b, cN, w.pi(h, lhs4, w.app(cQ, w.bvar(1))))), w.lam(a, cN, w.lam(b, cN, w.lam(h, lhs4, w.bvar(0)))))
w.save(f"{out}/bad_named_pair_open.ndjson")
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
a = w.name("a")
lhs = w.app(cQ, w.app(cI, w.bvar(0)))
body = w.lam(h, lhs, w.bvar(0))
w.thm(w.name("t5"), w.pi(h, w.app(cQ, w.app(cI, c2)), w.app(cQ, c1)), w.ex(letE={"name": a, "type": cN, "value": c2, "body": body, "nondep": False}))
w.save(f"{out}/bad_named_pair_let.ndjson")
print("milestone 8 vectors written")

# ---- open pairs kept across declarations (milestone 9, SK_POPEN=1): a
# binder's variable is PV(type name, slot). t3 : (a : N) -> Q (I a) -> Q a
# keeps the open pair (Q (I PV0), Q PV0). Later declarations ask pairs that
# a wrong identity would confuse with it.
def open_base(w, cN, cQ, cI, h, two=False):
    a = w.name("a")
    lhs = w.app(cQ, w.app(cI, w.bvar(0)))
    w.thm(w.name("t3"), w.pi(a, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1)))), w.lam(a, cN, w.lam(h, lhs, w.bvar(0))))
    return a
# 1. two variables of one type open at once (slots 0 and 1)
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base(); a = open_base(w, cN, cQ, cI, h); b = w.name("b")
lhs = w.app(cQ, w.app(cI, w.bvar(1)))
w.thm(w.name("t4"), w.pi(a, cN, w.pi(b, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1))))), w.lam(a, cN, w.lam(b, cN, w.lam(h, lhs, w.bvar(0)))))
w.save(f"{out}/bad_open_pair_two_slots.ndjson")
# 2. the same statement again under other binder names: the kept pair (good)
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base(); a = open_base(w, cN, cQ, cI, h); z = w.name("z")
lhs = w.app(cQ, w.app(cI, w.bvar(0)))
w.thm(w.name("t4"), w.pi(z, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1)))), w.lam(z, cN, w.lam(h, lhs, w.bvar(0))))
w.save(f"{out}/good_open_pair_reused.ndjson")
# 3. binders swapped: K2 a b := a; t5 : (a b : N) -> Q (K2 a b) -> Q a
# keeps (Q (K2 PV0 PV1), Q PV0); t6 : (a b : N) -> Q (K2 a b) -> Q b
# (bad), and t6 with the same pair as t5 (good)
for good in (False, True):
    w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
    a = w.name("a"); b = w.name("b"); x = w.name("x"); y = w.name("y")
    K2 = w.name("K2"); w.defn(K2, w.pi(x, cN, w.pi(y, cN, cN)), w.lam(x, cN, w.lam(y, cN, w.bvar(1))), h={"regular": 1}); cK = w.const(K2)
    lhs = w.app(cQ, w.app(w.app(cK, w.bvar(1)), w.bvar(0)))
    w.thm(w.name("t5"), w.pi(a, cN, w.pi(b, cN, w.pi(h, lhs, w.app(cQ, w.bvar(2))))), w.lam(a, cN, w.lam(b, cN, w.lam(h, lhs, w.bvar(0)))))
    rhs = w.app(cQ, w.bvar(2) if good else w.bvar(1))
    w.thm(w.name("t6"), w.pi(b, cN, w.pi(a, cN, w.pi(h, lhs, rhs))), w.lam(b, cN, w.lam(a, cN, w.lam(h, lhs, w.bvar(0)))))
    w.save(f"{out}/{'good' if good else 'bad'}_open_pair_swapped.ndjson")
# 4. a dependent variable type: P : N -> Prop, R : (n : N) -> P n -> Prop,
# J n p := p (def). t7 : (a b : N) (p : P a) -> R a (J a p) -> R a p keeps
# a pair over p = PV(P PV0, 0); t8 has q : P b and asks R b (J b q) -> R a q
# shaped pairs that differ only in which variable q's type holds (bad: R a q
# is ill-typed, the check must still fail)
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
prop = w.sort(0); n = w.name("n"); p_ = w.name("p"); a = w.name("a"); b = w.name("b"); q = w.name("q")
P = w.name("P"); w.axiom(P, w.pi(n, cN, prop)); cP = w.const(P)
R = w.name("R"); w.axiom(R, w.pi(n, cN, w.pi(p_, w.app(cP, w.bvar(0)), prop))); cR = w.const(R)
J = w.name("J"); w.defn(J, w.pi(n, cN, w.pi(p_, w.app(cP, w.bvar(0)), w.app(cP, w.bvar(1)))), w.lam(n, cN, w.lam(p_, w.app(cP, w.bvar(0)), w.bvar(0))), h={"regular": 1}); cJ = w.const(J)
# under a b p (p : P a = bvar 0, b = 1, a = 2)
lhs = w.app(w.app(cR, w.bvar(2)), w.app(w.app(cJ, w.bvar(2)), w.bvar(0)))
lhs_h = w.app(w.app(cR, w.bvar(3)), w.app(w.app(cJ, w.bvar(3)), w.bvar(1)))
rhs_h = w.app(w.app(cR, w.bvar(3)), w.bvar(1))
w.thm(w.name("t7"), w.pi(a, cN, w.pi(b, cN, w.pi(p_, w.app(cP, w.bvar(1)), w.pi(h, lhs, rhs_h)))),
      w.lam(a, cN, w.lam(b, cN, w.lam(p_, w.app(cP, w.bvar(1)), w.lam(h, lhs, w.bvar(0))))))
# t8: q : P b (bvar 1 under a b), R a (J a q) is ill-typed
lhs8 = w.app(w.app(cR, w.bvar(2)), w.app(w.app(cJ, w.bvar(2)), w.bvar(0)))
w.thm(w.name("t8"), w.pi(a, cN, w.pi(b, cN, w.pi(q, w.app(cP, w.bvar(0)), w.pi(h, lhs8, rhs_h)))),
      w.lam(a, cN, w.lam(b, cN, w.lam(q, w.app(cP, w.bvar(0)), w.lam(h, lhs8, w.bvar(0))))))
w.save(f"{out}/bad_open_pair_dependent.ndjson")
# 5. universe parameters: G.{u} (α : Sort u) (x : α) : Prop, Id.{u} α x := x.
# t9.{u} : (α : Sort u) (x : α) -> G α (Id α x) -> G α x keeps an open
# pair under u. t10 repeats it with u not declared (bad), or under v (good).
for kind in ("bad", "good"):
    w, prop, f = base()
    u = w.name("u"); lu = lvl_param(w, u); v = w.name("v"); lv = lvl_param(w, v)
    al = w.name("α"); x = w.name("x"); G = w.name("G"); Id = w.name("Id")
    w.axiom(G, w.pi(al, w.sort(lu), w.pi(x, w.bvar(0), w.sort(0))), lp=(u,))
    w.defn(Id, w.pi(al, w.sort(lu), w.pi(x, w.bvar(0), w.bvar(1))), w.lam(al, w.sort(lu), w.lam(x, w.bvar(0), w.bvar(0))), lp=(u,), h={"regular": 1})
    def stmt(l):
        cG = w.const(G, [l]); cId = w.const(Id, [l]); hh = w.name("h")
        lhs = w.app(w.app(cG, w.bvar(1)), w.app(w.app(cId, w.bvar(1)), w.bvar(0)))
        ty = w.pi(al, w.sort(l), w.pi(x, w.bvar(0), w.pi(hh, lhs, w.app(w.app(cG, w.bvar(2)), w.bvar(1)))))
        val = w.lam(al, w.sort(l), w.lam(x, w.bvar(0), w.lam(hh, lhs, w.bvar(0))))
        return ty, val
    ty, val = stmt(lu); w.thm(w.name("t9"), ty, val, lp=(u,))
    if kind == "bad":
        w.thm(w.name("t10"), ty, val)
    else:
        ty2, val2 = stmt(lv); w.thm(w.name("t10"), ty2, val2, lp=(v,))
    w.save(f"{out}/{kind}_open_pair_levels.ndjson")
# 6. a pair found in an unsafe definition is not kept: X (unsafe) has the
# statement of t4 in vector 1 as its type; then t4 itself (bad)
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base(); a = w.name("a"); b = w.name("b")
lhs = w.app(cQ, w.app(cI, w.bvar(1)))
ty4 = w.pi(a, cN, w.pi(b, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1)))))
val4 = w.lam(a, cN, w.lam(b, cN, w.lam(h, lhs, w.bvar(0))))
w.defn(w.name("X"), ty4, val4, safety="unsafe")
w.thm(w.name("t4"), ty4, val4)
w.save(f"{out}/bad_open_pair_unsafe.ndjson")
# 7. back in order (namespace order): B.y (declaration before A.K) states
# (a : N) -> Q (A.K a) -> Q a; A.w after A.K the same, kept first under
# SK_ORDER=ns; B.y must still be rejected
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
a1 = w.name("A.first"); w.axiom(a1, w.sort(0))
K = w.name("A.K"); cK = w.const(K); a = w.name("a"); x = w.name("x")
lhs = w.app(cQ, w.app(cK, w.bvar(0)))
ty = w.pi(a, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1)))); val = w.lam(a, cN, w.lam(h, lhs, w.bvar(0)))
w.thm(w.name("B.y"), ty, val)
w.defn(K, w.pi(x, cN, cN), w.lam(x, cN, w.bvar(0)), h={"regular": 1})
w.thm(w.name("A.w"), ty, val)
w.save(f"{out}/bad_open_pair_back_in_order.ndjson")
print("milestone 9 vectors written")

# ---- milestone 10: sessions (arena and caches kept across declarations)
def sess_base():
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    return w, prop, one, cN, c1, c2
# 1. a fact from an unsafe declaration: X (unsafe) : N -> N := fun a => U a
# with U an unsafe axiom; Y (safe) has the same value (the open term `U a`
# is shared, so its check-mode result would be found): Y must be rejected
for saf in ("unsafe", "partial"):
    w, prop, one, cN, c1, c2 = sess_base()
    U = w.name("U"); x = w.name("x")
    w.lines.append(json.dumps({"axiom": {"name": U, "type": w.pi(x, cN, cN), "levelParams": [], "isUnsafe": True}}))
    a = w.name("a"); ty = w.pi(a, cN, cN)
    body = w.app(w.const(U), w.bvar(0)); val = w.lam(a, cN, body)
    if saf == "unsafe":
        w.defn(w.name("X"), ty, val, safety="unsafe")
    else:
        # a partial definition P := fun a => U a is itself ill-formed (U is
        # unsafe); the partial one here is fine and uses only N
        P = w.name("P"); w.defn(P, ty, w.lam(a, cN, w.bvar(0)), safety="partial")
        val = w.lam(a, cN, w.app(w.const(P), w.bvar(0)))
        w.defn(w.name("X"), ty, val, safety="partial")
    w.defn(w.name("Y"), ty, val)
    w.save(f"{out}/bad_sess_{saf}_fact.ndjson")
# 2. the same variable slot with different types across declarations:
# t1 : (a : N) -> G N a -> G N a, then t2 : (a : M) -> G N a -> G N a with
# a : M (ill-typed: G N expects an N); a variable chosen by slot alone would
# be t1's a : N
w, prop, one, cN, c1, c2 = sess_base()
M = w.name("M"); w.axiom(M, w.sort(one)); cM = w.const(M)
G = w.name("G"); T = w.name("T"); x = w.name("x")
w.axiom(G, w.pi(T, w.sort(one), w.pi(x, w.bvar(0), prop)))
a = w.name("a"); h = w.name("h"); cG = w.const(G)
lhs = w.app(w.app(cG, cN), w.bvar(0))
for nm, dom, kind in (("t1", cN, "ok"), ("t2", cM, "bad")):
    lhs = w.app(w.app(cG, cN), w.bvar(0))
    w.thm(w.name(nm), w.pi(a, dom, w.pi(h, lhs, w.app(w.app(cG, cN), w.bvar(1)))), w.lam(a, dom, w.lam(h, lhs, w.bvar(0))))
w.save(f"{out}/bad_sess_slot_types.ndjson")
w.lines.pop()
w.thm(w.name("t2"), w.pi(a, cM, w.pi(h, w.app(w.app(cG, cM), w.bvar(0)), w.app(w.app(cG, cM), w.bvar(1)))), w.lam(a, cM, w.lam(h, w.app(w.app(cG, cM), w.bvar(0)), w.bvar(0))))
w.save(f"{out}/good_sess_slot_types.ndjson")
# 3. a fact from a failed declaration: t1 is ill-typed (h : Q a used as
# Q (I a) ... and its comparison found I a = a); t2 states the same and is
# fine: the run is rejected at t1, at 1 and 4 workers, in both orders
w, cN, cQ, cI, c1, c2, h, imp = closed_pair_base()
a = w.name("a")
lhs = w.app(cQ, w.app(cI, w.bvar(0)))
w.thm(w.name("t3"), w.pi(a, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1)))), w.lam(a, cN, w.lam(h, lhs, w.const(w.name("t1")))))
w.thm(w.name("t4"), w.pi(a, cN, w.pi(h, lhs, w.app(cQ, w.bvar(1)))), w.lam(a, cN, w.lam(h, lhs, w.bvar(0))))
w.save(f"{out}/bad_sess_failed_fact.ndjson")
# 4. level parameters in an open shared term: t1.{u} checks the open term
# `G.{u} α x` (under binders α x); t2 without u has the same statement
for kind in ("bad", "good"):
    w, prop, f = base()
    u = w.name("u"); lu = lvl_param(w, u)
    al = w.name("α"); x = w.name("x"); G = w.name("G"); h = w.name("h")
    w.axiom(G, w.pi(al, w.sort(lu), w.pi(x, w.bvar(0), prop)), lp=(u,))
    one = w.succ(0)
    gax = w.app(w.app(w.const(G, [lu]), w.bvar(1)), w.bvar(0))
    gax2 = w.app(w.app(w.const(G, [lu]), w.bvar(2)), w.bvar(1))
    ty = w.pi(al, w.sort(lu), w.pi(x, w.bvar(0), w.pi(h, gax, gax2)))
    val = w.lam(al, w.sort(lu), w.lam(x, w.bvar(0), w.lam(h, gax, w.bvar(0))))
    w.thm(w.name("t1"), ty, val, lp=(u,))
    w.thm(w.name("t2"), ty, val, lp=(() if kind == "bad" else (u,)))
    w.save(f"{out}/{kind}_sess_levels_open.ndjson")
print("milestone 10 vectors written")

# ---- milestone 11: applications made canonical neutral values at once
# (canon_app), including a variable head bound to a neutral value.
# (fun g => Q (g n1)) K  against  Q (K n1) (good) / Q (K n2) (bad)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); h = w.name("h"); g = w.name("g")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    K = w.name("K"); w.axiom(K, w.pi(x, cN, cN)); cK = w.const(K)
    lhs = w.app(w.lam(g, w.pi(x, cN, cN), w.app(cQ, w.app(w.bvar(0), c1))), cK)
    rhs = w.app(cQ, w.app(cK, c1 if good else c2))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_canon_var_head.ndjson")
# a variable bound to a partial application: (fun g => Q (g n2)) (F n1)
# against Q (F n1 n2) (good) / Q (F n2 n1) (bad): the arguments keep their order
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); y = w.name("y"); h = w.name("h"); g = w.name("g")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    F = w.name("F"); w.axiom(F, w.pi(x, cN, w.pi(y, cN, cN))); cF = w.const(F)
    lhs = w.app(w.lam(g, w.pi(x, cN, cN), w.app(cQ, w.app(w.bvar(0), c2))), w.app(cF, c1))
    rhs = w.app(cQ, w.app(w.app(cF, c1), c2) if good else w.app(w.app(cF, c2), c1))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_canon_var_partial.ndjson")
# a head constant declared later: t : P := B p, B declared after t
w, prop, f = base()
P = w.name("P"); w.axiom(P, prop); cP = w.const(P)
p = w.name("p"); w.axiom(p, cP)
x = w.name("x")
B = w.name("B"); cB = w.const(B)
w.defn(w.name("t"), cP, w.app(cB, w.const(p)), h={"regular": 1})
w.axiom(B, w.pi(x, cP, cP))
w.save(f"{out}/bad_canon_later_constant_head.ndjson")
# the same open application in two declarations under different level
# parameters: t1.{u} and t2.{v} state G.{u} α x -> G.{u} α x; t3.{u v}
# claims G.{u} = G.{v} on it (bad) / the same level (good)
for good in (True, False):
    w, prop, f = base()
    u = w.name("u"); v = w.name("v"); lu = lvl_param(w, u); lv = lvl_param(w, v)
    al = w.name("α"); x = w.name("x"); G = w.name("G"); h = w.name("h")
    w.axiom(G, w.pi(al, w.sort(0), w.pi(x, w.bvar(0), prop)), lp=(u,))
    def gx(l, a, b): return w.app(w.app(w.const(G, [l]), w.bvar(a)), w.bvar(b))
    for nm, l in (("t1", lu), ("t2", lv)):
        ty = w.pi(al, w.sort(0), w.pi(x, w.bvar(0), w.pi(h, gx(l, 1, 0), gx(l, 2, 1))))
        val = w.lam(al, w.sort(0), w.lam(x, w.bvar(0), w.lam(h, gx(l, 1, 0), w.bvar(0))))
        w.thm(w.name(nm), ty, val, lp=((u,) if nm == "t1" else (v,)))
    l2 = lu if good else lv
    ty = w.pi(al, w.sort(0), w.pi(x, w.bvar(0), w.pi(h, gx(lu, 1, 0), gx(l2, 2, 1))))
    val = w.lam(al, w.sort(0), w.lam(x, w.bvar(0), w.lam(h, gx(lu, 1, 0), w.bvar(0))))
    w.thm(w.name("t3"), ty, val, lp=(u, v))
    w.save(f"{out}/{'good' if good else 'bad'}_canon_levels_sessions.ndjson")
print("milestone 11 vectors written")

# ---- milestone 12: neutral values hash-consed by head and whole spine
# (one slice per neutral, one probe). Equal arguments under different
# heads, a spine against its prefix, long spines, and a table that grows
# (rehashes) within a session.
# heads: Q (F n1 n2) -> Q (G n1 n2) (bad) / Q (F n1 n2) -> Q ((fun g => g n2) (F n1)) (good)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); y = w.name("y"); h = w.name("h"); g = w.name("g")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    F = w.name("F"); w.axiom(F, w.pi(x, cN, w.pi(y, cN, cN))); cF = w.const(F)
    G = w.name("G"); w.axiom(G, w.pi(x, cN, w.pi(y, cN, cN))); cG = w.const(G)
    lhs = w.app(cQ, w.app(w.app(cF, c1), c2))
    if good:
        rhs = w.app(cQ, w.app(w.lam(g, w.pi(x, cN, cN), w.app(w.bvar(0), c2)), w.app(cF, c1)))
    else:
        rhs = w.app(cQ, w.app(w.app(cG, c1), c2))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m12_heads.ndjson")
# a spine and its prefix: Q2 (F n1) -> Q2 (fun x => F n1 x) (good, eta) /
# Q2 (F n1) -> Q2 (fun x => F n1 n2) (bad)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q2 = w.name("Q2"); x = w.name("x"); y = w.name("y"); h = w.name("h")
    w.axiom(Q2, w.pi(x, w.pi(y, cN, cN), prop)); cQ2 = w.const(Q2)
    F = w.name("F"); w.axiom(F, w.pi(x, cN, w.pi(y, cN, cN))); cF = w.const(F)
    lhs = w.app(cQ2, w.app(cF, c1))
    rhs = w.app(cQ2, w.lam(x, cN, w.app(w.app(cF, c1), w.bvar(0) if good else c2)))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m12_prefix.ndjson")
# a long spine (12 arguments, past the inline buffers): the last argument
# differs (bad) / the same application built through a variable head bound
# to a partial application of 6 arguments (good)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); h = w.name("h"); g = w.name("g")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    ty = cN
    for _ in range(12):
        ty = w.pi(x, cN, ty)
    F = w.name("F12"); w.axiom(F, ty); cF = w.const(F)
    def appn(hd, args):
        for a in args:
            hd = w.app(hd, a)
        return hd
    lhs = w.app(cQ, appn(cF, [c1] * 12))
    if good:
        gty = cN
        for _ in range(6):
            gty = w.pi(x, cN, gty)
        rhs = w.app(cQ, w.app(w.lam(g, gty, appn(w.bvar(0), [c1] * 6)), appn(cF, [c1] * 6)))
    else:
        rhs = w.app(cQ, appn(cF, [c1] * 11 + [c2]))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m12_long.ndjson")
# many neutrals in one session (the table grows and rehashes): 30 x 30
# theorems Q (F a_i a_j) -> Q (F a_i a_j), then Q (F a_3 a_5) -> Q (F a_5 a_3)
# (bad) / Q (F a_3 a_5) -> Q (F a_3 a_5) (good)
for good in (True, False):
    w, prop, f = base()
    one = w.succ(0)
    N = w.name("N"); w.axiom(N, w.sort(one)); cN = w.const(N)
    xs = []
    for i in range(30):
        a = w.name(f"a{i}"); w.axiom(a, cN); xs.append(w.const(a))
    Q = w.name("Q"); x = w.name("x"); y = w.name("y"); h = w.name("h")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    F = w.name("F"); w.axiom(F, w.pi(x, cN, w.pi(y, cN, cN))); cF = w.const(F)
    def qf(i, j): return w.app(cQ, w.app(w.app(cF, xs[i]), xs[j]))
    for i in range(30):
        for j in range(30):
            w.thm(w.name(f"t{i}_{j}"), w.pi(h, qf(i, j), qf(i, j)), w.lam(h, qf(i, j), w.bvar(0)))
    lhs = qf(3, 5); rhs = qf(3, 5) if good else qf(5, 3)
    w.thm(w.name("last"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m12_grow.ndjson")
print("milestone 12 vectors written")

# ---- milestone 12: the wider surely-not-proof test (Pestka's
# notProofByHead). A wrong "not a proof" can only lose proof irrelevance
# (reject good), so the good ones are the point: proofs whose type ends in a
# type variable bound with Prop / Sort u, a variable head applied to
# arguments, a partial application into Prop; bad: the same shapes at Type.
def np_base(w):
    one, cN, c1, c2 = nat_like(w)
    P = w.name("P"); w.axiom(P, w.sort(0)); cP = w.const(P)
    p1 = w.name("p1"); w.axiom(p1, cP); p2 = w.name("p2"); w.axiom(p2, cP)
    return one, cN, c1, c2, cP, w.const(p1), w.const(p2)
for kind in ("prop", "sortu", "type"):
    w, prop, f = base()
    one, cN, c1, c2, cP, q1, q2 = np_base(w)
    x = w.name("x"); g = w.name("γ"); h = w.name("h"); u = w.name("u")
    if kind == "sortu":
        lu = lvl_param(w, u)
        F = w.name("idf"); w.axiom(F, w.pi(g, w.sort(lu), w.pi(x, w.bvar(0), w.bvar(1)), "implicit"), lp=(u,))
        cF = w.const(F, [0])
    else:
        F = w.name("idf"); w.axiom(F, w.pi(g, w.sort(0 if kind == "prop" else one), w.pi(x, w.bvar(0), w.bvar(1)), "implicit"))
        cF = w.const(F)
    ty, a1, a2 = (cN, c1, c2) if kind == "type" else (cP, q1, q2)
    Q = w.name("Q"); w.axiom(Q, w.pi(x, ty, prop)); cQ = w.const(Q)
    lhs = w.app(cQ, w.app(w.app(cF, ty), a1)); rhs = w.app(cQ, w.app(w.app(cF, ty), a2))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'bad' if kind == 'type' else 'good'}_np_typevar_{kind}.ndjson")
# a variable head with an argument: forall (k : N -> P), Q (k n1) -> Q (k n2)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2, cP, q1, q2 = np_base(w)
    x = w.name("x"); k = w.name("k"); h = w.name("h")
    cod = cP if good else cN
    Q = w.name("Q"); w.axiom(Q, w.pi(x, cod, prop)); cQ = w.const(Q)
    lhs = w.app(cQ, w.app(w.bvar(0), c1)); rhs = w.app(cQ, w.app(w.bvar(1), c2))
    w.thm(w.name("t"), w.pi(k, w.pi(x, cN, cod), w.pi(h, lhs, rhs)), w.lam(k, w.pi(x, cN, cod), w.lam(h, lhs, w.bvar(0))))
    w.save(f"{out}/{'good' if good else 'bad'}_np_fvar_args.ndjson")
# a partial application into Prop: R (g n1) -> R (g n2), g : N -> N -> P
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2, cP, q1, q2 = np_base(w)
    x = w.name("x"); y = w.name("y"); h = w.name("h")
    cod = cP if good else cN
    G = w.name("g"); w.axiom(G, w.pi(x, cN, w.pi(y, cN, cod))); cG = w.const(G)
    R = w.name("R"); w.axiom(R, w.pi(x, w.pi(y, cN, cod), prop)); cR = w.const(R)
    lhs = w.app(cR, w.app(cG, c1)); rhs = w.app(cR, w.app(cG, c2))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_np_partial.ndjson")
print("milestone 12 not-proof vectors written")
# a variable whose type is a proposition constant (x : P, P : Prop) is a
# proof: forall (Q : P -> Prop) (x y : P), Q x -> Q y (good; Q a variable,
# so no proof-argument skip of a constant head decides it); at N (bad)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2, cP, q1, q2 = np_base(w)
    q = w.name("Q"); x = w.name("x"); y = w.name("y"); h = w.name("h")
    ty = cP if good else cN
    qt = w.pi(x, ty, prop)
    lhs = w.app(w.bvar(2), w.bvar(1)); rhs = w.app(w.bvar(3), w.bvar(1))
    stmt = w.pi(q, qt, w.pi(x, ty, w.pi(y, ty, w.pi(h, lhs, rhs))))
    w.thm(w.name("t"), stmt, w.lam(q, qt, w.lam(x, ty, w.lam(y, ty, w.lam(h, lhs, w.bvar(0))))))
    w.save(f"{out}/{'good' if good else 'bad'}_np_fvar_prop_const.ndjson")
print("milestone 12 not-proof vectors (2) written")

# ---- milestone 13: environments cut to the entries a term reads (frames
# hash-consed by content, a direct-mapped (environment, mask) memo).
# A closure made under two environments that differ in what it reads must
# stay two values; the same closure under environments that differ only in
# unread entries may be one. Every closure below has an entry it does not
# read (v), so a frame is built for it.
def k_base(w):
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); y = w.name("y"); z = w.name("z"); h = w.name("h"); v = w.name("v")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, w.pi(y, cN, cN), w.sort(0))); cQ = w.const(Q)
    return one, cN, c1, c2, cQ, x, y, z, h, v
# env: Q ((fun y v z => y) n1 n1) -> Q ((fun y v z => y) n2 n1) (bad) / n1 n2 (good)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2, cQ, x, y, z, h, v = k_base(w)
    K = w.lam(y, cN, w.lam(v, cN, w.lam(z, cN, w.bvar(2))))
    lhs = w.app(cQ, w.app(w.app(K, c1), c1))
    rhs = w.app(cQ, w.app(w.app(K, c1), c2)) if good else w.app(cQ, w.app(w.app(K, c2), c1))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m13_frame_env.ndjson")
# order: Q (fun z => F y w) under (y, v, w) = (n1, _, n2) against (n2, _, n1):
# the same values at swapped positions (bad) / the same order (good)
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2, cQ, x, y, z, h, v = k_base(w)
    u = w.name("u")
    F = w.name("F"); w.axiom(F, w.pi(x, cN, w.pi(y, cN, cN))); cF = w.const(F)
    K = w.lam(y, cN, w.lam(v, cN, w.lam(u, cN, w.lam(z, cN, w.app(w.app(cF, w.bvar(3)), w.bvar(1))))))
    def k3(a, b, c): return w.app(w.app(w.app(K, a), b), c)
    lhs = w.app(cQ, k3(c1, c1, c2))
    rhs = w.app(cQ, k3(c1, c2, c2) if good else k3(c2, c1, c1))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m13_frame_order.ndjson")
# sessions: 40 theorems Q (K a_i a_0) -> Q (K a_i a_0) (frames of every
# session at the same ids), then Q (K a_3 a_0) -> Q (K a_5 a_0) (bad) / a_3 (good)
for good in (True, False):
    w, prop, f = base()
    one = w.succ(0)
    N = w.name("N"); w.axiom(N, w.sort(one)); cN = w.const(N)
    xs = []
    for i in range(40):
        a = w.name(f"a{i}"); w.axiom(a, cN); xs.append(w.const(a))
    x = w.name("x"); y = w.name("y"); z = w.name("z"); h = w.name("h"); v = w.name("v")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, w.pi(y, cN, cN), w.sort(0))); cQ = w.const(Q)
    K = w.lam(y, cN, w.lam(v, cN, w.lam(z, cN, w.bvar(2))))
    def qk(i): return w.app(cQ, w.app(w.app(K, xs[i]), xs[0]))
    for i in range(40):
        w.thm(w.name(f"t{i}"), w.pi(h, qk(i), qk(i)), w.lam(h, qk(i), w.bvar(0)))
    lhs = qk(3); rhs = qk(3) if good else qk(5)
    w.thm(w.name("last"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m13_frame_sessions.ndjson")
print("milestone 13 vectors written")

# ---- milestone 16: level lists canonical by MAIN side offset (a list that
# occurs in MAIN is named by the offset of its content; a list made by
# substitution is looked up there first, a list MAIN lacks is pooled), and
# the substitution memo keyed by (side offset, substitution).
# 1. g.{u} := fun x => H.{u} x. t.{u v}: Q (g.{v} n1) -> Q (H.{u} n1): the
# substituted list [v] is MAIN's [v], not [u] (bad); with g.{u} (good).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); h = w.name("h")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    u = w.name("u"); v = w.name("v"); lu = lvl_param(w, u); lv = lvl_param(w, v)
    H = w.name("H"); w.axiom(H, w.pi(x, cN, cN), lp=(u,))
    g = w.name("g"); w.defn(g, w.pi(x, cN, cN), w.lam(x, cN, w.app(w.const(H, [lu]), w.bvar(0))), lp=(u,), h={"regular": 1})
    w.axiom(w.name("Hv"), w.app(cQ, w.app(w.const(H, [lv]), c1)), lp=(v,))  # [v] occurs in MAIN
    lhs = w.app(cQ, w.app(w.const(g, [lu if good else lv]), c1))
    rhs = w.app(cQ, w.app(w.const(H, [lu]), c1))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)), lp=(u, v))
    w.save(f"{out}/{'good' if good else 'bad'}_m16_subst_main_list.ndjson")
# 2. lists MAIN lacks on both sides: g.{u} := H.{succ u}, k.{w} := H.{succ
# (succ w)}; t.{v}: g.{succ v} and k.{v} both give H.{succ (succ v)}, a list
# made only by substitution (good); k.{succ v} gives one more succ (bad).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); h = w.name("h")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    u = w.name("u"); v = w.name("v"); ww = w.name("w")
    lu = lvl_param(w, u); lv = lvl_param(w, v); lw = lvl_param(w, ww)
    su = w.succ(lu); sw = w.succ(lw); ssw = w.succ(sw); sv = w.succ(lv); ssv = w.succ(sv)
    H = w.name("H"); w.axiom(H, w.pi(x, cN, cN), lp=(u,))
    g = w.name("g"); w.defn(g, w.pi(x, cN, cN), w.lam(x, cN, w.app(w.const(H, [su]), w.bvar(0))), lp=(u,), h={"regular": 1})
    k = w.name("k"); w.defn(k, w.pi(x, cN, cN), w.lam(x, cN, w.app(w.const(H, [ssw]), w.bvar(0))), lp=(ww,), h={"regular": 1})
    lhs = w.app(cQ, w.app(w.const(g, [sv]), c1))
    rhs = w.app(cQ, w.app(w.const(k, [lv if good else sv]), c1))
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)), lp=(v,))
    w.save(f"{out}/{'good' if good else 'bad'}_m16_pool_lists.ndjson")
# 3. one substitution, two MAIN lists of the same length: g.{u v} :=
# P (H.{u} n1) (H.{v} n1) where P a b := Q a -> Q b; at [w, w] it is
# Q (H.{w} n1) -> Q (H.{w} n1) (good); t claims g.{w z} is that (bad: the
# memo must keep [u] and [v] apart under one substitution).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    Q = w.name("Q"); x = w.name("x"); y = w.name("y"); h = w.name("h")
    w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
    u = w.name("u"); v = w.name("v"); ww = w.name("w"); zz = w.name("z")
    lu = lvl_param(w, u); lv = lvl_param(w, v); lw = lvl_param(w, ww); lz = lvl_param(w, zz)
    H = w.name("H"); w.axiom(H, w.pi(x, cN, cN), lp=(u,))
    imp = w.pi(h, w.app(cQ, w.bvar(1)), w.app(cQ, w.bvar(1)))
    P = w.name("P"); w.defn(P, w.pi(x, cN, w.pi(y, cN, prop)), w.lam(x, cN, w.lam(y, cN, imp)), h={"regular": 1})
    body = w.app(w.app(w.const(P), w.app(w.const(H, [lu]), c1)), w.app(w.const(H, [lv]), c1))
    g = w.name("g"); w.defn(g, prop, body, lp=(u, v), h={"regular": 2})
    hw = w.app(cQ, w.app(w.const(H, [lw]), c1))
    gv = w.const(g, [lw, lw] if good else [lw, lz])
    # t.{w z} : g.{..} := fun h => h, typed as Q (H.{w} n1) -> Q (H.{w} n1)
    w.thm(w.name("t"), gv, w.lam(h, hw, w.bvar(0)), lp=(ww, zz))
    w.save(f"{out}/{'good' if good else 'bad'}_m16_memo_two_lists.ndjson")
print("milestone 16 vectors written")

# ---- milestone 17: the same-head argument probe under non-regular heads
# (abbreviations: projection functions, instances, user abbrevs), within a
# step budget; a probe out of budget is "not equal" and both sides unfold.
# 1. levels: B.{u} : N -> Prop an axiom, K.{u} x := B.{u} x (abbrev).
# t.{u v} : K.{u} n1 -> K.{v} n1 (bad: the arguments are equal, the levels
# are not); K.{u} (G n1) -> K.{u} n1 with G the identity (good: the probe
# compares G n1 with n1).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); h = w.name("h")
    u = w.name("u"); v = w.name("v"); lu = lvl_param(w, u); lv = lvl_param(w, v)
    B = w.name("B"); w.axiom(B, w.pi(x, cN, prop), lp=(u,))
    K = w.name("K"); w.defn(K, w.pi(x, cN, prop), w.lam(x, cN, w.app(w.const(B, [lu]), w.bvar(0))), lp=(u,), h="abbrev")
    G = w.name("G"); w.defn(G, w.pi(x, cN, cN), w.lam(x, cN, w.bvar(0)), h={"regular": 1})
    if good:
        lhs = w.app(w.const(K, [lu]), w.app(w.const(G), c1)); rhs = w.app(w.const(K, [lu]), c1)
    else:
        lhs = w.app(w.const(K, [lu]), c1); rhs = w.app(w.const(K, [lv]), c1)
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)), lp=(u, v))
    w.save(f"{out}/{'good' if good else 'bad'}_m17_probe_levels.ndjson")
# 2. the budget: g0 := n1 (bad) / n2 (good), g_{i+1} := g_i, 3000 regular
# definitions; K x := Q x (abbrev). t : K g3000 -> K n2. The probe runs out
# of budget unfolding the chain; out of budget must mean "not equal" (then
# K unfolds, Q g3000 =?= Q n2 decides).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); h = w.name("h")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, cN, prop))
    K = w.name("K"); w.defn(K, w.pi(x, cN, prop), w.lam(x, cN, w.app(w.const(Q), w.bvar(0))), h="abbrev")
    prev = c2 if good else c1
    for i in range(3000):
        g = w.name(f"g{i}"); w.defn(g, cN, prev, h={"regular": i + 1}); prev = w.const(g)
    lhs = w.app(w.const(K), prev); rhs = w.app(w.const(K), c2)
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m17_probe_budget.ndjson")
# 3. two abbreviations with the same arguments: K1 x := Q x, K2 x := R x;
# t : K1 n1 -> K2 n1 (bad: different heads are never probed); K2 := Q x
# too (good: both unfold to Q n1).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); h = w.name("h")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, cN, prop)); R = w.name("R"); w.axiom(R, w.pi(x, cN, prop))
    K1 = w.name("K1"); w.defn(K1, w.pi(x, cN, prop), w.lam(x, cN, w.app(w.const(Q), w.bvar(0))), h="abbrev")
    K2 = w.name("K2"); w.defn(K2, w.pi(x, cN, prop), w.lam(x, cN, w.app(w.const(Q if good else R), w.bvar(0))), h="abbrev")
    lhs = w.app(w.const(K1), c1); rhs = w.app(w.const(K2), c1)
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m17_probe_heads.ndjson")
# 4. unused arguments: K x y := Q x (abbrev, y never read); t : K n1 n2 ->
# K n1 n1 (good: the probe may skip y); K x y := Q y (bad: y is read).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); y = w.name("y"); h = w.name("h")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, cN, prop))
    K = w.name("K"); w.defn(K, w.pi(x, cN, w.pi(y, cN, prop)), w.lam(x, cN, w.lam(y, cN, w.app(w.const(Q), w.bvar(1 if good else 0)))), h="abbrev")
    lhs = w.app(w.app(w.const(K), c1), c2); rhs = w.app(w.app(w.const(K), c1), c1)
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m17_probe_unused.ndjson")
# 5. the old gap (milestone 16, mutant I2): an open term checked under one
# declaration's universe parameters is reused by a declaration that does
# not declare them. C.{v} : N -> Sort v -> Prop; X.{u} : (x : N) -> C.{u+1}
# x (Sort u), then Y : the same type without u (bad: u undeclared) / Y.{u}
# (good). The application under x reads x, so its inference is kept by its
# used entries (infer_u), not as a closed term.
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); a = w.name("a")
    v = w.name("v"); lv = lvl_param(w, v)
    C = w.name("C"); w.axiom(C, w.pi(x, cN, w.pi(a, w.sort(lv), prop)), lp=(v,))
    u = w.name("u"); lu = lvl_param(w, u); su = w.succ(lu)
    T = w.pi(x, cN, w.app(w.app(w.const(C, [su]), w.bvar(0)), w.sort(lu)))
    w.axiom(w.name("X"), T, lp=(u,))
    w.axiom(w.name("Y"), T, lp=(u,) if good else ())
    w.save(f"{out}/{'good' if good else 'bad'}_m17_open_universe.ndjson")
print("milestone 17 vectors written")
# 6. same_term's memo (milestone 17, direct-mapped) must keep the
# environments: X_k := fun z => G #k, idq : (F : N -> N) -> Q F -> Q F.
# t : (a c : N) -> Q X_2 -> (u : N) -> Q X_4 := fun a c h u => idq X_4 h
# (X_2 at depth 2 and X_4 at depth 4 both name a: the walk at the entry of
# Q X_2 =?= Q X_4 finds the closures equal). Then t2 : (a c w : N) -> Q X_2
# -> Q X_4 := fun a c w h => idq X_4 h (X_2 at depth 3 names c, X_4 at
# depth 4 names a: the same term pair under other environments, bad) /
# X_3 for X_4 (good).
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); z = w.name("z"); h = w.name("h"); a = w.name("a"); c = w.name("c"); u = w.name("u"); ww = w.name("w"); F = w.name("F")
    G = w.name("G"); w.axiom(G, w.pi(x, cN, cN))
    NN = w.pi(z, cN, cN)
    Q = w.name("Q"); w.axiom(Q, w.pi(x, NN, prop)); cQ = w.const(Q)
    idq = w.name("idq"); w.axiom(idq, w.pi(F, NN, w.pi(h, w.app(cQ, w.bvar(0)), w.app(cQ, w.bvar(1)))))
    def X(k): return w.lam(z, cN, w.app(w.const(G), w.bvar(k)))
    def q(k): return w.app(cQ, X(k))
    def use(k): return w.app(w.app(w.const(idq), X(k)), w.bvar(k - 3 if k > 3 else 0))
    ty = w.pi(a, cN, w.pi(c, cN, w.pi(h, q(2), w.pi(u, cN, q(4)))))
    val = w.lam(a, cN, w.lam(c, cN, w.lam(h, q(2), w.lam(u, cN, w.app(w.app(w.const(idq), X(4)), w.bvar(1))))))
    w.thm(w.name("t"), ty, val)
    k = 3 if good else 4
    ty2 = w.pi(a, cN, w.pi(c, cN, w.pi(ww, cN, w.pi(h, q(2), q(k)))))
    val2 = w.lam(a, cN, w.lam(c, cN, w.lam(ww, cN, w.lam(h, q(2), w.app(w.app(w.const(idq), X(k)), w.bvar(0))))))
    w.thm(w.name("t2"), ty2, val2)
    w.save(f"{out}/{'good' if good else 'bad'}_m17_term_memo_envs.ndjson")
print("milestone 17 term memo vectors written")
# milestone 18: same_term's table across a session reset (mutant T1:
# generation not compared). A := fun a c h u => idq X_4 h, h : Q X_2,
# result Q X_4 (X_2 and X_4 both name a: the walk stores the pair as
# equal). B is A over its own copies of G, Q, idq (no term shared with A,
# so B's terms are decoded in the same places as A's), each of A and B
# first in its session when sessions are cut every 2 declarations (filler
# axioms), so B's pair gets A's ids. Bad: B's X_4 is fun z => G' #3
# (names c: Q X_2 is not Q X_3); good: as A. A stale entry (same ids, an
# older generation) would make B's pair equal.
for good in (True, False):
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); z = w.name("z"); h = w.name("h"); a = w.name("a"); c = w.name("c"); u = w.name("u"); F = w.name("F")
    NN = w.pi(z, cN, cN)
    def thm(name, sfx, k):
        G = w.name("G" + sfx); w.axiom(G, w.pi(x, cN, cN))
        Q = w.name("Q" + sfx); w.axiom(Q, w.pi(x, NN, prop)); cQ = w.const(Q)
        idq = w.name("idq" + sfx); w.axiom(idq, w.pi(F, NN, w.pi(h, w.app(cQ, w.bvar(0)), w.app(cQ, w.bvar(1)))))
        w.axiom(w.name("pad" + sfx), prop)
        def X(k): return w.lam(z, cN, w.app(w.const(G), w.bvar(k)))
        def q(k): return w.app(cQ, X(k))
        ty = w.pi(a, cN, w.pi(c, cN, w.pi(h, q(2), w.pi(u, cN, q(k)))))
        val = w.lam(a, cN, w.lam(c, cN, w.lam(h, q(2), w.lam(u, cN, w.app(w.app(w.const(idq), X(k)), w.bvar(1))))))
        w.thm(w.name(name), ty, val)
    thm("A", "", 4)
    thm("B", "'", 4 if good else 3)
    w.axiom(w.name("pad2"), prop)
    w.save(f"{out}/{'good' if good else 'bad'}_m18_term_memo_gen.ndjson")
print("milestone 18 term memo vectors written")

# ---- milestone 19: structure eta leaves proof fields out (Pestka's
# EtaProofFieldsSkipped). BP (hp : P) : Type, mk (x : N) (h : P): positions
# 0 (the parameter hp) and 2 (the field h) are proofs, 1 (the field x) is
# data. For s : BP p, s = BP.mk p s.1 p' is structure eta with a proof field
# (good: p and s.2 are proofs of P); s = BP.mk p n1 p is not (bad: the data
# field differs; a skip of every field, or by the field's own index i
# instead of the position nparams + i, would accept it).
def bp_struct(w):
    prop = w.sort(0); one = w.succ(0); ty = w.sort(one)
    u = w.name("u"); lu = lvl_param(w, u)
    N = w.name("N"); w.axiom(N, ty); cN = w.const(N)
    n1 = w.name("n1"); w.axiom(n1, cN)
    P = w.name("P"); w.axiom(P, prop); cP = w.const(P)
    p = w.name("p"); w.axiom(p, cP); p2 = w.name("p2"); w.axiom(p2, cP)
    BP = w.name("BP"); mk = w.name("mk", pre=BP); rec = w.name("rec", pre=BP)
    hp = w.name("hp"); x = w.name("x"); h = w.name("h"); mo = w.name("motive"); t = w.name("t"); mkb = w.name("mk")
    cBP = w.const(BP); cMk = w.const(mk)
    bp_ty = w.pi(hp, cP, ty)
    mk_ty = w.pi(hp, cP, w.pi(x, cN, w.pi(h, cP, w.app(cBP, w.bvar(2)))), "implicit")
    mot_ty = w.pi(t, w.app(cBP, w.bvar(0)), w.sort(lu))
    minor_ty = w.pi(x, cN, w.pi(h, cP, w.app(w.bvar(2), w.app(w.app(w.app(cMk, w.bvar(3)), w.bvar(1)), w.bvar(0)))))
    rec_ty = w.pi(hp, cP, w.pi(mo, mot_ty, w.pi(mkb, minor_ty, w.pi(t, w.app(cBP, w.bvar(2)), w.app(w.bvar(2), w.bvar(0)))), "implicit"), "implicit")
    rhs = w.lam(hp, cP, w.lam(mo, mot_ty, w.lam(mkb, minor_ty, w.lam(x, cN, w.lam(h, cP, w.app(w.app(w.bvar(2), w.bvar(1)), w.bvar(0)))))))
    w.lines.append(json.dumps({"inductive": {
        "ctors": [{"cidx": 0, "induct": BP, "isUnsafe": False, "levelParams": [], "name": mk, "numFields": 2, "numParams": 1, "type": mk_ty}],
        "recs": [{"all": [BP], "isUnsafe": False, "k": False, "levelParams": [u], "name": rec, "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 1,
                  "rules": [{"ctor": mk, "nfields": 2, "rhs": rhs}], "type": rec_ty}],
        "types": [{"all": [BP], "ctors": [mk], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": BP,
                   "numIndices": 0, "numNested": 0, "numParams": 1, "type": bp_ty}]}}))
    return dict(cN=cN, n1=w.const(n1), cP=cP, p=w.const(p), p2=w.const(p2), BP=BP, cBP=cBP, cMk=cMk)
for good in (True, False):
    w = W(); d = bp_struct(w); prop = w.sort(0)
    sbp = w.app(d["cBP"], d["p"])
    q = w.name("Q"); s = w.name("s"); w.axiom(q, w.pi(s, sbp, prop)); cq = w.const(q)
    # under s (bvar 0 outside the hypothesis binder)
    x = w.ex(proj={"idx": 0, "struct": w.bvar(0), "typeName": d["BP"]}) if good else d["n1"]
    other = w.app(w.app(w.app(d["cMk"], d["p"]), x), d["p2"])
    hyp = w.name("hy")
    lhs = w.app(cq, w.bvar(0))
    # Π s, Q s → Q (mk p x p2); the conclusion sits under hy: shift s to bvar 1
    x1 = w.ex(proj={"idx": 0, "struct": w.bvar(1), "typeName": d["BP"]}) if good else d["n1"]
    other1 = w.app(w.app(w.app(d["cMk"], d["p"]), x1), d["p2"])
    ty = w.pi(s, sbp, w.pi(hyp, lhs, w.app(cq, other1)))
    val = w.lam(s, sbp, w.lam(hyp, lhs, w.bvar(0)))
    w.thm(w.name("etaProof"), ty, val)
    w.save(f"{out}/{'good' if good else 'bad'}_m19_eta_proof_field.ndjson")
print("milestone 19 eta vectors written")
# ---- milestone 19: sparse casesOn read directly (Pestka's RecHeadedDirect).
# Base: Arena tutorial 070 (N with zero and succ, N.rec.{u}), without nRec.
# A definition named N._sparseCasesOn_k whose value is lambdas over N.rec:
# pred t := N.rec (fun _ => N) zero (fun n ih => n) t (the field taken);
# idr t := N.rec (fun _ => N) zero (fun n ih => succ ih) t (a minor premise
# that reads its hypothesis: unfolded as before); after t e := N.rec (fun _
# => N -> N) (fun x => x) (fun n ih x => n) t e (an argument after the
# major premise).
n_base = os.path.join(os.path.dirname(__file__), "..", "tests", "adv-base", "n.base")
def n_sparse(k, motive_arrow, mz_f, ms_f, extra):
    w = from_base(n_base)
    cN = w.const(1); z = w.const(2); s = w.const(3)
    one = w.succ(0)
    t = w.name("t"); n = w.name("n"); ih = w.name("ih"); x = w.name("x"); e = w.name("e")
    us = w.name("_sparseCasesOn_%d" % k, pre=1)
    rt = w.pi(x, cN, cN) if motive_arrow else cN
    mot = w.lam(t, cN, rt)
    rec = w.const(9, [one])
    # under t (and e): bvar 0 is t, or e with t at 1
    tv = 1 if extra else 0
    body = w.app(w.app(w.app(w.app(rec, mot), mz_f(w, z, s, cN)), ms_f(w, z, s, cN)), w.bvar(tv))
    if extra:
        body = w.app(body, w.bvar(0))
        val = w.lam(t, cN, w.lam(e, cN, body)); ty = w.pi(t, cN, w.pi(e, cN, cN))
    else:
        val = w.lam(t, cN, body); ty = w.pi(t, cN, cN)
    w.defn(us, ty, val, h="abbrev")
    q = w.name("Q"); w.axiom(q, w.pi(x, cN, w.sort(0)))
    return w, w.const(us), w.const(q), z, s, cN
def sparse_thm(w, cq, lhs_arg, rhs_arg, name, good):
    h = w.name("h"); lhs = w.app(cq, lhs_arg)
    w.thm(w.name("t_" + name), w.pi(h, lhs, w.app(cq, rhs_arg)), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m19_sparse_{name}.ndjson")
lam = lambda w, nm, ty, b: w.lam(w.name(nm), ty, b)
# pred: zero minor `zero`, succ minor fun n ih => n
for good in (True, False):
    w, f, cq, z, s, cN = n_sparse(1, False, lambda w, z, s, cN: z,
        lambda w, z, s, cN: lam(w, "n", cN, lam(w, "ih", cN, w.bvar(1))), False)
    one_ = w.app(s, z)
    sparse_thm(w, cq, w.app(f, w.app(s, one_)), one_ if good else w.app(s, one_), "field", good)
# idr: succ minor fun n ih => succ ih reads the hypothesis
for good in (True, False):
    w, f, cq, z, s, cN = n_sparse(2, False, lambda w, z, s, cN: z,
        lambda w, z, s, cN: lam(w, "n", cN, lam(w, "ih", cN, w.app(s, w.bvar(0)))), False)
    one_ = w.app(s, z); two = w.app(s, one_)
    sparse_thm(w, cq, w.app(f, one_ if not good else two), two, "hypothesis", good)
# after: an argument after the major premise
for good in (True, False):
    w, f, cq, z, s, cN = n_sparse(3, True, lambda w, z, s, cN: lam(w, "x", cN, w.bvar(0)),
        lambda w, z, s, cN: lam(w, "n", cN, lam(w, "ih", w.pi(w.name("x"), cN, cN), lam(w, "x", cN, w.bvar(2)))), True)
    one_ = w.app(s, z)
    sparse_thm(w, cq, w.app(w.app(f, w.app(s, one_)), z), one_ if good else z, "after", good)
print("milestone 19 sparse casesOn vectors written")
# two fields, in order: TwoBool._sparseCasesOn_1 t := TwoBool.rec (fun _ =>
# Bool) (fun b1 b2 => b2) t (base: Arena tutorial 064)
for good in (True, False):
    w = from_base(base_path)
    cB = w.const(1); cTB = w.const(10); one = w.succ(0)
    t = w.name("t"); b1 = w.name("b1"); b2 = w.name("b2"); x = w.name("x")
    us = w.name("_sparseCasesOn_1", pre=10)
    body = w.app(w.app(w.app(w.const(14, [one]), w.lam(t, cTB, cB)), w.lam(b1, cB, w.lam(b2, cB, w.bvar(0)))), w.bvar(0))
    w.defn(us, w.pi(t, cTB, cB), w.lam(t, cTB, body), h="abbrev")
    q = w.name("Q"); w.axiom(q, w.pi(x, cB, w.sort(0))); cq = w.const(q)
    mk = w.app(w.app(w.const(11), w.const(3)), w.const(2))
    sparse_thm(w, cq, w.app(w.const(us), mk), w.const(2 if good else 3), "two_fields", good)
# the minor premise of the constructor met: Bool._sparseCasesOn_1 t :=
# Bool.rec (fun _ => Bool) true false t (not)
for good in (True, False):
    w = from_base(base_path)
    cB = w.const(1); one = w.succ(0); t = w.name("t"); x = w.name("x")
    us = w.name("_sparseCasesOn_1", pre=1)
    body = w.app(w.app(w.app(w.app(w.const(4, [one]), w.lam(t, cB, cB)), w.const(3)), w.const(2)), w.bvar(0))
    w.defn(us, w.pi(t, cB, cB), w.lam(t, cB, body), h="abbrev")
    q = w.name("Q"); w.axiom(q, w.pi(x, cB, w.sort(0))); cq = w.const(q)
    sparse_thm(w, cq, w.app(w.const(us), w.const(3)), w.const(2 if good else 3), "minor", good)

# ---- milestone 19: const_ll's direct-mapped table is stamped with the level
# epoch. T.{u} : Prop, D.{u} : Prop := T.{u}; a : D.{0} -> T.{0} (good), then
# b : D.{1} -> T.{0} (bad: D.{1} is T.{1}). With SK_LVL_FLUSH=1 the level
# tables are flushed between a and b, so b's substitution u := 1 gets a's id
# (u := 0) again: an entry read across the flush would make D.{1} T.{0}.
for good in (True, False):
    w = W(); prop = w.sort(0)
    u = w.name("u"); lu = lvl_param(w, u); one = w.succ(0)
    T = w.name("T"); w.axiom(T, prop, lp=(u,))
    D = w.name("D"); w.defn(D, prop, w.const(T, [lu]), lp=(u,), h={"regular": 1})
    h = w.name("h")
    da = w.const(D, [0]); ta = w.const(T, [0])
    w.thm(w.name("a"), w.pi(h, da, ta), w.lam(h, da, w.bvar(0)))
    db = w.const(D, [one if not good else 0]); tb = w.const(T, [0])
    w.thm(w.name("b"), w.pi(h, db, tb), w.lam(h, db, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m19_cll_epoch.ndjson")
print("milestone 19 level-list table vectors written")

# ---- milestone 21: namespace order checks A.P (0), A.w (2) then B.x (1),
# B.y (3) on one worker (A.w uses only A.P); written for a session rule that
# went on at an earlier declaration (measured, rejected), kept as order vectors.
# Good: B.x := A.P, and A.w's shared value term (h : A.P) -> A.P is met
# again in B.y. Bad: B.x := A.w (declared after B.x), with A.w's facts in
# the session; B.x must still be rejected.
for good in (True, False):
    w = W(); prop = w.sort(0)
    P = w.name("A.P"); w.axiom(P, prop); cP = w.const(P)
    h = w.name("h")
    imp = w.pi(h, cP, cP)
    Aw = w.name("A.w")
    w.defn(w.name("B.x"), prop, imp if good else w.const(Aw), h={"regular": 1})
    w.defn(Aw, prop, imp, h={"regular": 1})
    Bx = w.names["B.x"]
    w.thm(w.name("B.y"), w.pi(h, w.const(Bx), w.const(Aw)), w.lam(h, w.const(Bx), w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m21_back_join.ndjson")
print("milestone 21 session order vectors written")

# ---- milestone 29: open facts. A.f : A.P -> A.P := fun x => A.k x makes
# `A.k x` (its body) and `A.P` (its type's codomain) open facts; a
# declaration type whose Pi telescope has the same domains finds them.
# good: B.L : (x : A.P) -> A.Pp (A.k x) after A.f (the fact is used).
# bad_m29_open_domains: B.L : (x : A.Q) -> A.Pp (A.k x) (other domain).
# bad_m29_open_later: B.L before A.k and A.f in the file, checked after them
#   in namespace order (a fact of a later declaration).
# bad_m29_open_levels: A.k.{u}, A.f.{u}; B.L without u uses A.k.{u} x.
# bad_m29_open_unsafe: A.k an unsafe axiom, A.f an unsafe definition.
# (later, unsafe: the body is A.g (A.k x), so that inference without
# checking never meets A.k)
def open_vec(kind):
    w = W(); prop = w.sort(0)
    P = w.name("A.P"); w.axiom(P, prop); cP = w.const(P)
    Q = w.name("A.Q"); w.axiom(Q, prop); cQ = w.const(Q)
    x = w.name("x")
    Pp = w.name("A.Pp"); w.axiom(Pp, w.pi(x, cP, prop)); cPp = w.const(Pp)
    u = w.name("u")
    lu = lvl_param(w, u) if kind == "levels" else None
    lp = (u,) if kind == "levels" else ()
    us = [lu] if kind == "levels" else []
    k = w.name("A.k"); f = w.name("A.f"); L = w.name("B.L")
    g = w.name("A.g"); w.axiom(g, w.pi(x, cP, cP))
    # A.g (A.k x): inference without checking reads only A.g's type
    kx = w.app(w.const(k, us), w.bvar(0))
    if kind in ("later", "unsafe"):
        kx = w.app(w.const(g), kx)
    lty = w.pi(x, cQ if kind == "domains" else cP, w.app(cPp, kx))
    fty = w.pi(x, cP, cP)
    if kind == "later":
        w.axiom(L, lty)
    w.axiom(k, fty, lp=lp)
    if kind == "unsafe":
        w.lines[-1] = w.lines[-1].replace('"isUnsafe": false', '"isUnsafe": true')
    w.defn(f, fty, w.lam(x, cP, kx), lp=lp, h={"regular": 1}, safety="unsafe" if kind == "unsafe" else "safe")
    if kind != "later":
        w.axiom(L, lty)
    w.save(f"{out}/{'good' if kind == 'good' else 'bad'}_m29_open_{kind}.ndjson")
for kind in ("good", "domains", "later", "levels", "unsafe"):
    open_vec(kind)
print("milestone 29 open fact vectors written")

# ---- milestone 29: the value-term walk memo (same_vt) is keyed by the
# level substitution too. G f k x := W (f (k R)), E.{u} f x :=
# W (f (K.{u} R)), R = S^20 x (both arguments of W stay thunks: their head
# is a lambda). c1 : G I K.{0} a -> E.{0} I a walks K.{0} (a value)
# against the term K.{u} at u := 0 (equal); c2 : G I K.{0} a -> E.{1} I a
# meets the same pair at u := 1 (not equal). good: c2 at E.{0} again.
for good in (True, False):
    w = W(); prop = w.sort(0); ty = w.sort(w.succ(0))
    u = w.name("u"); lu = lvl_param(w, u); one = w.succ(0)
    A = w.name("A"); w.axiom(A, ty); cA = w.const(A)
    x = w.name("x"); k = w.name("k"); a = w.name("a"); h = w.name("h"); f = w.name("f"); z = w.name("z")
    Wn = w.name("W"); w.axiom(Wn, w.pi(x, ty, ty)); cW = w.const(Wn)
    K = w.name("K"); w.axiom(K, w.pi(x, cA, ty), lp=(u,))
    Sn = w.name("S"); w.axiom(Sn, w.pi(x, cA, cA)); cS = w.const(Sn)
    R = w.bvar(0)
    for _ in range(20):
        R = w.app(cS, R)
    aty = w.pi(x, cA, ty); fty = w.pi(z, ty, ty)
    E = w.name("E")
    w.defn(E, w.pi(f, fty, aty), w.lam(f, fty, w.lam(x, cA, w.app(cW, w.app(w.bvar(1), w.app(w.const(K, [lu]), R))))), lp=(u,), h={"regular": 1})
    G = w.name("G")
    w.defn(G, w.pi(f, fty, w.pi(k, aty, aty)), w.lam(f, fty, w.lam(k, aty, w.lam(x, cA, w.app(cW, w.app(w.bvar(2), w.app(w.bvar(1), R)))))), h={"regular": 2})
    I = w.lam(z, ty, w.bvar(0))
    def stmt(l):
        gk = w.app(w.app(w.app(w.const(G), I), w.const(K, [0])), w.bvar(0))
        el = w.app(w.app(w.const(E, [l]), I), w.bvar(1))
        return w.pi(a, cA, w.pi(h, gk, el)), w.lam(a, cA, w.lam(h, gk, w.bvar(0)))
    t1, v1 = stmt(0); w.defn(w.name("c1"), t1, v1, h={"regular": 3})
    t2, v2 = stmt(0 if good else one); w.defn(w.name("c2"), t2, v2, h={"regular": 3})
    w.save(f"{out}/{'good' if good else 'bad'}_m29_vt_levels.ndjson")
print("milestone 29 value-term memo vectors written")

# ---- milestone 29: a field's universe against the inductive type's (Lean's
# is_geq_core: offsets compare when the bases are equal or the field's base
# is zero). S.{u} : Sort R, S.mk (x : X) with X : Sort F.
# good_m29_level_zero_base: R = u+2, X = N : Type (F = 1): u+2 >= 1 (FLT's
#   DoubleComplex.Bounded: a field N : Nat in a structure in Sort (u+2)).
# bad_m29_level_const_base: R = 2, X = Type u (F = u+2): 2 >= u+2 is false
#   (a constant base against a parameter: Sort 2 would hold Type u).
def level_struct(kind):
    w = W(); one = w.succ(0); ty = w.sort(one)
    u = w.name("u"); lu = lvl_param(w, u)
    u1 = w.name("u_1"); lu1 = lvl_param(w, u1)
    N = w.name("N"); w.axiom(N, ty)
    if kind == "zero_base":
        R = w.succ(w.succ(lu)); X = w.const(N)
    else:
        R = w.succ(one); X = w.sort(w.succ(lu))
    S = w.name("S"); mk = w.name("mk", pre=S); rec = w.name("rec", pre=S)
    x = w.name("x"); mo = w.name("motive"); t = w.name("t"); mkb = w.name("mk")
    cS = w.const(S, [lu]); cMk = w.const(mk, [lu])
    mk_ty = w.pi(x, X, cS)
    mot_ty = w.pi(t, cS, w.sort(lu1))
    minor_ty = w.pi(x, X, w.app(w.bvar(1), w.app(cMk, w.bvar(0))))
    rec_ty = w.pi(mo, mot_ty, w.pi(mkb, minor_ty, w.pi(t, cS, w.app(w.bvar(2), w.bvar(0)))), "implicit")
    rhs = w.lam(mo, mot_ty, w.lam(mkb, minor_ty, w.lam(x, X, w.app(w.bvar(1), w.bvar(0)))))
    w.lines.append(json.dumps({"inductive": {
        "ctors": [{"cidx": 0, "induct": S, "isUnsafe": False, "levelParams": [u], "name": mk, "numFields": 1, "numParams": 0, "type": mk_ty}],
        "recs": [{"all": [S], "isUnsafe": False, "k": False, "levelParams": [u1, u], "name": rec, "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0,
                  "rules": [{"ctor": mk, "nfields": 1, "rhs": rhs}], "type": rec_ty}],
        "types": [{"all": [S], "ctors": [mk], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [u], "name": S,
                   "numIndices": 0, "numNested": 0, "numParams": 0, "type": w.sort(R)}]}}))
    w.save(f"{out}/{'good' if kind == 'zero_base' else 'bad'}_m29_level_{kind}.ndjson")
for kind in ("zero_base", "const_base"):
    level_struct(kind)
print("milestone 29 field universe vectors written")

# ---- milestone 29: used-entry keys past 63 entries. ax1 : (p : P) -> D^64
# -> C (g p) and ax2 : (q : Q) -> D^64 -> C (g q) share the term C (g #64)
# under 65 binders; its inference is keyed by the entry it reads, the
# variable of P or of Q. bad: ax2 (g : P -> R applied to q : Q).
for good in (True, False):
    w = W(); prop = w.sort(0); ty = w.sort(w.succ(0))
    P = w.name("P"); w.axiom(P, ty); cP = w.const(P)
    Q = w.name("Q"); w.axiom(Q, ty); cQ = w.const(Q)
    Dn = w.name("D"); w.axiom(Dn, ty); cD = w.const(Dn)
    Rn = w.name("R"); w.axiom(Rn, ty); cR = w.const(Rn)
    x = w.name("x"); d = w.name("d"); p = w.name("p")
    g = w.name("g"); w.axiom(g, w.pi(x, cP, cR)); cg = w.const(g)
    C = w.name("C"); w.axiom(C, w.pi(x, cR, ty)); cC = w.const(C)
    body = w.app(cC, w.app(cg, w.bvar(64)))
    def tele(dom):
        t = body
        for _ in range(64):
            t = w.pi(d, cD, t)
        return w.pi(p, dom, t)
    w.axiom(w.name("ax1"), tele(cP))
    w.axiom(w.name("ax2"), tele(cP if good else cQ))
    w.save(f"{out}/{'good' if good else 'bad'}_m29_wide_key.ndjson")
print("milestone 29 wide key vectors written")

# ---- milestone 31: a projection application is reduced before its
# arguments are compared (Lean's order). S.{} : Type, S.mk (f : N -> N).
# F x := n1, G x := x, C1 := mk F, C2 := mk G (regular). t : Q (C1.1 n1)
# -> Q (C2.1 n1)
# (good: the functions differ, the reduced sides are n1 both);
# n2 in place of n1 (bad: F n2 = n1, G n2 = n2). proj_stuck: s : S a
# variable, s.1 (I n1) against s.1 n1 with I the identity (good: neither
# side reduces, the arguments are compared) / s.1 n2 (bad).
def fn_struct(w, cN):
    one = w.succ(0); ty = w.sort(one)
    u1 = w.name("u"); lu1 = lvl_param(w, u1)
    S = w.name("S"); mk = w.name("mk", pre=S); rec = w.name("rec", pre=S)
    x = w.name("x"); f = w.name("f"); mo = w.name("motive"); t = w.name("t"); mkb = w.name("mk")
    cS = w.const(S); cMk = w.const(mk)
    X = w.pi(x, cN, cN)
    mk_ty = w.pi(f, X, cS)
    mot_ty = w.pi(t, cS, w.sort(lu1))
    minor_ty = w.pi(f, X, w.app(w.bvar(1), w.app(cMk, w.bvar(0))))
    rec_ty = w.pi(mo, mot_ty, w.pi(mkb, minor_ty, w.pi(t, cS, w.app(w.bvar(2), w.bvar(0)))), "implicit")
    rhs = w.lam(mo, mot_ty, w.lam(mkb, minor_ty, w.lam(f, X, w.app(w.bvar(1), w.bvar(0)))))
    w.lines.append(json.dumps({"inductive": {
        "ctors": [{"cidx": 0, "induct": S, "isUnsafe": False, "levelParams": [], "name": mk, "numFields": 1, "numParams": 0, "type": mk_ty}],
        "recs": [{"all": [S], "isUnsafe": False, "k": False, "levelParams": [u1], "name": rec, "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0,
                  "rules": [{"ctor": mk, "nfields": 1, "rhs": rhs}], "type": rec_ty}],
        "types": [{"all": [S], "ctors": [mk], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": S,
                   "numIndices": 0, "numNested": 0, "numParams": 0, "type": ty}]}}))
    return S, cS, cMk
for kind in ("ctor", "stuck"):
    for good in (True, False):
        w, prop, ff = base()
        one, cN, c1, c2 = nat_like(w)
        S, cS, cMk = fn_struct(w, cN)
        x = w.name("x"); h = w.name("h"); s = w.name("s")
        Q = w.name("Q"); w.axiom(Q, w.pi(x, cN, prop)); cQ = w.const(Q)
        F = w.name("F"); w.defn(F, w.pi(x, cN, cN), w.lam(x, cN, c1), h={"regular": 1})
        G = w.name("G"); w.defn(G, w.pi(x, cN, cN), w.lam(x, cN, w.bvar(0)), h={"regular": 1})
        I = w.name("I"); w.defn(I, w.pi(x, cN, cN), w.lam(x, cN, w.bvar(0)), h={"regular": 1})
        a = c1 if good else c2
        if kind == "ctor":
            # the structures are definitions (cheap projections do not unfold them)
            C1 = w.name("C1"); w.defn(C1, cS, w.app(cMk, w.const(F)), h={"regular": 2})
            C2 = w.name("C2"); w.defn(C2, cS, w.app(cMk, w.const(G)), h={"regular": 2})
            pa = w.ex(proj={"typeName": S, "idx": 0, "struct": w.const(C1)})
            pb = w.ex(proj={"typeName": S, "idx": 0, "struct": w.const(C2)})
            lhs = w.app(cQ, w.app(pa, a)); rhs = w.app(cQ, w.app(pb, a))
            w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
        else:
            # Π s, Q (s.1 (I n1)) -> Q (s.1 a); under h, s is bvar 1
            def sp(k, arg): return w.app(cQ, w.app(w.ex(proj={"typeName": S, "idx": 0, "struct": w.bvar(k)}), arg))
            lhs0 = sp(0, w.app(w.const(I), c1))
            ty_ = w.pi(s, cS, w.pi(h, lhs0, sp(1, a)))
            w.thm(w.name("t"), ty_, w.lam(s, cS, w.lam(h, lhs0, w.bvar(0))))
        w.save(f"{out}/{'good' if good else 'bad'}_m31_proj_app_{kind}.ndjson")
# ---- milestone 31: a pair a probe ran out of budget on stops later probes.
# K x := Q x and H a b := R a b (abbreviations), g0 := n2 (good) / n1 (bad),
# g_{i+1} := g_i, 3000 regular definitions. t : H (K g3000) (K g3000) ->
# H (K n2) (K n2). H's probe compares K g3000 with K n2 (K's arguments
# inside it) and runs out of budget: the pairs it was on are marked. H
# unfolds; R's arguments K g3000 =?= K n2 are compared outside any probe,
# K's own probe reaches g3000 =?= n2, marked: it stops (not equal), K
# unfolds and Q g3000 =?= Q n2 decides. A marked pair answering "equal"
# would accept the bad file.
for good in (True, False):
    w, prop, ff = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); y = w.name("y"); h = w.name("h")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, cN, prop))
    R = w.name("R"); w.axiom(R, w.pi(x, prop, w.pi(y, prop, prop)))
    K = w.name("K"); w.defn(K, w.pi(x, cN, prop), w.lam(x, cN, w.app(w.const(Q), w.bvar(0))), h="abbrev")
    H = w.name("H"); w.defn(H, w.pi(x, prop, w.pi(y, prop, prop)), w.lam(x, prop, w.lam(y, prop, w.app(w.app(w.const(R), w.bvar(1)), w.bvar(0)))), h="abbrev")
    prev = c2 if good else c1
    for i in range(3000):
        g = w.name(f"g{i}"); w.defn(g, cN, prev, h={"regular": i + 1}); prev = w.const(g)
    ka = w.app(w.const(K), prev); kb = w.app(w.const(K), c2)
    lhs = w.app(w.app(w.const(H), ka), ka); rhs = w.app(w.app(w.const(H), kb), kb)
    w.thm(w.name("t"), w.pi(h, lhs, rhs), w.lam(h, lhs, w.bvar(0)))
    w.save(f"{out}/{'good' if good else 'bad'}_m31_probe_dead.ndjson")
print("milestone 31 vectors written")
# ---- milestone 31: inference by name (proposal 2's inference site, on by
# default; in release-da from the first unfolding). F.{w} : N -> U.{w},
# K.{w} : U.{w} -> U.{w} -> Prop. def t.{u v} : Prop := K.{u} (F.{u} n1)
# (F.{u} n1) written twice (two term ids, one name: the second inference is
# a name hit; good) / the second F.{v} (bad: the names differ by the level;
# U.{v} is not U.{u}).
for good in (True, False):
    w, prop, ff = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); y = w.name("y")
    uu = w.name("u"); vv = w.name("v"); wn = w.name("w")
    lu = lvl_param(w, uu); lv = lvl_param(w, vv); lw = lvl_param(w, wn)
    U = w.name("U"); w.axiom(U, w.sort(one), lp=(wn,))
    F = w.name("F"); w.axiom(F, w.pi(x, cN, w.const(U, [lw])), lp=(wn,))
    Kn = w.name("K"); w.axiom(Kn, w.pi(x, w.const(U, [lw]), w.pi(y, w.const(U, [lw]), prop)), lp=(wn,))
    a1 = w.app(w.const(F, [lu]), c1)
    a2 = w.app(w.const(F, [lu if good else lv]), c1)
    w.defn(w.name("t"), prop, w.app(w.app(w.const(Kn, [lu]), a1), a2), lp=(uu, vv), h={"regular": 1})
    w.save(f"{out}/{'good' if good else 'bad'}_m31_infer_names.ndjson")
print("milestone 31 inference name vectors written")
# ---- milestone 31: a name hit of the inference site in release-da (names
# from the first unfolding, closed terms included). P.{w} : N -> Prop,
# A.{w} := U.{w} -> P.{w} n1 (written in place), G.{w} : N -> A.{w}, Kp : (p :
# Prop) -> p -> p -> Prop, U.{w} : Sort (w+1), Tri a b c with mkTri, q1 : Q n1. Imp_w := (k : A_w -> A_w -> Prop) -> k (G_w n1) (G_w n1)
# -> k (G_w n2) (G_w n2) (a variable head: the proofs are compared, not
# skipped). def t.{u v} : Tri Imp_u Imp_v (Q n1) := mkTri (fun k h => h) (fun k
# h => h) q1 (good): proof irrelevance (G_w n1 against G_w n2) infers the sort of A_w,
# its domain U.{w} (Sort (w+1)) at [u] and then at [v]; a name without the level
# substitution would call them one term (release-da's check of the hit
# fails). bad: the third component Q n2 (q1 : Q n1), checked after both.
for good in (True, False):
    w, prop, ff = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); y = w.name("y"); p = w.name("p"); q = w.name("q"); h = w.name("h"); a = w.name("a"); b = w.name("b")
    uu = w.name("u"); vv = w.name("v"); wn = w.name("w")
    lu = lvl_param(w, uu); lv = lvl_param(w, vv); lw = lvl_param(w, wn)
    P = w.name("P"); w.axiom(P, w.pi(x, cN, prop), lp=(wn,))
    U = w.name("U"); w.axiom(U, w.sort(w.succ(lw)), lp=(wn,))
    def A(l): return w.pi(y, w.const(U, [l]), w.app(w.const(P, [l]), c1))
    G = w.name("G"); w.axiom(G, w.pi(x, cN, A(lw)), lp=(wn,))
    Kp = w.name("Kp"); w.axiom(Kp, w.pi(p, prop, w.pi(x, w.bvar(0), w.pi(y, w.bvar(1), prop))))
    c = w.name("c"); z = w.name("z")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, cN, prop))
    q1 = w.name("q1"); w.axiom(q1, w.app(w.const(Q), c1))
    Pr = w.name("Tri"); w.axiom(Pr, w.pi(p, prop, w.pi(q, prop, w.pi(c, prop, prop))))
    mk = w.name("mkTri"); w.axiom(mk, w.pi(a, prop, w.pi(b, prop, w.pi(c, prop, w.pi(x, w.bvar(2), w.pi(y, w.bvar(2), w.pi(z, w.bvar(2), w.app(w.app(w.app(w.const(Pr), w.bvar(5)), w.bvar(4)), w.bvar(3))))), "implicit"), "implicit"), "implicit"))
    k = w.name("k")
    def kty(l): return w.pi(x, A(l), w.pi(y, A(l), prop))
    # under k (bvar d): k (G_l n) (G_l n)
    def K(l, n, d): g = w.app(w.const(G, [l]), n); return w.app(w.app(w.bvar(d), g), g)
    def imp(l, l2): return w.pi(k, kty(l), w.pi(h, K(l, c1, 0), K(l2, c2, 1)))
    iu = imp(lu, lu); iv = imp(lv, lv); qq = w.app(w.const(Q), c1 if good else c2)
    def idf(l): return w.lam(k, kty(l), w.lam(h, K(l, c1, 0), w.bvar(0)))
    idu = idf(lu); idv = idf(lv)
    val = w.app(w.app(w.app(w.app(w.app(w.app(w.const(mk), iu), iv), qq), idu), idv), w.const(q1))
    w.defn(w.name("t"), w.app(w.app(w.app(w.const(Pr), iu), iv), qq), val, lp=(uu, vv), h={"regular": 1})
    w.save(f"{out}/{'good' if good else 'bad'}_m31_infer_name_levels.ndjson")
print("milestone 31 inference name level vectors written")
# ---- milestone 34: a lambda's type at an argument from the type its body
# got under the lambda's own variable, when that type does not mention the
# variable (bind_body, lam_type_at). Q : N -> Prop, q : (x : N) -> Q x,
# I : (p : Prop) -> p -> p := fun p h => h, G : N -> N -> N.
# - good_m34_lam_type_ladder: def t : N := (fun x => (fun y => G x y) n1) n2
#   (the body types are N: from the cache);
# - good_m34_lam_type_dep: def t : Q n1 := (fun x => q x) n1 (the body's
#   type Q x mentions x: inferred again at n1);
# - bad_m34_lam_type_escape: def L : (x : N) -> Q x := T, T = fun x => q x
#   (checking T gives its variable y and the body's type Q y), then
#   theorem t : (m : N) -> Q m := fun m => I (Q m) (T n1): m opens the same
#   variable y (out of scope again); T n1 has type Q n1, not Q m. Taking the
#   cached Q y without the mention test accepts it.
def m34_base():
    w, prop, f = base()
    one, cN, c1, c2 = nat_like(w)
    x = w.name("x"); y = w.name("y"); p = w.name("p"); h = w.name("h"); m = w.name("m")
    Q = w.name("Q"); w.axiom(Q, w.pi(x, cN, prop))
    q = w.name("q"); w.axiom(q, w.pi(x, cN, w.app(w.const(Q), w.bvar(0))))
    I = w.name("I"); w.defn(I, w.pi(p, prop, w.pi(h, w.bvar(0), w.bvar(1))), w.lam(p, prop, w.lam(h, w.bvar(0), w.bvar(0))), h={"regular": 1})
    G = w.name("G"); w.axiom(G, w.pi(x, cN, w.pi(y, cN, cN)))
    return w, prop, cN, c1, c2, Q, q, I, G, x, y, m
w, prop, cN, c1, c2, Q, q, I, G, x, y, m = m34_base()
inner = w.app(w.lam(y, cN, w.app(w.app(w.const(G), w.bvar(1)), w.bvar(0))), c1)
w.defn(w.name("t"), cN, w.app(w.lam(x, cN, inner), c2), h={"regular": 1})
w.save(f"{out}/good_m34_lam_type_ladder.ndjson")
w, prop, cN, c1, c2, Q, q, I, G, x, y, m = m34_base()
w.defn(w.name("t"), w.app(w.const(Q), c1), w.app(w.lam(x, cN, w.app(w.const(q), w.bvar(0))), c1), h={"regular": 1})
w.save(f"{out}/good_m34_lam_type_dep.ndjson")
w, prop, cN, c1, c2, Q, q, I, G, x, y, m = m34_base()
T = w.lam(x, cN, w.app(w.const(q), w.bvar(0)))
w.defn(w.name("L"), w.pi(x, cN, w.app(w.const(Q), w.bvar(0))), T, h={"regular": 1})
body = w.app(w.app(w.const(I), w.app(w.const(Q), w.bvar(0))), w.app(T, c1))
w.thm(w.name("t"), w.pi(m, cN, w.app(w.const(Q), w.bvar(0))), w.lam(m, cN, body))
w.save(f"{out}/bad_m34_lam_type_escape.ndjson")
print("milestone 34 lambda type vectors written")

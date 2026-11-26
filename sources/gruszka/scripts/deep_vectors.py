# Milestone 42: deep vectors (tests/deep.sh). Writes to OUTDIR:
#   lets_bad.ndjson   D y := let x1 := g y; ...; xN := g x(N-1); xN (N = 300000 lets)
#                     t : forall y, P (D y) -> P (g y)                 (rejected)
#   acc_bad.ndjson    go t a := N.rec (fun _ => A -> A) (fun a => a) (fun n ih a => ih (g a)) t a,
#                     big := dbl^20 (succ zero): a lazy accumulator 2^20 steps deep
#                     t : forall y, P (go big y) -> P (g y)            (rejected)
#   acc_good.ndjson   t : forall y, P (go big y) -> P (go2 big y)      (accepted; go2 a copy of go)
#   list_good.ndjson  chars : L := cons z (cons z (... nil)), N = 1000000 conses (accepted;
#                     milestone 45: CFSG's RG.chars, a 791 K-element List Char literal)
#   list_bad.ndjson   the same with the innermost element of the wrong type (rejected)
# usage: python3 scripts/deep_vectors.py OUTDIR
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "adversarial.py")).read()
exec(src.split("out = os.path.join")[0])  # W, META
exec("def from_base" + src.split("def from_base")[1].split("base_path =")[0])
outd = sys.argv[1]
os.makedirs(outd, exist_ok=True)

def lets(n, path):
    w = W(); one = w.succ(0); ty = w.sort(one); prop = w.sort(0)
    A = w.name("A"); w.axiom(A, ty); cA = w.const(A)
    x = w.name("x"); y = w.name("y")
    g = w.name("g"); w.axiom(g, w.pi(x, cA, cA)); cg = w.const(g)
    P = w.name("P"); w.axiom(P, w.pi(x, cA, prop)); cP = w.const(P)
    body = w.bvar(0); gb = w.app(cg, w.bvar(0))
    for _ in range(n):
        body = w.ex(letE={"name": x, "type": cA, "value": gb, "body": body, "nondep": False})
    D = w.name("D"); w.defn(D, w.pi(y, cA, cA), w.lam(y, cA, body), h={"regular": 1}); cD = w.const(D)
    h = w.name("h")
    lhs = w.app(cP, w.app(cD, w.bvar(0))); rhs = w.app(cP, w.app(cg, w.bvar(1)))
    w.thm(w.name("t"), w.pi(y, cA, w.pi(h, lhs, rhs)), w.lam(y, cA, w.lam(h, lhs, w.bvar(0))))
    w.save(path)

def acc(m, kind, path):
    w = from_base(os.path.join(here, "..", "tests", "adv-base", "n.base"))
    cN = w.const(1); z = w.const(2); s = w.const(3); one = w.succ(0)
    ty = w.sort(one); prop = w.sort(0)
    nm = w.name
    A = nm("A"); w.axiom(A, ty); cA = w.const(A)
    x = nm("x"); y = nm("y"); a = nm("a"); n = nm("n"); ih = nm("ih"); t = nm("t")
    g = nm("g"); w.axiom(g, w.pi(x, cA, cA)); cg = w.const(g)
    P = nm("P"); w.axiom(P, w.pi(x, cA, prop)); cP = w.const(P)
    rec = w.const(9, [one]); AA = w.pi(x, cA, cA)
    def mkgo(name):
        mot = w.lam(t, cN, AA); mz = w.lam(a, cA, w.bvar(0))
        ms = w.lam(n, cN, w.lam(ih, AA, w.lam(a, cA, w.app(w.bvar(1), w.app(cg, w.bvar(0))))))
        body = w.app(w.app(w.app(w.app(rec, mot), mz), ms), w.bvar(0))
        G = nm(name); w.defn(G, w.pi(t, cN, AA), w.lam(t, cN, body), h={"regular": 1}); return w.const(G)
    cgo = mkgo("go")
    mot = w.lam(t, cN, cN); ms = w.lam(n, cN, w.lam(ih, cN, w.app(s, w.app(s, w.bvar(0)))))
    D = nm("dbl"); w.defn(D, w.pi(t, cN, cN), w.lam(t, cN, w.app(w.app(w.app(w.app(rec, mot), z), ms), w.bvar(0))), h={"regular": 1})
    big = w.app(s, z)
    for _ in range(m):
        big = w.app(w.const(D), big)
    B = nm("big"); w.defn(B, cN, big, h={"regular": 1}); cB = w.const(B)
    h = nm("h")
    lhs = w.app(cP, w.app(w.app(cgo, cB), w.bvar(0)))
    if kind == "bad":
        rhs = w.app(cP, w.app(cg, w.bvar(1)))
    else:
        rhs = w.app(cP, w.app(w.app(mkgo("go2"), cB), w.bvar(1)))
    w.thm(nm("t"), w.pi(y, cA, w.pi(h, lhs, rhs)), w.lam(y, cA, w.lam(h, lhs, w.bvar(0))))
    w.save(path)

def lst(n, kind, path):
    w = from_base(os.path.join(here, "..", "tests", "adv-base", "n.base"))
    cN = w.const(1); z = w.const(2); one = w.succ(0); ty = w.sort(one)
    nm = w.name; x = nm("x"); xs = nm("xs")
    L = nm("L"); w.axiom(L, ty); cL = w.const(L)
    nil = nm("nil"); w.axiom(nil, cL)
    cons = nm("cons"); w.axiom(cons, w.pi(x, cN, w.pi(xs, cL, cL))); cc = w.const(cons)
    body = w.const(nil)
    if kind == "bad":
        body = w.app(w.app(cc, w.const(nil)), body)
    for _ in range(n):
        body = w.app(w.app(cc, z), body)
    w.defn(nm("chars"), cL, body, h={"regular": 1})
    w.save(path)

lets(300000, os.path.join(outd, "lets_bad.ndjson"))
lst(1000000, "good", os.path.join(outd, "list_good.ndjson"))
lst(1000000, "bad", os.path.join(outd, "list_bad.ndjson"))
acc(20, "bad", os.path.join(outd, "acc_bad.ndjson"))
acc(20, "good", os.path.join(outd, "acc_good.ndjson"))

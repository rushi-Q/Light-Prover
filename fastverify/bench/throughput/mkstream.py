#!/usr/bin/python3 -I
"""mkstream.py CORPUS OUT [--n N] [--fail F] [--cheat C] [--seed S] : a synthetic stream of model-like proof attempts for
the batch verifier. Every attempt targets one of the corpus problems and is
  ok    : the problem's honest proof (expected ACCEPTED),
  fail  : the honest proof with an extra failing step (`exact v04_no_such_lemma`; does not compile -> REJECTED),
  cheat : a generic cheat applied to the statement, one of: `by sorry`, `sorryAx _ false`, `sorry` under
          `set_option warn.sorry false`, an extra `axiom` stating the theorem -> REJECTED.
Attempts are packed into batches OUT/batch-KKK/<theorem>.lean with at most one attempt per problem per batch (a batch
verifier needs distinct theorem names), in stream order. OUT/labels.json: batch -> {theorem: (kind, expected)}."""
import argparse, json, os, random, sys

ap = argparse.ArgumentParser()
ap.add_argument("corpus"); ap.add_argument("out")
ap.add_argument("--n", type=int, default=1000)
ap.add_argument("--fail", type=float, default=0.6)
ap.add_argument("--cheat", type=float, default=0.1)
ap.add_argument("--seed", type=int, default=1)
a = ap.parse_args()
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "corpus"))
import problems as M  # noqa: E402

rnd = random.Random(a.seed)
P = M.P
CHEATS = [
    lambda q: "by sorry",
    lambda q: "sorryAx _ false",
    lambda q: "by\n  set_option warn.sorry false in\n  sorry",
    None,   # extra axiom (prelude)
]


def thm(name, stmt, proof, pre=""):
    return M.PREAMBLE + "\n" + pre + "theorem " + name + " : " + stmt + " :=\n  " + proof.replace("\n", "\n  ") + "\n"


attempts = []
for i in range(a.n):
    q = rnd.choice(P)
    r = rnd.random()
    if r < a.fail:
        kind, exp = "fail", "REJECTED"
        pr = q["proof"]
        body = thm(q["name"], q["stmt"], "by\n  exact v04_no_such_lemma" if rnd.random() < 0.5 else
                   (pr + "\n  exact v04_no_such_lemma" if pr.startswith("by\n") else "by exact (v04_no_such_lemma : False).elim"))
    elif r < a.fail + a.cheat:
        kind, exp = "cheat", "REJECTED"
        c = rnd.choice(CHEATS)
        if c is None:
            body = thm(q["name"], q["stmt"], "v04_cheat", pre="axiom v04_cheat : " + q["stmt"] + "\n\n")
        else:
            body = thm(q["name"], q["stmt"], c(q))
    else:
        kind, exp = "ok", "ACCEPTED"
        body = thm(q["name"], q["stmt"], q["proof"])
    attempts.append((q["name"], kind, exp, body))

# pack: batch k = the k-th attempt of every problem, in stream order (greedy first-fit keeps batches large)
batches = []
for name, kind, exp, body in attempts:
    for b in batches:
        if name not in b:
            b[name] = (kind, exp, body)
            break
    else:
        batches.append({name: (kind, exp, body)})
os.makedirs(a.out, exist_ok=False)
labels = {}
for k, b in enumerate(batches):
    d = os.path.join(a.out, f"batch-{k:03d}")
    os.makedirs(d)
    labels[f"batch-{k:03d}"] = {}
    for name, (kind, exp, body) in b.items():
        open(os.path.join(d, name + ".lean"), "w").write(body)
        labels[f"batch-{k:03d}"][name] = [kind, exp]
json.dump(labels, open(os.path.join(a.out, "labels.json"), "w"), indent=1)
from collections import Counter
print(len(attempts), "attempts in", len(batches), "batches", dict(Counter(k for _, k, _, _ in attempts)),
      "batch sizes", [len(b) for b in batches])

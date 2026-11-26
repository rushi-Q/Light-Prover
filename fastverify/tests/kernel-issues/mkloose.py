#!/usr/bin/python3 -I
"""mkloose.py BASE.export OUTDIR : crafted exports for Lean issue #16489 ("Kernel: add_inductive accepts constructor type
with loose bound variable and stores a different type"; fixed in lean4 427023483c, after v4.36.0) and related
inductive-record attacks (#15100 constructor map key != embedded name, #15101 arbitrary quotInfo treated as canonical).
BASE = an official export of `inductive T (a : Type) : Type | mk : a -> T a` + `main_thm ... := (fun (_ : T Nat) => rfl)
(T.mk n)`."""
import json
import os
import sys

_h = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(_h, "..", "frontier-adversarial"))      # xmut.py (export editing helpers)
from xmut import X  # noqa: E402


def find_ind(x, tname):
    for k, o in enumerate(x.lines):
        if "inductive" in o:
            for t in o["inductive"]["types"]:
                if x.name_str(t["name"]) == tname:
                    return k, o
    raise KeyError(tname)


def main(base, out):
    os.makedirs(out, exist_ok=True)
    rows = []

    def emit(mid, x, note):
        p = os.path.join(out, mid + ".export")
        x.write(p)
        rows.append((mid, note))

    # L1: constructor type with a loose bvar: forall (a : Type), forall (y : #1), T a  (the issue's example shape)
    x = X(base)
    k, o = find_ind(x, "T")
    ind = json.loads(json.dumps(o["inductive"]))
    c = ind["ctors"][0]
    ty = x.lines  # noqa
    outer = x_expr(x, c["type"])            # forallE a (sort 1) (forallE y (bvar 0) (app T (bvar 1)))
    inner = x_expr(x, outer["forallE"]["body"])
    loose = x.add_expr("bvar", 1)
    nin = x.add_expr("forallE", dict(inner["forallE"], type=loose))
    nout = x.add_expr("forallE", dict(outer["forallE"], body=nin))
    c["type"] = nout
    x.lines[k] = {"inductive": ind}
    x.touch(k)
    emit("L1-ctor-loose-domain", x, "T.mk : forall (a : Type), forall (y : #1), T a  (loose bvar in a ctor field domain)")
    # L2: loose bvar in the RESULT of the ctor type: forall (a : Type), forall (y : a), T #2
    x = X(base)
    k, o = find_ind(x, "T")
    ind = json.loads(json.dumps(o["inductive"]))
    c = ind["ctors"][0]
    outer = x_expr(x, c["type"])
    inner = x_expr(x, outer["forallE"]["body"])
    app = x_expr(x, inner["forallE"]["body"])     # app T (bvar 1)
    nb = x.add_expr("app", dict(app["app"], arg=x.add_expr("bvar", 2)))
    nin = x.add_expr("forallE", dict(inner["forallE"], body=nb))
    c["type"] = x.add_expr("forallE", dict(outer["forallE"], body=nin))
    x.lines[k] = {"inductive": ind}
    x.touch(k)
    emit("L2-ctor-loose-result", x, "T.mk : forall (a : Type), forall (y : a), T #2  (loose bvar in the ctor result)")
    # L3: loose bvar in the inductive TYPE: T : forall (a : Type), #1
    x = X(base)
    k, o = find_ind(x, "T")
    ind = json.loads(json.dumps(o["inductive"]))
    t = ind["types"][0]
    tt = x_expr(x, t["type"])                      # forallE a (sort 1) (sort 1)
    t["type"] = x.add_expr("forallE", dict(tt["forallE"], body=x.add_expr("bvar", 1)))
    x.lines[k] = {"inductive": ind}
    x.touch(k)
    emit("L3-type-loose", x, "T : forall (a : Type), #1  (loose bvar in the inductive type)")
    # L4 (#15100 shape): constructor record whose `name` differs from the name listed in the type's ctors
    x = X(base)
    k, o = find_ind(x, "T")
    ind = json.loads(json.dumps(o["inductive"]))
    other = x.mk_name("T.mk2")
    ind["ctors"][0]["name"] = other
    x.lines[k] = {"inductive": ind}
    x.touch(k)
    emit("L4-ctor-name-mismatch", x, "ctor record named T.mk2 while T lists T.mk (constructor map key != embedded name)")
    # L5 (#15101 shape): a quot declaration record for a fresh name with Quot.lift's type (arbitrary quotInfo)
    x = X(base)
    qn = None
    for o in x.lines:
        if "quot" in o and x.name_str(o["quot"]["name"]) == "Quot.lift":
            qn = o["quot"]
    if qn is not None:
        fake = x.mk_name("Fake.lift")
        x.add_decl({"quot": dict(qn, name=fake)})
        emit("L5-fake-quot", x, "a quot record (kind lift) for a fresh name Fake.lift (arbitrary quotInfo)")
    # L6 (#15101 shape): Quot.lift's quot record with kind 'ind' (wrong kind for the canonical name)
    x = X(base)
    for kk, o in enumerate(x.lines):
        if "quot" in o and x.name_str(o["quot"]["name"]) == "Quot.lift":
            x.lines[kk] = {"quot": dict(o["quot"], kind="ind")}
            x.touch(kk)
            emit("L6-quot-wrong-kind", x, "Quot.lift's quot record with kind ind")
            break
    # L7 (#15101 exploit attempt): smuggle an AXIOM as a quot record: Fake.ax (kind lift) : forall n, n + 0 = n, and
    # main_thm := Fake.ax. ccmp's checkAxioms only flags axiomInfo (a quotInfo is not an axiom); the kernels must reject
    x = X(base)
    m = x.decl("thm", "main_thm")
    fake = x.mk_name("Fake.ax")
    x.add_decl({"quot": {"kind": "lift", "levelParams": [], "name": fake, "type": m["type"]}})
    v = x.add_expr("const", {"name": fake, "us": []})
    x.replace_decl("thm", "main_thm", {"thm": dict(m, value=v)})
    emit("L7-quot-smuggled-axiom", x, "main_thm := Fake.ax where Fake.ax is a quot record (kind lift) with main_thm's statement")
    # --- Replay's unsafe-constructor paths (a single-kernel case on pleanchecker-437) ---
    def unuse_T(x):
        """main_thm := fun n => (fun (_ : Nat) => rfl) n  - the closure no longer mentions T or T.mk (so ccmp's axiom
        check cannot see a fake constructor: only the kernels can)."""
        m = x.decl("thm", "main_thm")
        lam = x_expr(x, m["value"])                     # lam n : Nat . app (lam _ : T Nat . rfl) (T.mk Nat #0)
        app = x_expr(x, lam["lam"]["body"])
        inner = x_expr(x, app["app"]["fn"])
        nin = x.add_expr("lam", dict(inner["lam"], type=lam["lam"]["type"]))
        napp = x.add_expr("app", {"fn": nin, "arg": x.add_expr("bvar", 0)})
        x.replace_decl("thm", "main_thm", {"thm": dict(m, value=x.add_expr("lam", dict(lam["lam"], body=napp)))})

    def l1_ind(x, unsafe):
        k, o = find_ind(x, "T")
        ind = json.loads(json.dumps(o["inductive"]))
        c = ind["ctors"][0]
        outer = x_expr(x, c["type"])
        inner = x_expr(x, outer["forallE"]["body"])
        nin = x.add_expr("forallE", dict(inner["forallE"], type=x.add_expr("bvar", 1)))
        c["type"] = x.add_expr("forallE", dict(outer["forallE"], body=nin))
        c["isUnsafe"] = unsafe
        x.lines[k] = {"inductive": ind}
        x.touch(k)

    x = X(base)                      # control: the honest export with main_thm rewritten not to use T (must ACCEPT)
    unuse_T(x)
    emit("C0-control-unused", x, "CONTROL (must be ACCEPTED): honest T, main_thm := fun n => (fun (_ : Nat) => rfl) n")
    for used in (True, False):
        sfx = "" if used else "-unused"
        why = "" if used else "; main_thm no longer uses T (only the kernels can catch it)"
        # L8: the #16489 shape with an UNSAFE constructor record (Replay skips the postponed-constructor comparison
        # for unsafe constructors in some versions)
        x = X(base)
        l1_ind(x, True)
        if not used:
            unuse_T(x)
        emit("L8-loose-unsafe-ctor" + sfx, x, "T.mk : forall (a : Type), forall (y : #1), T a with isUnsafe=true" + why)
        # L9: #15100 shape with an unsafe constructor: wrong induct + cidx
        x = X(base)
        k, o = find_ind(x, "T")
        ind = json.loads(json.dumps(o["inductive"]))
        ind["ctors"][0]["induct"] = x.mk_name("Nat")
        ind["ctors"][0]["cidx"] = 1
        ind["ctors"][0]["isUnsafe"] = True
        x.lines[k] = {"inductive": ind}
        x.touch(k)
        if not used:
            unuse_T(x)
        emit("L9-unsafe-ctor-wrong-induct" + sfx, x, "T.mk record: induct=Nat, cidx=1, isUnsafe=true" + why)
        # L10: the constructor as an UNSAFE AXIOM record: T lists T.mk in ctors, the inductive line carries no ctor
        # record, an axiom record {name T.mk, isUnsafe true} follows the inductive line
        x = X(base)
        k, o = find_ind(x, "T")
        ind = json.loads(json.dumps(o["inductive"]))
        c = ind["ctors"].pop(0)
        x.lines[k] = {"inductive": ind}
        x.lines.insert(k + 1, {"axiom": {"isUnsafe": True, "levelParams": c["levelParams"], "name": c["name"],
                                         "type": c["type"]}})
        x.touch(k)
        if not used:
            unuse_T(x)
        emit("L10-unsafe-axiom-as-ctor" + sfx, x, "T lists T.mk; T.mk is an unsafe AXIOM record, no ctor record" + why)

    with open(os.path.join(out, "notes.tsv"), "w") as f:
        for r in rows:
            f.write("\t".join(r) + "\n")
    print(len(rows), "crafted exports")


def x_expr(x, eid):
    for o in reversed(x.lines):
        if "ie" in o and o["ie"] == eid:
            return {k: v for k, v in o.items() if k != "ie"}
    for o in x.new:
        if "ie" in o and o["ie"] == eid:
            return {k: v for k, v in o.items() if k != "ie"}
    raise KeyError(eid)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])

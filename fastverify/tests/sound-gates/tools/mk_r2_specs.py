#!/usr/bin/python3 -I
"""mk_r2_specs.py EXPORT CHALLENGE.export OUTDIR : systematic kernel-level mutation classes as fvmut specs, one
edit each, on an export such as the rh-mid reference export. Each mutant is labelled later by the OFFICIAL Lean 4.36
comparator (check/official/check.sh), so the classes need no expected verdict here. Chosen declarations lie outside the
challenge (so the statement comparison does not reject before the kernels run), as late in the file as possible.
Classes:
  K1 thm2axiom     a theorem turned into an axiom with the same type          (kernel-valid; only checkAxioms can reject)
  U1 lvl-drop      a theorem's first universe parameter removed               (unknown universe parameter)
  U2 lvl-swap      a theorem's two universe parameters swapped                (dependents instantiate them wrongly)
  R1 rec-rhs       a recursor rule's rhs replaced by another rule's rhs       (recursor differs from the kernel's)
  R2 rec-k         a recursor's K flag flipped                                (recursor differs from the kernel's)
  I1 ctor-fields   a constructor's numFields + 1                              (constructor differs from the kernel's)
  I2 ind-isrec     an inductive type's isRec flag flipped                     (type record differs; official behaviour decides)
  D1 dup-decl      a theorem line duplicated                                  (duplicate declaration)
  P1 proj-idx      a projection index + 1                                     (wrong field)
  L1 const-us      a constant's universe instantiation changed (u -> succ u)  (universe mismatch)
  B1 binder-info   a binder of a theorem's type made implicit                 (kernel ignores binder info: should stay valid)
"""
import json, os, sys

exp, chal, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)


def names_of(path):
    names = {0: ""}
    decl = set()
    with open(path, "rb") as f:
        for raw in f:
            if raw.startswith(b'{"in":'):
                j = json.loads(raw); i = j["in"]
                if "str" in j:
                    p = names[j["str"]["pre"]]; names[i] = (p + "." if p else "") + j["str"]["str"]
                else:
                    p = names[j["num"]["pre"]]; names[i] = (p + "." if p else "") + str(j["num"]["i"])
            elif raw.startswith((b'{"thm":', b'{"def":', b'{"axiom":', b'{"opaque":')):
                j = json.loads(raw); k = next(iter(j)); decl.add(names[j[k]["name"]])
            elif raw.startswith(b'{"inductive":'):
                j = json.loads(raw)
                for t in j["inductive"]["types"]:
                    decl.add(names[t["name"]])
    return names, decl


_, cdecl = names_of(chal)
names = {0: ""}
cand = {k: None for k in ["K1", "U1", "U2", "R1", "R2", "I1", "I2", "D1", "P1", "L1", "B1"]}
forall_lines = {}   # expr index -> (off, line) of forallE lines (for B1)
off = 0
with open(exp, "rb") as f:
    for raw in f:
        line = raw.decode().rstrip("\n")
        if raw.startswith(b'{"in":'):
            j = json.loads(raw); i = j["in"]
            if "str" in j:
                p = names[j["str"]["pre"]]; names[i] = (p + "." if p else "") + j["str"]["str"]
            else:
                p = names[j["num"]["pre"]]; names[i] = (p + "." if p else "") + str(j["num"]["i"])
        elif raw.startswith(b'{"thm":'):
            j = json.loads(raw)["thm"]
            nm = names[j["name"]]
            if nm not in cdecl:
                cand["K1"] = (off, line, nm, j)
                cand["D1"] = (off, line, nm, j)
                if len(j["levelParams"]) >= 1:
                    cand["U1"] = (off, line, nm, j)
                if len(j["levelParams"]) >= 2:
                    cand["U2"] = (off, line, nm, j)
                if j["type"] in forall_lines:
                    cand["B1"] = (forall_lines[j["type"]] + (nm,))
        elif raw.startswith(b'{"inductive":'):
            j = json.loads(raw)["inductive"]
            tn = names[j["types"][0]["name"]]
            if tn not in cdecl:
                for r in j["recs"]:
                    if len(r["rules"]) >= 2 and r["rules"][0]["rhs"] != r["rules"][1]["rhs"]:
                        cand["R1"] = (off, line, tn, j)
                cand["R2"] = (off, line, tn, j)
                if j["ctors"]:
                    cand["I1"] = (off, line, tn, j)
                cand["I2"] = (off, line, tn, j)
        elif raw.startswith(b'{"ie":') and b',"proj":' in raw:
            j = json.loads(raw)
            cand["P1"] = (off, line, "proj", {"proj": j["proj"], "ie": j["ie"]})
        elif raw.startswith(b'{"const":') and '"us":[' in line and '"us":[]' not in line:
            cand["L1"] = (off, line, "const", json.loads(raw))
        elif raw.startswith(b'{"forallE":') and '"binderInfo":"default"' in line:
            j = json.loads(raw)
            forall_lines[j["ie"]] = (off, line)
        off += len(raw)

specs = {}


def put(cls, off, old, new_lines, what):
    p = os.path.join(out, f"r2-{cls}.spec")
    with open(p, "w") as f:
        f.write(f"# {cls}: {what}\nE {off}\nO {old}\n")
        for n in new_lines:
            f.write(f"N {n}\n")
    specs[cls] = what


def sub1(line, old, new):
    assert line.count(old) == 1, (old, line[:200])
    return line.replace(old, new)


o, line, nm, j = cand["K1"]
lp = ",".join(str(x) for x in j["levelParams"])
put("K1", o, line, ['{"axiom":{"isUnsafe":false,"levelParams":[%s],"name":%d,"type":%d}}' % (lp, j["name"], j["type"])],
    f"theorem {nm} -> axiom with the same type")
o, line, nm, j = cand["U1"]
lp = j["levelParams"]
put("U1", o, line, [sub1(line, '"levelParams":[%s]' % ",".join(map(str, lp)), '"levelParams":[%s]' % ",".join(map(str, lp[1:])))],
    f"theorem {nm}: first universe parameter removed")
o, line, nm, j = cand["U2"]
lp = j["levelParams"]
sw = [lp[1], lp[0]] + lp[2:]
put("U2", o, line, [sub1(line, '"levelParams":[%s]' % ",".join(map(str, lp)), '"levelParams":[%s]' % ",".join(map(str, sw)))],
    f"theorem {nm}: universe parameters {lp[0]},{lp[1]} swapped")
o, line, nm, j = cand["R1"]
for r in j["recs"]:
    if len(r["rules"]) >= 2 and r["rules"][0]["rhs"] != r["rules"][1]["rhs"]:
        a, b = r["rules"][0]["rhs"], r["rules"][1]["rhs"]
        old = '"nfields":%d,"rhs":%d}' % (r["rules"][0]["nfields"], a)
        new = '"nfields":%d,"rhs":%d}' % (r["rules"][0]["nfields"], b)
        if line.count(old) == 1:
            put("R1", o, line, [sub1(line, old, new)], f"inductive {nm}: recursor {names[r['name']]} rule 0 rhs := rule 1 rhs")
            break
o, line, nm, j = cand["R2"]
r = j["recs"][0]
k = "true" if r["k"] else "false"; nk = "false" if r["k"] else "true"
old = '"k":%s,"levelParams"' % k
put("R2", o, line, [line.replace(old, '"k":%s,"levelParams"' % nk, 1)], f"inductive {nm}: recursor {names[r['name']]} K flag {k} -> {nk}")
o, line, nm, j = cand["I1"]
c = j["ctors"][0]
old = '"name":%d,"numFields":%d' % (c["name"], c["numFields"])
put("I1", o, line, [sub1(line, old, '"name":%d,"numFields":%d' % (c["name"], c["numFields"] + 1))],
    f"inductive {nm}: constructor {names[c['name']]} numFields +1")
o, line, nm, j = cand["I2"]
t = j["types"][0]
old = '"isRec":%s' % ("true" if t["isRec"] else "false")
put("I2", o, line, [sub1(line, old, '"isRec":%s' % ("false" if t["isRec"] else "true"))], f"inductive {nm}: isRec flipped")
o, line, nm, j = cand["D1"]
put("D1", o, line, [line, line], f"theorem {nm}: declaration line duplicated")
o, line, _, j = cand["P1"]
old = '"idx":%d' % j["proj"]["idx"]
put("P1", o, line, [sub1(line, old, '"idx":%d' % (j["proj"]["idx"] + 1))], f"projection expr {j['ie']}: idx {j['proj']['idx']} -> +1")
o, line, _, j = cand["L1"]
us = j["const"]["us"]
old = '"us":[%s]' % ",".join(map(str, us))
# u -> 0 (the level zero, index 0) for the first universe argument
new = '"us":[%s]' % ",".join(map(str, [0] + us[1:]))
if new == old:
    new = '"us":[%s]' % ",".join(map(str, [us[0] + 1] + us[1:]))
put("L1", o, line, [sub1(line, old, new)], f"const expr {j['ie']} ({names[j['const']['name']]}): universe args {us} -> {new}")
if cand["B1"]:
    o, line, nm = cand["B1"]
    put("B1", o, line, [sub1(line, '"binderInfo":"default"', '"binderInfo":"implicit"')],
        f"theorem {nm}: outermost binder of its type made implicit (expr shared with every user)")
json.dump(specs, open(os.path.join(out, "r2-specs.json"), "w"), indent=1)
for k, v in specs.items():
    print(k, v)

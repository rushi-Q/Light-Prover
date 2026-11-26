#!/usr/bin/python3 -I
"""mk_def_swap_spec.py EXPORT NAME_A NAME_B OUT.spec : fvmut spec that gives definition NAME_A the value of definition
NAME_B (same type required; e.g. Nat.add := Nat.sub's value): a kernel-valid but WRONG version of a kernel-implicit
constant, for the incremental-leg suite (a snapshot carrying it must never let the final step take the incremental path)."""
import json, sys
exp, na, nb, out = sys.argv[1:5]
names = {0: ""}
defs = {}
off = 0
with open(exp, "rb") as f:
    for raw in f:
        if raw.startswith(b'{"in":'):
            j = json.loads(raw); i = j["in"]
            if "str" in j:
                p = names[j["str"]["pre"]]; names[i] = (p + "." if p else "") + j["str"]["str"]
            else:
                p = names[j["num"]["pre"]]; names[i] = (p + "." if p else "") + str(j["num"]["i"])
        elif raw.startswith(b'{"def":'):
            j = json.loads(raw)
            n = names[j["def"]["name"]]
            if n in (na, nb):
                defs[n] = (off, raw.decode().rstrip("\n"), j["def"])
            if len(defs) == 2:
                break
        off += len(raw)
(oa, la, da), (_, _, db) = defs[na], defs[nb]
assert da["type"] == db["type"], "types differ"
old = '"value":%d' % da["value"]
assert la.count(old) == 1
new = la.replace(old, '"value":%d' % db["value"])
open(out, "w").write(f"# {na}: value := {nb}'s value (same type {da['type']})\nE {oa}\nO {la}\nN {new}\n")
print(f"{na} at {oa}: value {da['value']} -> {db['value']}")

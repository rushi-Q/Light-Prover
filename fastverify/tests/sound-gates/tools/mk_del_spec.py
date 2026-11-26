#!/usr/bin/python3 -I
"""mk_del_spec.py EXPORT NAME OUT.spec : fvmut spec that deletes the declaration line of NAME (an export that is no longer
closed; as a snapshot: a constant that arrives only with a later snapshot)."""
import json, sys
exp, nm, out = sys.argv[1:4]
names = {0: ""}
off = 0
with open(exp, "rb") as f:
    for raw in f:
        if raw.startswith(b'{"in":'):
            j = json.loads(raw); i = j["in"]
            if "str" in j:
                p = names[j["str"]["pre"]]; names[i] = (p + "." if p else "") + j["str"]["str"]
            else:
                p = names[j["num"]["pre"]]; names[i] = (p + "." if p else "") + str(j["num"]["i"])
        elif raw.startswith((b'{"def":', b'{"thm":', b'{"opaque":', b'{"axiom":')):
            j = json.loads(raw); k = next(iter(j))
            if names[j[k]["name"]] == nm:
                open(out, "w").write(f"# delete the declaration of {nm}\nE {off}\nO {raw.decode().rstrip(chr(10))}\n")
                print(f"{nm} at {off}")
                sys.exit(0)
        off += len(raw)
sys.exit(f"{nm} not found")

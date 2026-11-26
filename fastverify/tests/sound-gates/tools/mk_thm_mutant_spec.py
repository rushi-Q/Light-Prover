#!/usr/bin/python3 -I
"""mk_thm_mutant_spec.py SOLUTION.export CHALLENGE.export WHICH OUT.spec
Writes an fvmut spec that replaces the value of one theorem by its own type (kernel-invalid: 'declaration type
mismatch'), for a theorem whose name is NOT declared in the challenge export (so compareAt does not reject first).
WHICH = first | last | middle (position in the file). Names are resolved from the export's own name records."""
import json, sys

sol, chal, which, out = sys.argv[1:5]


def names_and_thms(path, want_thms):
    names = {0: ""}
    thms = []      # (offset, line, name_idx)
    decl_names = set()
    off = 0
    with open(path, "rb") as f:
        for raw in f:
            if raw.startswith(b'{"in":'):
                j = json.loads(raw)
                i = j["in"]
                if "str" in j:
                    p = names[j["str"]["pre"]]
                    names[i] = (p + "." if p else "") + j["str"]["str"]
                else:
                    p = names[j["num"]["pre"]]
                    names[i] = (p + "." if p else "") + str(j["num"]["i"])
            elif raw.startswith(b'{"thm":') or raw.startswith(b'{"def":') or raw.startswith(b'{"axiom":') or \
                    raw.startswith(b'{"opaque":') or raw.startswith(b'{"inductive":') or raw.startswith(b'{"quot":'):
                j = json.loads(raw)
                k = next(iter(j))
                if k == "inductive":
                    for t in j[k]["types"]:
                        decl_names.add(t["name"])
                else:
                    decl_names.add(j[k]["name"])
                if want_thms and k == "thm" and j[k]["value"] != j[k]["type"]:
                    thms.append((off, raw.decode().rstrip("\n"), j[k]["name"]))
            off += len(raw)
    return names, thms, decl_names


cn, _, cdecl = names_and_thms(chal, False)
chal_names = {cn[i] for i in cdecl}
sn, thms, _ = names_and_thms(sol, True)
cands = [t for t in thms if sn[t[2]] not in chal_names]
pick = {"first": cands[0], "last": cands[-1], "middle": cands[len(cands) // 2]}[which]
off, line, ni = pick
j = json.loads(line)
j["thm"]["value"] = j["thm"]["type"]
new = json.dumps(j, separators=(",", ":"), ensure_ascii=False)
# keep the exporter's key order: replace only the value field textually
old_val = '"value":%d' % json.loads(line)["thm"]["value"]
assert line.count(old_val) == 1
new = line.replace(old_val, '"value":%d' % j["thm"]["type"])
with open(out, "w") as f:
    f.write(f"# theorem {sn[ni]}: value -> its own type ({which} of {len(cands)} candidates outside the challenge)\n")
    f.write(f"E {off}\nO {line}\nN {new}\n")
print(f"{sn[ni]} at offset {off}; {len(cands)} candidates")

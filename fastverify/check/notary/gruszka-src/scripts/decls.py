# Lists declarations of an ndjson export: kind and name (for debugging).
import json, sys
names = {0: ""}
for line in open(sys.argv[1]):
    o = json.loads(line)
    if "in" in o:
        if "str" in o: names[o["in"]] = (names[o["str"]["pre"]] + "." if o["str"]["pre"] else "") + o["str"]["str"]
        else: names[o["in"]] = names[o["num"]["pre"]] + "." + str(o["num"]["i"])
    for k in ("def", "thm", "axiom", "opaque", "quot"):
        if k in o: print(k, names[o[k]["name"]])
    if "inductive" in o: print("inductive", [names[t["name"]] for t in o["inductive"]["types"]])

#!/usr/bin/python3 -I
"""export-names.py EXPORT [KIND...] — print 'kind<TAB>name' of every declaration of a lean4export NDJSON export (benchmark
helper: e.g. to pick edit targets that are inside the challenge's closure). KIND filters (thm, defn, opaque, axiom,
inductive, quot); default all."""
import json, sys
names = {0: ""}
kinds = set(sys.argv[2:])
out = sys.stdout
for line in open(sys.argv[1], encoding="utf-8"):
    if line.startswith('{"in":'):
        o = json.loads(line)
        if "str" in o:
            p = names[o["str"]["pre"]]; s = o["str"]["str"]
        else:
            p = names[o["num"]["pre"]]; s = str(o["num"]["i"])
        names[o["in"]] = (p + "." + s) if p else s
        continue
    if line.startswith('{"ie"') or line.startswith('{"il"') or line.startswith('{"bvar') or line.startswith('{"meta'):
        continue
    try:
        o = json.loads(line)
    except ValueError:
        continue
    for k, v in o.items():
        if isinstance(v, dict) and "name" in v and isinstance(v["name"], int) and (not kinds or k in kinds):
            out.write(f"{k}\t{names.get(v['name'], '?')}\n")
        elif k == "inductive" and isinstance(v, dict) and (not kinds or k in kinds):
            for t in v.get("types", []):
                out.write(f"inductive\t{names.get(t.get('name'), '?')}\n")

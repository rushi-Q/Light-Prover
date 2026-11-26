#!/usr/bin/python3 -I
"""simfill_select.py SRC MODULES_FILE TARGET_NAMES_FILE : find (target, lemmas) decompositions in a library: targets T
(from TARGET_NAMES_FILE, e.g. the challenge's theorem_names) whose tactic proof mentions >= 2 other theorems of the
same module that are themselves proved by a multi-line `:= by` tactic block. Prints JSON lines. Benchmark helper."""
import json, os, re, sys

src, modf, tnf = sys.argv[1:4]
tnames = set(l.strip() for l in open(tnf) if l.strip())
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+([^\s(:{\[]+)")
for m in (l.strip() for l in open(modf) if l.strip()):
    rel = m.replace(".", "/") + ".lean"
    p = os.path.join(src, rel)
    if not os.path.isfile(p):
        continue
    lines = open(p, encoding="utf-8").read().split("\n")
    decls = []   # (short, start, end, by_line)
    ns = []
    for i, ln in enumerate(lines):
        mm = DECL.match(ln)
        if mm:
            decls.append([mm.group(2), i, None])
        elif ln and not ln[0].isspace() and decls and decls[-1][2] is None and not ln.startswith(("--", "/-", "·")):
            decls[-1][2] = i
    for d in decls:
        if d[2] is None:
            d[2] = len(lines)
    info = {}
    for short, a, b in decls:
        body = "\n".join(lines[a:b])
        byl = next((j for j in range(a, b) if lines[j].rstrip().endswith(":= by")), None)
        info[short] = {"start": a, "end": b, "by": byl, "body": body, "multiline": byl is not None and b - byl > 2}
    for short, d in info.items():
        if not d["multiline"]:
            continue
        uses = [o for o, e in info.items() if o != short and e["multiline"] and e["start"] < d["start"]
                and re.search(r"(?<![\w.])" + re.escape(o.split(".")[-1]) + r"(?![\w'])", d["body"].split(":= by", 1)[-1])]
        if len(uses) >= 2:
            full = [t for t in tnames if t == short or t.endswith("." + short)]
            print(json.dumps({"module": m, "file": rel, "target": short, "target_full": full, "lemmas": uses}))

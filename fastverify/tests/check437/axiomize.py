#!/usr/bin/python3 -I
"""axiomize.py IN.export OUT.export MODE  - UNTRUSTED DIAGNOSTIC rewrite of an NDJSON 3.1.0 export: definition records become
axiom records of the same type (the body is dropped; the orphaned value expressions stay in the table), imitating the
module-system build's view in which imported non-@[expose] bodies are hidden. MODE: 'imported' = every def whose name does
not start with one of the project prefixes (GlobalTheory, GroundTheory, CompanionTheory, Development, Formalism, Lemmata,
PositivityTheory, LevelTowerAlt, ReciprocityTheory, CrystallineSemistableComparison, Cmp6, Main, Statements, RiemannHypothesis),
'all' = every def; 'thms-except:NAME[,NAME]' = every THEOREM record except the named ones becomes an axiom of the same type (the module
system's view: importers see theorems without bodies; the named targets keep their proofs and are checked); 'names:FILE' = exactly the names listed in FILE (one dotted name per line, e.g. the public-axiom /
private-def set produced by pubhidden); 'imported-regular' / 'all-regular' = the same but only definitions with `regular` reducibility
hints (abbrev = reducible wrappers such as outParam stay unfoldable; opaque stay). Prints counts. Never a verdict input."""
import json, sys
src, dst, mode = sys.argv[1], sys.argv[2], sys.argv[3]
NAMES = set(l.rstrip("\n") for l in open(mode[6:], encoding="utf-8")) if mode.startswith("names:") else None
KEEP = set(mode[len("thms-except:"):].split(",")) if mode.startswith("thms-except:") else None
PROJ = ("GlobalTheory", "GroundTheory", "CompanionTheory", "Development", "Formalism", "Lemmata", "PositivityTheory",
        "LevelTowerAlt", "ReciprocityTheory", "CrystallineSemistableComparison", "Cmp6", "Main", "Statements", "RiemannHypothesis")
names = {0: ()}; n_def = n_ax = 0
with open(src, "rb") as f, open(dst, "wb") as g:
    g.write(f.readline())
    for raw in f:
        if raw.startswith(b'{"in":'):
            o = json.loads(raw)
            if "str" in o: names[o["in"]] = names.get(o["str"]["pre"], ("?",)) + (o["str"]["str"],)
            elif "num" in o: names[o["in"]] = names.get(o["num"]["pre"], ("?",)) + (str(o["num"]["i"]),)
            g.write(raw); continue
        if KEEP is not None:
            if raw.startswith(b'{"thm":'):
                o = json.loads(raw)["thm"]; nm = ".".join(names.get(o["name"], ("?",)))
                n_def += 1
                if nm not in KEEP:
                    n_ax += 1
                    g.write((json.dumps({"axiom": {"isUnsafe": False, "levelParams": o["levelParams"], "name": o["name"], "type": o["type"]}},
                                        sort_keys=True, separators=(",", ":")) + "\n").encode()); continue
            g.write(raw); continue
        if raw.startswith(b'{"def":'):
            n_def += 1
            o = json.loads(raw)["def"]
            nm = names.get(o["name"], ("?",))
            reg = isinstance(o.get("hints"), dict) and "regular" in o["hints"]
            base = mode.split("-")[0]; only_regular = mode.endswith("-regular")
            hide = (base == "all" or (base == "imported" and nm[0] not in PROJ)) and (reg or not only_regular)
            if NAMES is not None: hide = ".".join(nm) in NAMES
            if hide and o.get("safety", "safe") == "safe":
                n_ax += 1
                g.write((json.dumps({"axiom": {"isUnsafe": False, "levelParams": o["levelParams"], "name": o["name"], "type": o["type"]}},
                                    sort_keys=True, separators=(",", ":")) + "\n").encode()); continue
        g.write(raw)
print(f"{mode}: {n_def} defs seen, {n_ax} turned into axioms -> {dst}", file=sys.stderr)

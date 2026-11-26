#!/usr/bin/python3 -I
"""tools/fvwork/mkedits.py - generate an AGENT-LIKE edit stream over a Lean project for tools/fvwork/replay.py --edits
(benchmark input, untrusted).

  mkedits.py SRC MODULES_FILE N [--seed S] [--pattern break,sorry,fix] > edits.jsonl

SRC = the project at the base state; MODULES_FILE = module names (one per line; e.g. the modules of the challenge's
closure); N = number of theorems to "work on". For each chosen theorem (a `theorem`/`lemma` whose proof starts with
`:= by` on its line), the stream contains one state per pattern step, each a JSON line {"label", "files": {rel: content}}
with the FULL content of the edited file (the daemon applies it over its current base):
  break  a wrong step inserted after ':= by' ('have _fvw : (2 : Nat) + 2 = 5 := by decide') -> the module fails
  sorry  a placeholder step ('have _fvw : (2 : Nat) + 2 = 4 := sorry')          -> builds with a warning, check REJECTS
  fix    a valid extra step ('have _fvw : (2 : Nat) + 2 = 4 := by decide')     -> the proof term changes, ACCEPTED
  orig   the original file again                                               -> ACCEPTED (export = base's)
This mimics an agent iterating on one lemma (failed attempt, placeholder, success) before moving to the next.
"""
import json, os, random, re, sys


def main():
    a = sys.argv[1:]
    if len(a) < 3:
        sys.exit(__doc__)
    src, modf, n = os.path.realpath(a[0]), a[1], int(a[2])
    seed, pattern = 1, ["break", "sorry", "fix"]
    if "--seed" in a:
        seed = int(a[a.index("--seed") + 1])
    if "--pattern" in a:
        pattern = a[a.index("--pattern") + 1].split(",")
    rnd = random.Random(seed)
    mods = [l.strip() for l in open(modf) if l.strip()]
    cands = []
    for m in mods:
        rel = m.replace(".", "/") + ".lean"
        p = os.path.join(src, rel)
        if not os.path.isfile(p):
            continue
        lines = open(p, encoding="utf-8").read().split("\n")
        for i, ln in enumerate(lines):
            if re.match(r"^\s*(theorem|lemma)\s", ln) and ln.rstrip().endswith(":= by") and i + 1 < len(lines) \
                    and lines[i + 1].strip() and not lines[i + 1].strip().startswith(("--", "·", "case", "next", "|")):
                cands.append((rel, i))
    rnd.shuffle(cands)
    used = set()
    out = 0
    for rel, i in cands:
        if out >= n or rel in used:
            continue
        used.add(rel)
        text = open(os.path.join(src, rel), encoding="utf-8").read()
        lines = text.split("\n")
        ind = re.match(r"^(\s*)", lines[i + 1]).group(1) or "  "
        steps = {"break": f"{ind}have _fvw : (2 : Nat) + 2 = 5 := by decide",
                 "sorry": f"{ind}have _fvw : (2 : Nat) + 2 = 4 := sorry",
                 "fix": f"{ind}have _fvw : (2 : Nat) + 2 = 4 := by decide"}
        name = lines[i].split()[1] if len(lines[i].split()) > 1 else "?"
        for k in pattern:
            if k == "orig":
                body = text
            else:
                body = "\n".join(lines[:i + 1] + [steps[k]] + lines[i + 1:])
            print(json.dumps({"label": f"{k}:{rel}:{name}", "kind": k, "files": {rel: body}}))
        out += 1
    if out < n:
        print(f"mkedits: only {out} theorems found", file=sys.stderr)


if __name__ == "__main__":
    main()

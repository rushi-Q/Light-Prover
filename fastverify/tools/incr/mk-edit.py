#!/usr/bin/python3 -I
"""tools/incr/mk-edit.py SRC OUT MODULE KIND [DECL] — make an edited copy of a Lean project (benchmark input).

OUT = copy of SRC (hard links, except the edited file, which is a new file) with ONE edit in MODULE (dotted name, file
under the lakefile's srcDir; looked up as SRC/**/<path>.lean). KIND:
  have    a valid proof edit: after the first line ending in ':= by' a line '  have _v05edit : (2 : Nat) + 2 = 4 := rfl'
          (indented like the next line) -> the proof term of that declaration changes, the module and every importer must be
          rebuilt, the export changes in that declaration only
  term    like 'have', for a term-mode proof ':= TERM' on its own line: ':= by\n  have ...\n  exact TERM' (first match)
  append  a new unused theorem at the end of the module (module + importers rebuilt; the export does not change)
  sorry   after the first ':= by' line a line 'have _v05edit : (2 : Nat) + 2 = 4 := sorry' -> the proof uses sorryAx: the
          build succeeds (warning only), the check must REJECT
  break   after the first ':= by' line a line 'have _v05edit : (2 : Nat) + 2 = 5 := rfl' -> the module fails to build
DECL (optional): the last name component of the declaration to edit; the search for ':= by' starts at the line that
declares 'theorem DECL' / 'lemma DECL' (default: the first match in the file).
Prints the edited file's path and the edited line number.
"""
import os, re, shutil, subprocess, sys


def main():
    src, out, mod, kind = sys.argv[1:5]
    decl = sys.argv[5] if len(sys.argv) > 5 else None
    src = os.path.realpath(src)
    rel = mod.replace(".", "/") + ".lean"
    cands = []
    for root, dirs, files in os.walk(src):
        if ".lake" in dirs:
            dirs.remove(".lake")
        p = os.path.join(root, os.path.basename(rel))
        if os.path.relpath(p, src).endswith(rel) and os.path.isfile(p):
            cands.append(p)
    if len(cands) != 1:
        sys.exit(f"mk-edit: module {mod}: {len(cands)} candidate files")
    f = cands[0]
    if os.path.exists(out):
        sys.exit(f"mk-edit: {out} exists")
    if subprocess.run(["cp", "-al", src, out], capture_output=True).returncode != 0:   # other file system: plain copy
        shutil.rmtree(out, ignore_errors=True)
        subprocess.run(["cp", "-a", src, out], check=True)
    g = os.path.join(out, os.path.relpath(f, src))
    lines = open(f, encoding="utf-8").read().split("\n")
    at = None
    start = 0
    if decl:
        dre = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\s+"
                         + re.escape(decl) + r"(?![\w'.])")
        hits = [i for i, l in enumerate(lines) if dre.search(l)]
        if len(hits) != 1:
            shutil.rmtree(out, ignore_errors=True)
            sys.exit(f"mk-edit: declaration {decl}: {len(hits)} matches in {f}")
        start = hits[0]
    if kind == "append":
        lines += ["", "theorem _v05_appended_edit : (2 : Nat) + 2 = 4 := rfl", ""]
        at = len(lines) - 2
    elif kind in ("have", "sorry", "break"):
        for i, l in enumerate(lines):
            if i < start:
                continue
            if re.search(r":=\s*by\s*$", l) and i + 1 < len(lines) and lines[i + 1].strip():
                ind = re.match(r"\s*", lines[i + 1]).group(0)
                pf = os.environ.get("MKEDIT_PROOF", "rfl")   # e.g. 'by decide' where `rfl` is shadowed (Mathlib namespaces)
                new = {"have": f"have _v05edit : (2 : Nat) + 2 = 4 := {pf}", "sorry": "have _v05edit : (2 : Nat) + 2 = 4 := sorry",
                       "break": "have _v05edit : (2 : Nat) + 2 = 5 := rfl"}[kind]
                lines.insert(i + 1, ind + new)
                at = i + 2
                break
    elif kind == "term":
        for i, l in enumerate(lines):
            if i <= start and decl:
                continue
            m = re.match(r"^(\s*)(.*\S)\s*$", l)
            if i > 0 and re.search(r":=\s*$", lines[i - 1]) and m and not l.strip().startswith(("by", "--", "fun", "⟨")):
                ind = m.group(1)
                lines[i - 1] = lines[i - 1].rstrip() + " by"
                pf = os.environ.get("MKEDIT_PROOF", "rfl")
                lines[i:i + 1] = [ind + f"have _v05edit : (2 : Nat) + 2 = 4 := {pf}", ind + "exact " + m.group(2)]
                at = i + 1
                break
    if at is None:
        shutil.rmtree(out, ignore_errors=True)
        sys.exit(f"mk-edit: no place for a '{kind}' edit in {f}")
    os.unlink(g)
    with open(g, "w", encoding="utf-8") as o:
        o.write("\n".join(lines))
    shutil.copystat(f, g)
    print(g, at)


if __name__ == "__main__":
    main()

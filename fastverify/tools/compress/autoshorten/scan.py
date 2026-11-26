#!/usr/bin/env python3
"""scan.py SRC_ROOT OUT.jsonl [--files LIST]
Split every Lean file under SRC_ROOT into top-level commands (column-0 heuristics, good for machine-formatted code)
and write one JSON record per theorem/lemma: file, name, line range (1-based, inclusive) of the whole command
(docstring + attributes included), the line/col of ':=' that starts the proof, signature text, proof kind
(tactic 'by' / term / match), proof size (lines, chars), modifiers.
Pure text analysis; nothing is elaborated."""
import json, os, re, sys

KW = ("theorem", "lemma", "def", "instance", "abbrev", "structure", "inductive", "class", "example", "opaque", "axiom",
      "macro", "macro_rules", "syntax", "elab", "elab_rules", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
      "set_option", "attribute", "open", "namespace", "section", "end", "variable", "universe", "noncomputable",
      "include", "omit", "local", "scoped", "private", "protected", "nonrec", "partial", "unsafe", "mutual", "import",
      "initialization", "builtin_initialize", "deriving", "export", "add_decl_doc", "irreducible_def", "alias", "suppress_compilation",
      "unseal", "seal", "public", "meta", "module", "prelude")
START_RE = re.compile(r"^(@\[|/--|/-|--|#[a-z_]+\b|(" + "|".join(KW) + r")\b)")
MODS = {"private", "protected", "noncomputable", "nonrec", "partial", "unsafe"}


def find_assign(text, start):
    """index of the first ':=' at bracket depth 0 (outside comments/strings) in text[start:], or of a '\n|' match arm,
    whichever comes first. Returns (idx, kind) with kind ':=' or '|' or None."""
    depth = 0
    i, n = start, len(text)
    while i < n:
        c = text[i]
        if text.startswith("/-", i):
            d = 1; i += 2
            while i < n and d:
                if text.startswith("/-", i): d += 1; i += 2
                elif text.startswith("-/", i): d -= 1; i += 2
                else: i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i); i = n if j < 0 else j; continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1; continue
        if c in "([{⟨⦃": depth += 1
        elif c in ")]}⟩⦄": depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return i, ":="
        elif depth == 0 and c == "\n" and text[i + 1:].lstrip(" ").startswith("|"):
            return i, "|"
        i += 1
    return None, None


def commands(lines):
    """yield (start, end) 0-based inclusive line ranges of top-level commands; a docstring/attribute line is merged with
    the following command."""
    starts = [i for i, l in enumerate(lines) if l and not l[0].isspace() and START_RE.match(l)]
    # inside a block comment / docstring, column-0 lines are not command starts
    good, incomment = [], False
    depth = 0
    s = set(starts)
    for i, l in enumerate(lines):
        if depth == 0 and i in s:
            good.append(i)
        depth += l.count("/-") - l.count("-/")
        if depth < 0: depth = 0
    starts = good
    out = []
    for k, st in enumerate(starts):
        en = (starts[k + 1] - 1) if k + 1 < len(starts) else len(lines) - 1
        while en > st and not lines[en].strip():
            en -= 1
        out.append([st, en])
    # merge docstring / attribute-only commands into the next command
    merged, pend = [], None
    for st, en in out:
        head = lines[st]
        is_prefix = head.startswith("/--") or (head.startswith("@[") and re.match(r"^@\[[^\]]*\]\s*$", "\n".join(lines[st:en + 1]).strip() + "") is not None)
        if pend is not None:
            st = pend; pend = None
        if is_prefix:
            pend = st; continue
        if head.startswith("--") or (head.startswith("/-") and not head.startswith("/--")):
            # plain comment: its own (non-decl) command
            merged.append((st, en)); continue
        merged.append((st, en))
    return merged


DECL_RE = re.compile(r"(?:^|\s)(theorem|lemma)\s+([^\s(\[{:]+)")


def scan_file(path, rel):
    try:
        text = open(path, encoding="utf-8").read()
    except Exception:
        return []
    lines = text.split("\n")
    offs = [0]
    for l in lines:
        offs.append(offs[-1] + len(l) + 1)
    recs = []
    for st, en in commands(lines):
        body = "\n".join(lines[st:en + 1])
        # strip docstring
        b0 = 0
        if body.startswith("/--"):
            j = body.find("-/")
            b0 = j + 2 if j >= 0 else 0
        m = DECL_RE.search(body, b0)
        if not m:
            continue
        pre = body[b0:m.start(1)]
        # only accept if what precedes the keyword is attributes / modifiers
        pre_s = re.sub(r"@\[[^\]]*\]", " ", pre).split()
        if any(w not in MODS for w in pre_s):
            continue
        kw, name = m.group(1), m.group(2)
        idx, kind = find_assign(body, m.end())
        if idx is None:
            recs.append(dict(file=rel, name=name, kw=kw, l0=st + 1, l1=en + 1, kind="none"))
            continue
        sig = body[m.end():idx].strip()
        if kind == "|":
            recs.append(dict(file=rel, name=name, kw=kw, l0=st + 1, l1=en + 1, kind="match", sig=sig))
            continue
        proof = body[idx + 2:]
        ps = proof.strip()
        pk = "by" if re.match(r"by\b", ps) else "term"
        # line/col of ':='
        aline = st + body.count("\n", 0, idx)
        acol = idx - (body.rfind("\n", 0, idx) + 1)
        where = bool(re.search(r"\n\s*where\b|\swhere\s*$", proof))
        recs.append(dict(file=rel, name=name, kw=kw, mods=pre_s, attrs=re.findall(r"@\[[^\]]*\]", pre), l0=st + 1,
                         l1=en + 1, al=aline + 1, ac=acol, kind=pk, where=where, sig=sig,
                         plines=ps.count("\n") + 1, pchars=len(ps), sigchars=len(sig),
                         doc=body.startswith("/--")))
    return recs


def main():
    root, outp = sys.argv[1], sys.argv[2]
    files = None
    if "--files" in sys.argv:
        files = [l.strip() for l in open(sys.argv[sys.argv.index("--files") + 1]) if l.strip()]
    if files is None:
        files = []
        for d, _, fs in os.walk(root):
            for f in fs:
                if f.endswith(".lean"):
                    files.append(os.path.relpath(os.path.join(d, f), root))
        files.sort()
    with open(outp, "w") as o:
        for rel in files:
            for r in scan_file(os.path.join(root, rel), rel):
                o.write(json.dumps(r, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main()

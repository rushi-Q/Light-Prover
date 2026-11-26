#!/usr/bin/env python3
"""mut.py BASE_CORPUS OUT [MATHLIB_SAMPLE [all|core|mathlib]] -> OUT/{cases,challenges,cases.json}: SOURCE-LEVEL MUTATION CAMPAIGN.

BASE_CORPUS = a corpus of honest one-challenge projects in the layout of a generated small-proof corpus
(projects/<id>/Solution.lean + challenges/<id>/ + cases.json with "imports"). For every base project whose first target
theorem has the shape `theorem NAME SIG := PROOF` (top level, one declaration), nine mutants of the solution are written:
  sorry     PROOF := sorry                                            (expected REJECTED: axiom sorryAx)
  axiom     axiom cheat_ax : False; PROOF := cheat_ax.elim               (REJECTED: illegal axiom)
  thm2ax    the target declared as `axiom NAME SIG`                       (REJECTED: kind mismatch)
  native    PROOF := by native_decide                                    (REJECTED: native_decide axiom, or build fails)
  skipk     set_option debug.skipKernelTC true in ... := by decide +kernel (oracle decides: kernel-valid if decidable+true)
  envhack   honest proof kept under NAME_orig, NAME added by Environment.addDeclCore (doCheck := false) with the same
            type and the ill-typed value True.intro                     (REJECTED: kernel)
  numeral   the first numeral of SIG incremented                         (REJECTED: statement, or build fails)
  weak      an extra first hypothesis (_hcheat : False), proof _hcheat.elim (REJECTED: statement)
  unusedax  honest + an unused axiom and an unused theorem using it      (ACCEPTED: unused axioms are allowed)
The reference preset (official flow) is the oracle; the expected values are only a-priori guesses.
MATHLIB_SAMPLE (default 40) = how many Mathlib-based bases are used (every core-only base is used).
"""
import json, os, random, re, shutil, sys

base, out = sys.argv[1], sys.argv[2]
msample = int(sys.argv[3]) if len(sys.argv) > 3 else 40
which = sys.argv[4] if len(sys.argv) > 4 else "all"   # all | core | mathlib
meta = json.load(open(os.path.join(base, "cases.json")))
TOP = re.compile(r"^(theorem|lemma|def|instance|example|#|@\[|open|namespace|end|section|set_option|abbrev|structure|class|"
                 r"inductive|noncomputable|private|protected|macro|syntax|axiom|variable|universe|attribute|local|scoped|import|elab|notation)\b")

def split_target(src, name):
    lines = src.split("\n")
    for i, l in enumerate(lines):
        if re.match(r"theorem %s(\s|$)" % re.escape(name), l):
            j = i + 1
            while j < len(lines) and not TOP.match(lines[j]):
                j += 1
            decl = "\n".join(lines[i:j]).rstrip()
            k = decl.find(":=")
            if k < 0 or " where" in decl[:k]:
                return None
            sig = decl[len("theorem " + name):k]
            return "\n".join(lines[:i]), sig, decl[k + 2:], "\n".join(lines[j:])
    return None

def mutants(src, name, core):
    sp = split_target(src, name)
    if not sp:
        return {}
    pre, sig, proof, post = sp
    T = lambda body: pre + "\n" + body + "\n" + post
    hdr_lean = ("import Lean\n" if core and not src.lstrip().startswith("import") else "")
    m = {}
    m["sorry"] = T("theorem %s%s:= sorry" % (name, sig))
    m["axiom"] = T("axiom cheat_ax : False\n\ntheorem %s%s:= cheat_ax.elim" % (name, sig))
    m["thm2ax"] = T("axiom %s%s" % (name, sig.rstrip()))
    m["native"] = T("theorem %s%s:= by native_decide" % (name, sig))
    m["skipk"] = T("set_option debug.skipKernelTC true in\ntheorem %s%s:= by decide +kernel" % (name, sig))
    hack = ("theorem %s_orig%s:=%s\n\nopen Lean Elab Command in\nrun_cmd do\n"
            "  let some ci := (← getEnv).find? `%s_orig | throwError \"no orig\"\n"
            "  let v : TheoremVal := { name := `%s, levelParams := ci.levelParams, type := ci.type, value := mkConst ``True.intro, all := [`%s] }\n"
            "  match (← getEnv).addDeclCore 0 0 (Declaration.thmDecl v) none (doCheck := false) with\n"
            "  | .ok env => setEnv env\n  | .error _ => throwError \"addDeclCore failed\"") % (name, sig, proof, name, name, name)
    if src.lstrip().startswith("import"):
        m["envhack"] = T(hack)
    else:
        m["envhack"] = "import Lean\n" + T(hack)
    nm = re.search(r"(?<![\w.^])(\d+)(?![\w.])", sig)
    if nm:
        m["numeral"] = T("theorem %s%s%d%s:=%s" % (name, sig[:nm.start()], int(nm.group(1)) + 1, sig[nm.end():], proof))
    m["weak"] = T("theorem %s (_hcheat : False)%s:= _hcheat.elim" % (name, sig))
    m["unusedax"] = src.rstrip() + "\n\naxiom unused_cheat : False\ntheorem not_a_target_cheat : False := unused_cheat\n"
    return m

EXPECT = {"sorry": "REJECTED", "axiom": "REJECTED", "thm2ax": "REJECTED", "native": "REJECTED", "skipk": "?",
          "envhack": "REJECTED", "numeral": "REJECTED", "weak": "REJECTED", "unusedax": "ACCEPTED"}

if __name__ == "__main__":
    core = sorted(k for k, v in meta.items() if v.get("imports") == "(core)" and v.get("n_theorems", 1) == 1)
    ml = sorted(k for k, v in meta.items() if v.get("imports") != "(core)" and v.get("n_theorems", 1) == 1
                and v.get("style") not in ("batch10", "batch", "same"))
    random.seed(20261122)
    bases = core + sorted(random.sample(ml, min(msample, len(ml))))
    if which == "core":
        bases = core
    elif which == "mathlib":
        bases = [b for b in bases if b not in core]
    os.makedirs(os.path.join(out, "cases"), exist_ok=True)
    os.makedirs(os.path.join(out, "challenges"), exist_ok=True)
    cases, skipped = {}, []
    for b in bases:
        cfg = json.load(open(os.path.join(base, "challenges", b, "comparator.json")))
        name = cfg["theorem_names"][0]
        src = open(os.path.join(base, "projects", b, "Solution.lean"), encoding="utf-8").read()
        is_core = meta[b].get("imports") == "(core)"
        ms = mutants(src, name, is_core)
        if not ms:
            skipped.append(b)
            continue
        shutil.copytree(os.path.join(base, "challenges", b), os.path.join(out, "challenges", b), dirs_exist_ok=True)
        for op, text in [("honest", src)] + sorted(ms.items()):
            cid = "%s__%s" % (b, op)
            d = os.path.join(out, "cases", cid)
            if os.path.exists(d):
                shutil.rmtree(d)
            shutil.copytree(os.path.join(base, "projects", b), d, ignore=shutil.ignore_patterns(".lake"))
            with open(os.path.join(d, "Solution.lean"), "w", encoding="utf-8") as f:
                f.write(text)
            cases[cid] = {"challenge": b, "expected_official": "ACCEPTED" if op == "honest" else EXPECT[op], "cls": op,
                          "catcher": "-", "desc": "%s of base %s (%s, style %s)" % (op, b, meta[b].get("imports"), meta[b].get("style")),
                          "mathlib": not is_core}
    json.dump(cases, open(os.path.join(out, "cases.json"), "w"), indent=1)
    print("bases %d (core %d, mathlib %d), skipped %s, cases %d" % (len(bases) - len(skipped), len(core),
          len(bases) - len(core), skipped, len(cases)))

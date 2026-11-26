#!/usr/bin/env python3
"""mkarc.py SRC_MATHLIB OUTROOT : the "Archive" case: Mathlib's Archive (IMO / Wiedijk-100 style competition
and textbook proofs, 85 modules) + Counterexamples (30 modules) as ONE downstream project on the cached Mathlib 0df444a.
Targets: 7 IMO theorems whose statements use only Mathlib constants (challenge statements written out explicitly)."""
import json, os, shutil, subprocess, sys
SRC, OUT = sys.argv[1], sys.argv[2]
WS_MANIFEST = os.environ.get("WS_MANIFEST", "$LIGHT_LEAN/verify/challenge/lake-manifest.json")
MODS = ["Archive.Imo.Imo1959Q1", "Archive.Imo.Imo1964Q1", "Archive.Imo.Imo2001Q6", "Archive.Imo.Imo2008Q3",
        "Archive.Imo.Imo2011Q5", "Archive.Imo.Imo2019Q4"]
STMTS = [
 ("imo1959_q1", "∀ n : ℕ, Nat.Coprime (21 * n + 4) (14 * n + 3)"),
 ("imo1964_q1a", "∀ (n : ℕ) (_ : 0 < n), 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n"),
 ("imo1964_q1b", "∀ (n : ℕ), ¬7 ∣ 2 ^ n + 1"),
 ("imo2001_q6", "∀ {a b c d : ℤ} (hd : 0 < d) (hdc : d < c) (hcb : c < b) (hba : b < a)\n    (h : a * c + b * d = (a + b - c + d) * (-a + b + c + d)), ¬_root_.Prime (a * b + c * d)"),
 ("imo2008_q3", "∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧\n    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + Real.sqrt (2 * n)"),
 ("imo2011_q5", "∀ (f : ℤ → ℤ) (hpos : ∀ n : ℤ, 0 < f n) (hdvd : ∀ m n : ℤ, f (m - n) ∣ f m - f n),\n    ∀ m n : ℤ, f m ≤ f n → f m ∣ f n"),
 ("imo2019_q4", "∀ {k n : ℕ} (hk : 0 < k) (hn : 0 < n),\n    (Nat.factorial k : ℤ) = ∏ i ∈ Finset.range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) ↔ (k, n) = (1, 1) ∨ (k, n) = (3, 2)"),
]
LEANOPTS = """leanOptions = { pp.unicode.fun = true, autoImplicit = false, maxSynthPendingDepth = 3, weak.linter.mathlibStandardSet = true, weak.linter.style.header = true, weak.linter.checkInitImports = true, weak.linter.allScriptsDocumented = true, weak.linter.pythonStyle = true, weak.linter.style.longFile = 1500 }"""
REQ = ('[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\n'
       'rev = "0df444a360eaa60ab8c11dca51a86af692955474"\n')
case = "archive"
pd = os.path.join(OUT, "proj", case); cd = os.path.join(OUT, "chal", case)
for d in (pd, cd):
    if os.path.exists(d): shutil.rmtree(d)
    os.makedirs(d)
# the mathlib package itself declares lean_libs `Archive` and `Counterexamples`: modules of those names would resolve to the
# (read-only) dependency (official lake build: "read-only file system"), so the roots are renamed Arc / Cex (imports rewritten)
import re
REN = {"Archive": "Arc", "Counterexamples": "Cex"}
def rew(txt):
    return re.sub(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+)(Archive|Counterexamples)\b', lambda m: m.group(1) + REN[m.group(2)], txt, flags=re.M)
for x, y in REN.items():
    for dp, dns, fns in os.walk(os.path.join(SRC, x)):
        rel = os.path.relpath(dp, os.path.join(SRC, x))
        od = os.path.normpath(os.path.join(pd, y, rel)); os.makedirs(od, exist_ok=True)
        for fn in fns:
            src = os.path.join(dp, fn); dst = os.path.join(od, fn)
            if fn.endswith(".lean"): open(dst, "w").write(rew(open(src, encoding="utf-8").read()))
            else: shutil.copy(src, dst)
    open(os.path.join(pd, y + ".lean"), "w").write(rew(open(os.path.join(SRC, x + ".lean"), encoding="utf-8").read()))
MODS = [m.replace("Archive.", "Arc.", 1) for m in MODS]
shutil.copy(os.path.join(SRC, "lean-toolchain"), pd); shutil.copy(os.path.join(SRC, "lean-toolchain"), cd)
with open(os.path.join(pd, "lakefile.toml"), "w") as f:
    f.write(f'name = "archive"\ndefaultTargets = ["Arc", "Cex", "Solution"]\n\n{REQ}\n'
            f'[[lean_lib]]\nname = "Arc"\n{LEANOPTS}\n\n[[lean_lib]]\nname = "Cex"\n{LEANOPTS}\n\n'
            f'[[lean_lib]]\nname = "Solution"\n')
with open(os.path.join(pd, "Solution.lean"), "w") as f:
    f.write("".join(f"import {m}\n" for m in MODS) + "\n/-! Archive case: the targets are the Archive theorems themselves -/\n")
for d, nm in ((pd, "archive"), (cd, "arcchal")):
    wm = json.load(open(WS_MANIFEST)); wm["name"] = nm
    json.dump(wm, open(os.path.join(d, "lake-manifest.json"), "w"), indent=1)
with open(os.path.join(cd, "Challenge.lean"), "w") as f:
    f.write("import Mathlib\n\n/-! Clean challenge for the Archive case (explicit statements, Mathlib constants only) -/\n\n")
    for n, st in STMTS: f.write(f"theorem {n} : {st} :=\n  sorry\n\n")
with open(os.path.join(cd, "lakefile.toml"), "w") as f:
    f.write(f'name = "arcchal"\ndefaultTargets = ["Challenge"]\n\n{REQ}\n[[lean_lib]]\nname = "Challenge"\n')
json.dump({"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": [n for n, _ in STMTS],
           "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]},
          open(os.path.join(cd, "comparator.json"), "w"), indent=1)
print(case, pd, cd)

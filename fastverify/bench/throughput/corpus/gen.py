#!/usr/bin/python3 -I
"""gen.py OUTDIR : the small-proof corpus (competition-style problems on Mathlib 0df444a / Lean 4.33.1).

Writes
  OUTDIR/challenges/<name>/   one clean challenge per problem (statement := sorry), comparator.json Lean-kernel only
  OUTDIR/projects/<name>/     the solution project of each problem (one module `Solution`)
  OUTDIR/projects/<name>--<kind>/  negative variants (AI-prover cheating patterns) of some problems; challenge = <name>
  OUTDIR/challenges/BATCH, OUTDIR/projects/BATCH   all problems in ONE project (one module per problem) / ONE challenge
  OUTDIR/cases.json           case -> {challenge, expected_official, style, kind}
Challenge and solution statements are textually identical (same preamble), except where a variant changes them.
"""
import json, os, shutil, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import problems as M  # noqa: E402

TOOLCHAIN = "leanprover/lean4:v4.33.1\n"
MANIFEST = os.path.join(os.environ.get("LIGHT_LEAN", "$LIGHT_LEAN"),
                        "verify/challenge/lake-manifest.json")
REQ = ('[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\n'
       'rev = "0df444a360eaa60ab8c11dca51a86af692955474"\n')
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def manifest(name):
    m = json.load(open(MANIFEST))
    m["name"] = name
    return json.dumps(m, indent=1) + "\n"


def thm(name, stmt, proof):
    return "theorem " + name + " : " + stmt + " :=\n  " + proof.replace("\n", "\n  ") + "\n"


def write_project(d, pkg, lib, files, default):
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, "lean-toolchain"), "w").write(TOOLCHAIN)
    open(os.path.join(d, "lakefile.toml"), "w").write(
        f'name = "{pkg}"\ndefaultTargets = ["{default}"]\n\n{REQ}\n[[lean_lib]]\nname = "{lib}"\n')
    open(os.path.join(d, "lake-manifest.json"), "w").write(manifest(pkg))
    for rel, txt in files.items():
        p = os.path.join(d, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, "w").write(txt)


def pkgname(name):
    return "p" + "".join(c for c in name.lower() if c.isalnum())[:40]


# negative variants: (problem, kind, transform(stmt, proof) -> (prelude, stmt, proof), expected)
SORRY_MACRO = 'macro "solve_it" : tactic => `(tactic| sorry)\n\n'
NEG = [
    ("amc_rem_2pow100_mod7", "sorry", lambda s, q: ("", s, "by sorry")),
    ("ind_gauss", "sorry-in-have", lambda s, q: ("", s, q.replace("by\n", "by\n  have _h : (1 : ℕ) = 1 := sorry\n", 1))),
    ("ineq_amgm2", "macro-sorry", lambda s, q: (SORRY_MACRO, s, "by solve_it")),
    ("nt_prime_1009", "axiom", lambda s, q: ("axiom cheat : " + s + "\n\n", s, "cheat")),
    ("nt_fib_20", "native_decide", lambda s, q: ("", s, "by native_decide")),
    ("dec_zmod", "native_decide", lambda s, q: ("", s, "by native_decide")),
    ("lia_chicken", "weaker-stmt", lambda s, q: ("", "∀ c r : ℕ, c + r = 35 → 2 * c + 4 * r = 94 → c = 23", "by intro c r h1 h2; omega")),
    ("an_pi_gt3", "changed-const", lambda s, q: ("", "3 < Real.pi + 1", "by linarith [Real.pi_gt_three]")),
    ("alg_solve_linear", "local-notation", lambda s, q: ("local notation \"twentytwo\" => (22 : ℝ)\n\n",
                                                          s.replace("22", "twentytwo"), q)),
    ("arith_frac", "sorryAx-direct", lambda s, q: ("", s, "sorryAx _ false")),
    ("rfl_nat_mul", "skipKernelTC-illtyped", None),   # special: ill-typed declaration added with debug.skipKernelTC
    ("nt_sqrt2_irr", "unsafe-cast", None),            # special: proof via unsafeCast through implemented_by-free route
    ("lia_system", "warn-sorry-off", lambda s, q: ("set_option warn.sorry false\n\n", s, "by sorry")),
    ("lia_two_consec", "local-instance", lambda s, q: ("local instance (priority := high) bogusMod : Mod ℕ := ⟨fun _ _ => 0⟩\n\n",
                                                        s, "by intro n; exact Or.inl rfl")),
    ("lia_mod_comb", "axiom-via-run_cmd", None),      # special: the theorem itself added as an axiom by meta code
]

SKIPKTC = '''theorem aux_stmt_holder : (12345 : ℕ) * 6789 = 83810205 := rfl

open Lean in
set_option debug.skipKernelTC true in
run_cmd Lean.Elab.Command.liftCoreM do
  let some ci := (← getEnv).find? `aux_stmt_holder | throwError "no aux"
  addDecl (.thmDecl { name := `rfl_nat_mul, levelParams := [], type := ci.type,
                      value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 7) })
'''


def main():
    out = sys.argv[1]
    only = None   # gen.py OUTDIR [--names a,b,c]: restrict the corpus (problems, their variants, BATCH) to these problems
    if len(sys.argv) > 3 and sys.argv[2] == "--names":
        only = set(sys.argv[3].split(","))
        M.P[:] = [q for q in M.P if q["name"] in only]
        NEG[:] = [x for x in NEG if x[0] in only]
    if len(sys.argv) > 3 and sys.argv[2] == "--replicate":   # K copies of every problem (names <name>__rK) for big batches
        k = int(sys.argv[3])
        M.P[:] = M.P + [dict(q, name=f"{q['name']}__r{i}") for i in range(1, k) for q in list(M.P)]
    if os.path.exists(out):
        shutil.rmtree(out)
    cases = {}
    byname = {q["name"]: q for q in M.P}
    for q in M.P:
        n = q["name"]
        cfg = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": [n],
               "definition_names": [], "permitted_axioms": AXIOMS}
        write_project(os.path.join(out, "challenges", n), pkgname(n) + "chal", "Challenge",
                      {"Challenge.lean": M.PREAMBLE + "\n" + thm(n, q["stmt"], "sorry"),
                       "comparator.json": json.dumps(cfg, indent=1) + "\n"}, "Challenge")
        write_project(os.path.join(out, "projects", n), pkgname(n), "Solution",
                      {"Solution.lean": M.PREAMBLE + "\n" + thm(n, q["stmt"], q["proof"])}, "Solution")
        cases[n] = {"challenge": n, "expected_official": "ACCEPTED", "style": q["style"], "kind": "positive"}
    for n, kind, f, *_ in NEG:
        q = byname[n]
        if kind == "skipKernelTC-illtyped":
            body = M.PREAMBLE + "\n" + SKIPKTC
        elif kind == "axiom-via-run_cmd":
            body = (M.PREAMBLE + "\ntheorem aux_holder : " + q["stmt"] + " :=\n  " + q["proof"].replace("\n", "\n  ") + "\n\n"
                    "open Lean in\nrun_cmd Lean.Elab.Command.liftCoreM do\n"
                    "  let some ci := (← getEnv).find? `aux_holder | throwError \"no aux\"\n"
                    "  addDecl (.axiomDecl { name := `" + n + ", levelParams := [], type := ci.type, isUnsafe := false })\n")
        elif kind == "unsafe-cast":
            body = (M.PREAMBLE + "\nunsafe def cheatU : " + q["stmt"] + " := unsafeCast ()\n\n"
                    "@[implemented_by cheatU] def cheatI : " + q["stmt"] + " := " + q["proof"] + "\n\n"
                    + thm(n, q["stmt"], "cheatI"))
            kind = "implemented_by"
        else:
            pre, s, pr = f(q["stmt"], q["proof"])
            body = M.PREAMBLE + "\n" + pre + thm(n, s, pr)
        c = n + "--" + kind
        write_project(os.path.join(out, "projects", c), pkgname(c), "Solution", {"Solution.lean": body}, "Solution")
        exp = "ACCEPTED" if kind in ("local-notation", "implemented_by") else "REJECTED"
        cases[c] = {"challenge": n, "expected_official": exp, "style": q["style"], "kind": kind}
    # one batch project: one module per problem; one challenge with every statement
    names = [q["name"] for q in M.P]
    files = {"Solution.lean": "".join(f"import Solution.{n}\n" for n in names)}
    for q in M.P:
        files[f"Solution/{q['name']}.lean"] = M.PREAMBLE + "\n" + thm(q["name"], q["stmt"], q["proof"])
    write_project(os.path.join(out, "projects", "BATCH"), "pbatch", "Solution", files, "Solution")
    cfg = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": names,
           "definition_names": [], "permitted_axioms": AXIOMS}
    write_project(os.path.join(out, "challenges", "BATCH"), "pbatchchal", "Challenge",
                  {"Challenge.lean": M.PREAMBLE + "\n" + "\n".join(thm(q["name"], q["stmt"], "sorry") for q in M.P),
                   "comparator.json": json.dumps(cfg, indent=1) + "\n"}, "Challenge")
    cases["BATCH"] = {"challenge": "BATCH", "expected_official": "ACCEPTED", "style": "batch", "kind": "positive"}
    json.dump(cases, open(os.path.join(out, "cases.json"), "w"), indent=1)
    print(len(cases), "cases")


if __name__ == "__main__":
    main()

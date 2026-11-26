#!/usr/bin/python3 -I
"""gen.py OUTROOT CASE [CASE ...]   -- synthetic projects of controlled SHAPE for the generality model.

CASE = BASE-SHAPE-N-CONTENT[-sSEED], e.g. core-wide-1024-tiny, mathlib-deep-64-tactic, core-layered-16x64-kernel
  BASE    core     no dependencies (only Lean core)
          mathlib  every module imports the trusted, cached Mathlib 0df444a (`require mathlib`, `import Mathlib`)
  SHAPE   wide     N independent modules M0..M(N-1); the root `Solution` imports all of them
          deep     a chain: M(i) imports M(i-1); `Solution` imports M(N-1)
          layered  LxW: W modules per layer, each imports min(4, W) random modules of the previous layer (seeded);
                   `Solution` imports the last layer
          N for layered is written LxW (e.g. 16x64)
  CONTENT tiny     1 def + 1 `rfl` lemma + the witness (fixed cost dominated)
          tactic   8 lemmas proved by tactics (core: omega/simp/decide on small goals; mathlib: ring/norm_num/linarith/
                   positivity/omega) + the witness
          kernel   1 lemma proved by `decide +kernel` on a moderate computation (kernel reduction in the build AND in the check)
          many     40 defs + 40 `rfl`/`simp` lemmas (export size / number of declarations)
          inductive  an enumeration with 64 constructors, a pattern-matching function, `cases <;> decide`
          typeclass  a chain of 12 `extends` classes, one instance, `rfl` theorems through instance search/projections
          universe   universe-polymorphic definitions with 6 level parameters, nested ULift/PLift
          automation core: `grind`; mathlib: `aesop`, `tauto`, `simp_all`, `omega`
          enumK / deepK / univK / litK  extreme sizes: K constructors, a proof term nested K deep, K universe
                     parameters, a K-digit Nat literal (edge cases for exporter, parsers and kernels)
          private    the same `private def helper` / `private theorem aux` names in every module (merge stress)
          CONTENTxK  K copies of the block in one module (layout experiments: same total work, different module count)
Every module M(i) defines `Shp.M<i>.w : True`, a proof that references the module's own lemmas and the witnesses of the
modules it imports, so the export closure of the single target `Shp.main : True` (in `Solution`) contains every module.
`main` aggregates the imported witnesses in a tree of fan-in 64 (no deep terms).
Negative variants: suffix `-sorryK` (module K's first proof is `sorry`), `-kfalseK` (module K adds a false
`decide +kernel` theorem referenced by its witness); both are REJECTED officially.
The challenge (OUTROOT/challenge) is shared by every case: `theorem Shp.main : True := sorry`, core only.
"""
import json, os, random, re, shutil, sys

LL = os.environ.get("LIGHT_LEAN", "$LIGHT_LEAN")
WS = os.environ.get("PACKAGES_WS", f"{LL}/verify/challenge")
TOOLCHAIN = "leanprover/lean4:v4.33.1\n"
MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
FANIN = 64


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def content(base, kind, i):
    """declarations of module i (namespace Shp.M<i>) and the names of the lemmas the witness must reference"""
    ns = f"Shp.M{i}"
    if kind == "tiny":
        return (f"def {ns}.d : Nat := {i}\n\ntheorem {ns}.l : {ns}.d = {i} := rfl\n", [f"{ns}.l"])
    if kind == "tactic":
        a, b = i % 7 + 1, i % 11 + 2
        if base == "core":
            ls = [
                f"theorem {ns}.t0 (x y : Nat) (h : x ≤ y) : x + {a} ≤ y + {a} := by omega",
                f"theorem {ns}.t1 (x y : Nat) : (x + y) * {b} = x * {b} + y * {b} := by simp [Nat.add_mul]",
                f"theorem {ns}.t2 (x : Nat) (h : {a} < x) : {a} * 2 < x + x := by omega",
                f"theorem {ns}.t3 (l : List Nat) : (l ++ [{i}]).length = l.length + 1 := by simp",
                f"theorem {ns}.t4 : ({i} : Nat) % {b} = {i % b} := by decide",
                f"theorem {ns}.t5 (x y z : Nat) (h1 : x < y) (h2 : y < z) : x + {a} < z + {a} := by omega",
                f"theorem {ns}.t6 (p q : Prop) (hp : p) (hq : q) : q ∧ p ∧ True := by simp [hp, hq]",
                f"theorem {ns}.t7 (x : Nat) : x * {a} + x * {b} = x * {a + b} := by omega",
            ]
        else:
            ls = [
                f"theorem {ns}.t0 (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring",
                f"theorem {ns}.t1 : ({i} : ℚ) * {a} / {a} = {i} := by norm_num",
                f"theorem {ns}.t2 (x y : ℝ) (h1 : x ≤ y) (h2 : 0 ≤ x) : x ≤ 2 * y + {a} := by linarith",
                f"theorem {ns}.t3 (x : ℝ) : 0 ≤ x ^ 2 + {b} := by positivity",
                f"theorem {ns}.t4 (x y : ℕ) (h : x ≤ y) : x + {a} ≤ y + {a} := by omega",
                f"theorem {ns}.t5 (x : ℤ) : (x - {a}) * (x + {a}) = x ^ 2 - {a * a} := by ring",
                f"theorem {ns}.t6 : Nat.gcd {a * b * 6} {b * 4} = {__import__('math').gcd(a * b * 6, b * 4)} := by norm_num",
                f"theorem {ns}.t7 (s : Finset ℕ) : s.card ≤ (insert {i} s).card := Finset.card_le_card (Finset.subset_insert _ _)",
            ]
        return ("\n\n".join(ls) + "\n", [f"{ns}.t{j}" for j in range(8)])
    if kind == "kernel":
        # `decide +kernel`: the kernel evaluates the Decidable instance (~1-1.5 s of kernel reduction per module on an
        # Intel host; plain `decide` hits the elaborator's maxRecDepth at these sizes)
        n = 20000 + 100 * (i % 50)
        return (f"theorem {ns}.k : (List.range {n}).foldl (· + ·) 0 = {n * (n - 1) // 2} := by decide +kernel\n",
                [f"{ns}.k"])
    if kind == "many":
        out, refs = [], []
        for j in range(40):
            out.append(f"def {ns}.f{j} (x : Nat) : Nat := x * {j + 1} + {i}")
            out.append(f"theorem {ns}.e{j} (x : Nat) : {ns}.f{j} x = x * {j + 1} + {i} := rfl")
            refs.append(f"{ns}.e{j}")
        return ("\n".join(out) + "\n", refs)
    if kind == "inductive":
        # one enumeration with 64 constructors, a function by pattern matching, a theorem by `cases <;> decide`
        # (large casesOn/recursor terms for the kernel; 64 goals for the elaborator)
        k = 64
        ctors = "\n".join(f"  | c{j}" for j in range(k))
        arms = "\n".join(f"  | .c{j} => {(j * 7 + i) % 100}" for j in range(k))
        return (f"inductive {ns}.T where\n{ctors}\n\ndef {ns}.f : {ns}.T → Nat\n{arms}\n\n"
                f"theorem {ns}.k (t : {ns}.T) : {ns}.f t < 100 := by\n  cases t <;> decide\n", [f"{ns}.k"])
    if kind == "typeclass":
        # a chain of 12 classes (each `extends` the previous), one instance, theorems that need instance search
        # through the whole chain and projections of the parent structures
        k = 12
        out = [f"class {ns}.C0 (α : Type) where\n  v0 : Nat"]
        for j in range(1, k):
            out.append(f"class {ns}.C{j} (α : Type) extends {ns}.C{j - 1} α where\n  v{j} : Nat")
        fields = ", ".join(f"v{j} := {j + i}" for j in range(k))
        out.append(f"instance {ns}.inst : {ns}.C{k - 1} Nat := {{ {fields} }}")
        out.append(f"def {ns}.get0 (α : Type) [{ns}.C0 α] : Nat := {ns}.C0.v0 α")
        out.append(f"theorem {ns}.t0 : {ns}.get0 Nat = {i} := rfl")
        out.append(f"theorem {ns}.t1 : {ns}.C{k // 2}.v{k // 2} Nat + {ns}.C0.v0 Nat = {k // 2 + 2 * i} := rfl")
        return ("\n\n".join(out) + "\n", [f"{ns}.t0", f"{ns}.t1"])
    if kind == "universe":
        # universe-polymorphic definitions with many level parameters and nested ULift/PLift (level max/imax terms)
        out = [f"universe u1 u2 u3 u4 u5 u6",
               f"def {ns}.W (α : Sort u1) (β : Sort u2) (γ : Sort u3) (δ : Sort u4) : Type (max u1 u2 u3 u4) :=\n"
               f"  PProd (PLift α) (PProd (PLift β) (PProd (PLift γ) (PLift δ)))",
               f"def {ns}.U (α : Type u5) : Type (max u5 u6) := ULift.{{u6}} α",
               f"def {ns}.mk {{α : Sort u1}} {{β : Sort u2}} {{γ : Sort u3}} {{δ : Sort u4}} (a : α) (b : β) (c : γ) (d : δ) :\n"
               f"    {ns}.W α β γ δ := ⟨⟨a⟩, ⟨⟨b⟩, ⟨⟨c⟩, ⟨d⟩⟩⟩⟩",
               f"theorem {ns}.t0 {{α : Sort u1}} {{β : Sort u2}} {{γ : Sort u3}} {{δ : Sort u4}} (a : α) (b : β) (c : γ) (d : δ) :\n"
               f"    ({ns}.mk a b c d).1.down = a := rfl",
               f"theorem {ns}.t1 (x : Nat) : (ULift.down (({{ down := x }} : {ns}.U.{{0, 2}} Nat))) = x := rfl"]
        return ("\n\n".join(out) + "\n", [f"{ns}.t0.{{0,0,0,0}}", f"{ns}.t1"])
    m = re.match(r"(enum|deep|univ|lit)(\d+)$", kind)
    if m:   # extreme-size edge cases (differential at the limits of exporter / parsers / kernels)
        k0, K = m.group(1), int(m.group(2))
        if k0 == "enum":     # an enumeration with K constructors, a K-arm match, a theorem by cases
            ctors = "\n".join(f"  | c{j}" for j in range(K))
            arms = "\n".join(f"  | .c{j} => {j % 97}" for j in range(K))
            return (f"inductive {ns}.E where\n{ctors}\n\ndef {ns}.f : {ns}.E → Nat\n{arms}\n\n"
                    f"theorem {ns}.k (e : {ns}.E) : {ns}.f e < 97 := by\n  cases e <;> decide\n", [f"{ns}.k"])
        if k0 == "deep":     # a proof term nested K deep (kernel / exporter / parser recursion)
            return (f"set_option maxRecDepth 100000 in\ntheorem {ns}.d : True :=\n  " + "id (" * K + "trivial" + ")" * K + "\n",
                    [f"{ns}.d"])
        if k0 == "univ":     # K universe parameters
            us = " ".join(f"u{j}" for j in range(K))
            args = " ".join(f"(a{j} : Sort u{j})" for j in range(K))
            lv = ",".join("0" for _ in range(K))
            return (f"universe {us}\n\ndef {ns}.U {args} : Sort u0 := a0\n\n"
                    f"theorem {ns}.u : {ns}.U.{{{lv}}} " + " ".join("True" for _ in range(K)) + " := trivial\n",
                    [f"{ns}.u"])
        if k0 == "lit":      # a Nat literal with K decimal digits (GMP in the kernels, big numbers in the export)
            n = "9" * K   # as text (Python's int<->str conversion is limited to 4,300 digits)
            return (f"theorem {ns}.n : ({n} : Nat) % 9 = 0 := by decide\n", [f"{ns}.n"])
    if kind == "private":
        # the SAME private names in every module (typical of generated code: `private def helper`, `private theorem aux`);
        # distinct per module officially (private names are qualified by the module), they meet when modules are merged
        return (f"private def helper : Nat := {i}\n\nprivate theorem aux : helper = {i} := rfl\n\n"
                f"theorem {ns}.l : {i} + 0 = {i} := by simp\n\ntheorem {ns}.p : True := (fun (_ : type_of% @aux) => trivial) aux\n",
                [f"{ns}.l", f"{ns}.p"])
    if kind == "automation":
        # proof automation: core `grind`; Mathlib `aesop`, `simp_all`, `tauto`
        a = i % 5 + 1
        if base == "core":
            ls = [f"theorem {ns}.g0 (x y : Nat) (h : x = y + {a}) : y < x := by grind",
                  f"theorem {ns}.g1 (xs : List Nat) (h : xs ≠ []) : 0 < xs.length := by grind [List.length_pos_iff]",
                  f"theorem {ns}.g2 (p q r : Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by grind",
                  f"theorem {ns}.g3 (x : Nat) (f : Nat → Nat) (h : ∀ n, f n = n + {a}) : f (f x) = x + {2 * a} := by grind"]
        else:
            ls = [f"theorem {ns}.g0 (s t : Set ℕ) (h : s ⊆ t) (x : ℕ) (hx : x ∈ s) : x ∈ t ∪ {{{a}}} := by aesop",
                  f"theorem {ns}.g1 (p q r : Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r ∧ p := by tauto",
                  f"theorem {ns}.g2 (l : List ℕ) (h : ∀ x ∈ l, x < {a}) (y : ℕ) (hy : y ∈ l) : y < {a + 1} := by\n"
                  f"  have := h y hy; omega",
                  f"theorem {ns}.g3 (f : ℕ → ℕ) (hf : ∀ n, f n = n) (x : ℕ) : f (f x) = x := by simp_all"]
        return ("\n\n".join(ls) + "\n", [f"{ns}.g{j}" for j in range(4)])
    raise SystemExit(f"unknown content {kind}")


def content_rep(base, kind, i):
    """CONTENT or CONTENTxK: K copies of the content block in one module (distinct names: namespace Shp.M<i>.b<k>),
    for layout experiments (the same total work as many small modules or few big ones)"""
    if "x" not in kind:
        return content(base, kind, i)
    k0, reps = kind.rsplit("x", 1)
    bodies, refs = [], []
    for k in range(int(reps)):
        b, r = content(base, k0, i * 100000 + k)   # unique index per block -> unique names and constants
        bodies.append(b); refs += r
    return "\n".join(bodies), refs


def witness(name, refs):
    """theorem name : True referencing every proof in refs (refs are theorem names; their statements are Props)"""
    if not refs:
        return f"theorem {name} : True := trivial\n"
    binders = " ".join(f"(_ : type_of% @{r})" for r in refs)
    args = " ".join(f"@{r}" for r in refs)
    return f"theorem {name} : True := (fun {binders} => trivial) {args}\n"


def agg_tree(prefix, refs):
    """declarations aggregating refs (witnesses : True) in a tree of fan-in FANIN; returns (text, root name)"""
    text, level, cur = [], 0, list(refs)
    while len(cur) > FANIN:
        nxt = []
        for j in range(0, len(cur), FANIN):
            nm = f"{prefix}.agg{level}_{j // FANIN}"
            text.append(witness(nm, cur[j:j + FANIN]))
            nxt.append(nm)
        cur, level = nxt, level + 1
    return "\n".join(text), cur


def parse_case(case):
    """BASE-SHAPE-N-CONTENT[-sSEED][-sorryK][-kfalseK] (the last two: negative variants, see the docstring)"""
    parts = case.split("-")
    seed, neg = 0, {}
    while len(parts) > 4:
        x = parts.pop()
        for tag in ("sorry", "kfalse"):
            if x.startswith(tag) and x[len(tag):].isdigit():
                neg[tag] = int(x[len(tag):]); break
        else:
            if x.startswith("s") and x[1:].isdigit():
                seed = int(x[1:])
            else:
                raise SystemExit(f"bad case suffix {x}")
    base, shape, n, kind = parts
    return base, shape, n, kind, seed, neg


def gen_case(outroot, case):
    base, shape, n, kind, seed, neg = parse_case(case)
    rnd = random.Random(seed)
    d = os.path.join(outroot, case)
    if os.path.exists(d):
        shutil.rmtree(d)
    imports = {}          # module index -> list of imported module indices
    if shape == "wide":
        N = int(n)
        for i in range(N):
            imports[i] = []
        tops = list(range(N))
    elif shape == "deep":
        N = int(n)
        for i in range(N):
            imports[i] = [i - 1] if i else []
        tops = [N - 1]
    elif shape == "layered":
        L, W = (int(x) for x in n.split("x"))
        N = L * W
        for l in range(L):
            for w in range(W):
                i = l * W + w
                imports[i] = [] if l == 0 else sorted(rnd.sample(range((l - 1) * W, l * W), min(4, W)))
        tops = list(range((L - 1) * W, L * W))
    else:
        raise SystemExit(f"unknown shape {shape}")
    p = os.path.join(d, "project")
    base_import = "import Mathlib\n" if base == "mathlib" else ""
    depth = {}
    for i in range(N):
        depth[i] = 1 + max((depth[j] for j in imports[i]), default=0)
        body, refs = content_rep(base, kind, i)
        if neg.get("sorry") == i:      # negative variant: the module's first proof is `sorry` (officially REJECTED: sorryAx)
            for pf in (":= rfl", ":= by", ":= Finset"):
                if pf in body:
                    body = body.replace(pf, ":= sorry --", 1) if pf != ":= rfl" else body.replace(pf, ":= sorry", 1)
                    break
        if neg.get("kfalse") == i:     # negative variant: a FALSE `decide +kernel` claim in the closure (the official build
            # fails in the kernel; under skip-kernel-tc the untrusted build passes and the trusted check must reject)
            body += f"\ntheorem Shp.M{i}.kbad : (List.range 10).foldl (· + ·) 0 = 46 := by decide +kernel\n"
            refs = refs + [f"Shp.M{i}.kbad"]
        imps = base_import + "".join(f"import Shp.M{j}\n" for j in imports[i])
        wrefs = refs + [f"Shp.M{j}.w" for j in imports[i]]
        aggs_i, wroot = agg_tree(f"Shp.M{i}", wrefs)   # fan-in <= 64 per witness term (CONTENTxK modules)
        write(f"{p}/Shp/M{i}.lean", imps + "\n" + body + "\n" + aggs_i + "\n" + witness(f"Shp.M{i}.w", wroot))
    aggs, root = agg_tree("Shp.Root", [f"Shp.M{j}.w" for j in tops])
    write(f"{p}/Solution.lean", base_import + "".join(f"import Shp.M{j}\n" for j in tops) + "\n" + aggs + "\n" +
          witness("Shp.main", root))
    write(f"{p}/lean-toolchain", TOOLCHAIN)
    req = (f'\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\n'
           f'rev = "{MATHLIB_REV}"\n') if base == "mathlib" else ""
    write(f"{p}/lakefile.toml", f'name = "shp"\ndefaultTargets = ["Shp", "Solution"]\n{req}\n'
          f'[[lean_lib]]\nname = "Shp"\nglobs = ["Shp.+"]\n\n[[lean_lib]]\nname = "Solution"\n')
    if base == "mathlib":
        m = json.load(open(os.path.join(WS, "lake-manifest.json")))
        m["name"] = "shp"
        write(f"{p}/lake-manifest.json", json.dumps(m, indent=1) + "\n")
    info = {"case": case, "base": base, "shape": shape, "n": n, "content": kind, "seed": seed, "modules": N + 1,
            "depth": max(depth.values()) + 1, "edges": sum(len(v) for v in imports.values()) + len(tops)}
    write(f"{d}/case.json", json.dumps(info) + "\n")
    print(json.dumps(info))


def gen_challenge(outroot):
    c = os.path.join(outroot, "challenge")
    if os.path.exists(os.path.join(c, "Challenge.lean")):
        return
    write(f"{c}/Challenge.lean", "/-! Shared clean challenge of the synthetic shape benchmark. -/\n\n"
          "theorem Shp.main : True :=\n  sorry\n")
    write(f"{c}/lean-toolchain", TOOLCHAIN)
    write(f"{c}/lakefile.toml", 'name = "shpchallenge"\ndefaultTargets = ["Challenge"]\n\n[[lean_lib]]\nname = "Challenge"\n')
    write(f"{c}/comparator.json", json.dumps({
        "challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["Shp.main"],
        "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "external_kernels": {"nanoda": ["nanoda_bin"]}}, indent=1) + "\n")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    gen_challenge(sys.argv[1])
    for c in sys.argv[2:]:
        gen_case(sys.argv[1], c)

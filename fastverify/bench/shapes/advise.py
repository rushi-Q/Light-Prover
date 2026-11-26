#!/usr/bin/python3 -I
"""advise.py PROJECT [--threads P] [--closure-mb MB] [--json]  -- which verifier configuration fits this project's SHAPE.

Reads only the project's .lean sources (outside .lake; never builds or runs anything), computes the features that the
synthetic-shape benchmark showed to decide the speed-up:
modules N, longest import chain inside the project, modules importing a big external library (Mathlib), single-importer
chains (merge candidates), kernel-computation proofs (`decide +kernel`, `by decide` on literals is not counted),
`@[to_dual]` (skip-kernel-tc hazard, see bench/mathlib-as-project), lemmas per module - and prints which levers of `--preset sound`
apply and a recommendation (official flow vs sound preset, items to drop). Advice only: it never influences a verdict.
"""
import json, os, re, sys

IMPORT_SKIP = ("module", "prelude", "public", "meta", "all", "private")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|example)\b", re.M)


def header_imports(txt):
    """imports of the module header: line scan that stops at the first code line (fast on huge trees)"""
    out, depth = [], 0
    for line in txt.splitlines():
        t = line.strip()
        if depth:
            depth += t.count("/-") - t.count("-/")
            continue
        if not t or t.startswith("--"):
            continue
        if t.startswith("/-"):
            depth = t.count("/-") - t.count("-/")
            continue
        toks = t.split("--")[0].split()
        while toks and toks[0] in IMPORT_SKIP:
            toks = toks[1:]
        if toks and toks[0] == "import":
            toks = [x for x in toks[1:] if x not in ("all", "public", "meta")]
            out.extend(toks)
            continue
        if not toks:
            continue
        break
    return out


def scan(root):
    mods = {}
    for dp, dns, fns in os.walk(root):
        dns[:] = [d for d in dns if d not in (".lake", ".git", "lake-packages")]
        for fn in fns:
            if fn.endswith(".lean") and fn not in ("lakefile.lean",):
                p = os.path.join(dp, fn)
                name = os.path.relpath(p, root)[:-5].replace(os.sep, ".")
                try:
                    txt = open(p, encoding="utf-8", errors="replace").read()
                except OSError:
                    continue
                mods[name] = txt
    return mods


def main():
    a = sys.argv[1:]
    js = "--json" in a; a = [x for x in a if x != "--json"]
    P = 32
    if "--threads" in a:
        i = a.index("--threads"); P = int(a[i + 1]); del a[i:i + 2]
    cmb = None   # closure size of the challenge's targets in MB (e.g. the size of an earlier export), if known
    if "--closure-mb" in a:
        i = a.index("--closure-mb"); cmb = float(a[i + 1]); del a[i:i + 2]
    if len(a) != 1:
        sys.exit(__doc__)
    root = a[0]
    src = scan(root)
    # module names may be relative to a srcDir: match imports by suffix when needed
    names = set(src)
    imps = {m: header_imports(t) for m, t in src.items()}
    proj_imps = {m: [d for d in v if d in names] for m, v in imps.items()}
    ext = {m: [d for d in v if d not in names] for m, v in imps.items()}
    lib_importers = sum(1 for m, v in ext.items() if any(d == "Mathlib" or d.startswith("Mathlib.") for d in v))
    # the zygote PREFIX only serves a module whose import closure starts with exactly Mathlib's closure, i.e. whose
    # first import is `Mathlib` (RH style); selective imports (`import Mathlib.Foo`) miss it (measured: 100 % misses on PNT,
    # Carleson)
    prefix_importers = sum(1 for m, v in imps.items() if v and v[0] == "Mathlib")
    # longest chain (iterative DFS over the project DAG)
    depth = {}
    for m0 in src:
        stack = [(m0, False)]
        while stack:
            m, done = stack.pop()
            if m in depth:
                continue
            if done:
                depth[m] = 1 + max((depth.get(d, 0) for d in proj_imps[m]), default=0)
                continue
            stack.append((m, True))
            for d in proj_imps[m]:
                if d not in depth:
                    stack.append((d, False))
    importers = {m: 0 for m in src}
    for m, v in proj_imps.items():
        for d in v:
            importers[d] += 1
    single = sum(1 for m in src if importers[m] == 1)
    kernel = sum(len(re.findall(r"decide\s*\+kernel|decide\s*\(\s*kernel\s*:=\s*true\s*\)", t)) for t in src.values())
    to_dual = sum(len(re.findall(r"@\[[^\]]*\bto_dual\b", t)) for t in src.values())
    decls = sum(len(DECL.findall(t)) for t in src.values())
    modsys = sum(1 for t in src.values() if re.match(r"\s*(?:/-.*?-/\s*|--[^\n]*\n\s*)*module\b", t, re.S))
    N = len(src); D = max(depth.values(), default=0)
    f = {"modules": N, "longest_chain": D, "library_importers": lib_importers, "prefix_importers": prefix_importers, "single_importer_modules": single,
         "kernel_computation_markers": kernel, "to_dual_attributes": to_dual, "declarations": decls,
         "declarations_per_module": round(decls / N, 1) if N else 0, "module_system_files": modsys, "threads": P}
    levers, rec, drop = [], [], []
    if N == 0:
        print(json.dumps({"error": f"no .lean sources found under {root}"}) if js else f"no .lean sources found under {root}")
        return
    if N <= 100 and D <= 10 and kernel < 20:
        rec.append("SMALL project: the official flow is expected to be faster (the fast presets add 10-20 s of fixed cost "
                   "and no lever applies); use --preset sound only if a sound verdict without the official comparator is wanted")
    if lib_importers >= 1000 or (N >= 2000 and P >= 96):
        levers.append("B1-family scheduler: Lake's serial per-module bookkeeping avoided (measured 408 s -> 26 s for 1,025 "
                      "Mathlib importers)")
    if prefix_importers >= 100:
        levers.append(f"zygote (glibc >= 2.38 only): {prefix_importers} modules start with `import Mathlib`: "
                      "per-process library import ~3-4 s -> ~0.5 s")
    elif lib_importers > 0:
        why = (f"only {prefix_importers} modules start with `import Mathlib` (selective imports miss the prefix)"
               if lib_importers >= 100 else "< ~100 library importers")
        drop.append(f"zygote,zygote-prefix ({why}: the zygote start-up ~9 s is a net loss)")
    # (no library importer: the zygote never matches; measured harmless on the AMD server: 21.9 vs 22.1 s)
    if D >= 16 and single >= D // 2 and modsys > N // 2:
        rec.append(f"long chains ({D}) but {modsys} module-system files: merge leaves them unmerged, no merge gain")
    elif D >= 16 and single >= D // 2:
        levers.append(f"merge: import chain of {D} modules with {single} single-importer modules (chains collapse into "
                      "groups of <= 24 modules; measured 3-4x on chains of cheap modules)")
    if kernel >= 20:
        levers.append(f"parallel CS check + skip-kernel-tc: {kernel} kernel-computation markers (the official check replays "
                      "them single-threaded; measured 3-13x)")
    if f["declarations_per_module"] >= 20:
        levers.append("heavy modules: T1/PGO toolchain (-15..-25 % CPU) and linter-off (-25 % CPU on Mathlib-style code); "
                      "on a critical-path-bound build expect <= ~1.5x from these alone")
    if cmb is not None and cmb >= 80:
        levers.append(f"E1 + CS on a {cmb:.0f} MB closure: official export + check ~0.16 s/MB (AMD) to ~0.45 s/MB (Intel "
                      f"hosts) single-threaded vs ~0.01-0.03 s/MB -> ~{0.15 * cmb:.0f}-{0.42 * cmb:.0f} s saved; real "
                      "projects with 400-600 MB closures: 10-16x on export+check")
    elif cmb is None and lib_importers > 0:
        rec.append("closure-dependent: theorems over Mathlib often pull 100-600 MB into the closure; if an export of the "
                   "targets is >= ~80 MB the sound check alone wins (re-run with --closure-mb SIZE)")
    if to_dual:
        drop.append(f"skip-kernel-tc ({to_dual} @[to_dual] attributes: under skip-kernel-tc to_dual keeps ill-typed first "
                    "attempts -> build failure or a false REJECT; or run with --confirm-reject)")
    if N >= 4 * P and D <= 3 and lib_importers == 0 and P <= 64:
        rec.append(f"WIDE project of cheap modules at {P} threads: little to gain (measured 0.6-1.3x); more threads help "
                   "the fast presets (lake build does not scale past a few dozen threads)")
    if f["declarations_per_module"] and f["declarations_per_module"] < 3 and N > 100:
        rec.append("many near-empty modules: merging lemmas into fewer modules would cut the per-process cost")
    if levers and not any(r.startswith("SMALL") for r in rec):
        rec.insert(0, "use --preset sound" + (f" --unsafe <preset list minus: {'; '.join(d.split(' ')[0] for d in drop)}>"
                                              if drop else ""))
    out = {"features": f, "levers_that_apply": levers, "drop_items": drop, "recommendation": rec or
           ["no dominant lever: expect the official flow and --preset sound to be within ~30 % of each other"]}
    if js:
        print(json.dumps(out, indent=1))
    else:
        print("features:", json.dumps(f))
        for k in ("levers_that_apply", "drop_items", "recommendation"):
            print(f"{k}:")
            for x in out[k]:
                print("  -", x)


if __name__ == "__main__":
    main()

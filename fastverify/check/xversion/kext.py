#!/usr/bin/python3 -I
"""kext.py GITDIR TAG... -- for each release tag, extract the Lean kernel's BUILT-IN EXTENSION code (the parts whose
soundness depends on the meaning of the primitive constants: Nat literal <-> Nat.zero/Nat.succ, GMP-accelerated Nat
operations, string literal expansion, Quot, the list of persistent constant names) from src/kernel/{type_checker.cpp,
quot.cpp,quot.h,inductive.cpp(nat/string parts)} and print a digest per function + whether it equals v4.36.0's text
(whitespace-normalized; unsigned/size_t integer-type changes reported separately). Reads git objects only (gc.auto=0)."""
import hashlib, re, subprocess, sys
G = sys.argv[1]; TAGS = sys.argv[2:]
FUNCS = ["reduce_nat", "reduce_bin_nat_op", "reduce_bin_nat_pred", "reduce_pow", "reduce_shiftLeft", "reduce_native",
         "nat_lit_to_constructor", "string_lit_to_constructor", "is_nat_lit_ext", "get_nat_val", "nat_lit_ext",
         "whnf_fvar", "reduce_proj_core", "whnf_core", "is_def_eq_offset", "is_nat_zero", "is_nat_succ", "lazy_delta_reduction",
         "initialize_type_checker", "infer_lit", "is_def_eq_unit_like", "to_cnstr_when_K", "mk_nat_succ", "mk_nat_zero"]
def show(tag, path):
    import os
    if os.path.isdir(tag):   # an extracted source tree (e.g. a release tarball) instead of a git tag
        try:
            return open(os.path.join(tag, path)).read()
        except OSError:
            return ""
    r = subprocess.run(["git", "-c", "gc.auto=0", "-C", G, "show", f"{tag}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""
def funcs(src):
    out = {}
    lines = src.split("\n")
    i = 0
    while i < len(lines):
        ln = lines[i]
        m = re.match(r"^[A-Za-z].*?\b(type_checker::)?([a-z_A-Z0-9]+)\s*\(.*$", ln)
        if m and m.group(2) in FUNCS and not ln.rstrip().endswith(";"):
            j = i; depth = 0; started = False; body = []
            while j < len(lines):
                body.append(lines[j]); depth += lines[j].count("{") - lines[j].count("}")
                if "{" in lines[j]: started = True
                if started and depth <= 0: break
                j += 1
            out.setdefault(m.group(2), []).append("\n".join(body)); i = j + 1; continue
        i += 1
    return {k: "\n".join(v) for k, v in out.items()}
def norm(s, types=False):
    s = re.sub(r"\s+", " ", s)
    if types: s = re.sub(r"\b(unsigned int|unsigned|size_t)\b", "INT", s)
    return s
ref = {}
for p in ("src/kernel/type_checker.cpp", "src/kernel/quot.cpp", "src/kernel/quot.h"):
    ref[p] = show("v4.36.0", p)
reff = funcs(ref["src/kernel/type_checker.cpp"])
consts36 = sorted(set(re.findall(r'new_persistent_expr_const\((\{[^)]*\})\)', ref["src/kernel/type_checker.cpp"])))
for tag in TAGS:
    tc = show(tag, "src/kernel/type_checker.cpp")
    if not tc:
        print(f"{tag}: no source"); continue
    f = funcs(tc); res = []
    for k in sorted(set(f) | set(reff)):
        a, b = reff.get(k), f.get(k)
        if a is None: res.append(f"{k}:ONLY-IN-{tag}")
        elif b is None: res.append(f"{k}:missing")
        elif norm(a) == norm(b): continue
        elif norm(a, True) == norm(b, True): res.append(f"{k}:int-types-only")
        else: res.append(f"{k}:DIFFERS")
    consts = sorted(set(re.findall(r'new_persistent_expr_const\((\{[^)]*\})\)', tc)))
    q = ["quot.cpp" if norm(show(tag, "src/kernel/quot.cpp")) != norm(ref["src/kernel/quot.cpp"]) else "",
         "quot.h" if norm(show(tag, "src/kernel/quot.h")) != norm(ref["src/kernel/quot.h"]) else ""]
    print(f"{tag}: functions differing from v4.36.0: {', '.join(res) or 'none'}; constant names "
          f"{'= v4.36.0' if consts == consts36 else 'DIFFER: +' + str(sorted(set(consts)-set(consts36))) + ' -' + str(sorted(set(consts36)-set(consts)))}; "
          f"quot: {' '.join(x for x in q if x) or 'identical'}")

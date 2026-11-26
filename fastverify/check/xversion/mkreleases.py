#!/usr/bin/python3 -I
"""mkreleases.py GITDIR OUT.json [EXTRA_TREE=VERSION=GITHASH ...]

Builds the verified-release table of xvcheck.py from the Lean 4 SOURCES of every release tag v4.26.0-rc1 .. v4.36.0 in
GITDIR (read-only: `git -c gc.auto=0 show`) plus extracted source trees given as DIR=VERSION=GITHASH (e.g. a release
tarball of v4.37.0-rc1). A release is admitted iff ALL mechanical checks hold (else it is left out = no verdict):
  K1 the kernel's GMP-accelerated Nat operations (the `if (f == *g_nat_X)` dispatch of reduce_nat) are the same set as
     in v4.36.0;
  K2 the kernel's persistent constant names are v4.36.0's, plus at most Lean.reduceBool/Lean.reduceNat (the in-kernel
     native reduction that 4.35 removed: the 4.36 kernel cannot reduce them, so it can only reject more);
  K3 string literals unfold to String.ofList (g_string_mk) as in v4.36.0;
  K4 src/kernel/quot.cpp and quot.h equal v4.36.0's (whitespace and unsigned/size_t normalized; without the name checks
     that 4.33.0 added before Quot is created, #14632, which make 4.36 reject more);
  F  the release's lean4export writes format 3.1.0 (true for every lean4export tag from 4.15 on, A07's exports; the
     exporter is recorded, not built here).
Recorded per release (information): whether src/kernel equals 4.36.0's, the official comparator source status
(Lake/CLI/Check.lean + Lake/Check/*: identical to 4.36.0 / absent = external leanprover/comparator era / differs) and the
extra comparator rules xvcheck applies (4.37: challenge-definitions-sorried)."""
import hashlib, json, os, re, subprocess, sys

G = sys.argv[1]
OUTF = sys.argv[2]
EXTRA = [x.split("=") for x in sys.argv[3:]]
CMP_FILES = ["src/lake/Lake/CLI/Check.lean", "src/lake/Lake/Check/Compare.lean", "src/lake/Lake/Check/Axioms.lean",
             "src/lake/Lake/Check/Util.lean"]


def git(*a):
    r = subprocess.run(["git", "-c", "gc.auto=0", "-C", G] + list(a), capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def reader(src):
    if os.path.isdir(src):
        def show(p):
            try:
                return open(os.path.join(src, p)).read()
            except OSError:
                return None
        def kernel_digest():
            h = hashlib.sha256()
            d = os.path.join(src, "src/kernel")
            for fn in sorted(os.listdir(d)):
                h.update(fn.encode() + b"\0" + open(os.path.join(d, fn), "rb").read())
            return h.hexdigest()
        return show, kernel_digest
    def show(p):
        return git("show", f"{src}:{p}")
    def kernel_digest():
        return git("rev-parse", f"{src}:src/kernel").strip()
    return show, kernel_digest


def norm(s):
    s = re.sub(r"\s+", " ", s or "")
    return re.sub(r"\b(unsigned int|unsigned|size_t)\b", "INT", s)


def facts(src):
    show, kd = reader(src)
    tc = show("src/kernel/type_checker.cpp") or ""
    m = re.search(r"optional<expr> type_checker::reduce_nat\(expr const & e\) \{(.*?)\n\}", tc, re.S)
    accel = sorted(set(re.findall(r"f == \*g_nat_([A-Za-z]+)\)", m.group(1)))) if m else None
    consts = sorted(set(re.findall(r"new_persistent_expr_const\((\{[^)]*\})\)", tc)))
    sm = re.search(r"g_string_mk\s*=\s*new_persistent_expr_const\(\{\"String\", \"([A-Za-z]+)\"\}\)", tc)
    q = show("src/kernel/quot.cpp") or ""
    # the 4.33.0 hardening (#14632) added name checks before adding Quot (4.36 can only reject more): compared without it
    q = re.sub(r"\n\s*/\* The `add_core` calls below overwrite.*?ill typed\. \*/", "", q, flags=re.S)
    q = re.sub(r"\n\s*check_name\(\*quot_consts::g_quot[a-z_]*\);", "", q)
    quot = norm(q) + "|" + norm(show("src/kernel/quot.h"))
    cmpf = [show(p) for p in CMP_FILES]
    return {"accel": accel, "consts": consts, "string_lit": sm.group(1) if sm else None, "quot": quot,
            "kernel": kd(), "cmp": cmpf}


def prim_lists(check_lean):
    """the primitiveTargets / builtinTargets lists of Lake/CLI/Check.lean (names only)"""
    out = []
    for fn in ("primitiveTargets", "builtinTargets"):
        m = re.search(r"def " + fn + r" : M \(Array Lean.Name\) := do(.*?)\n\n", check_lean or "", re.S)
        out.append(sorted(re.findall(r"``([A-Za-z.]+)", m.group(1))) if m else None)
    return out


ref = facts("v4.36.0")
# judge code (Lake/Check/Compare.lean, Axioms.lean, Util.lean) whose verdict semantics were reviewed against 4.36.0
REVIEWED_JUDGE = {
    hashlib.sha256("\0".join(x or "" for x in ref["cmp"][1:]).encode()).hexdigest():
        ("judge code identical to 4.36.0's", []),
    "909558e95130a8e8783228ee2c85578c383c67cbf202077e7ca31c0a9a9d339e": ("judge code of 4.37.0-rc1: 4.36's + the rule 'Challenge definition is not sorried' (Compare.lean) + "
                 "an order-independent axiom report (Axioms.lean, messages only), reviewed by A04",
                 ["challenge-definitions-sorried"]),
}
NATIVE = {'{"Lean", "reduceBool"}', '{"Lean", "reduceNat"}'}
tags = [t for t in (git("tag") or "").split() if re.match(r"^v4\.(2[6-9]|3[0-6])\.\d+(-rc\d+)?$", t)]
key = lambda t: [int(x) for x in re.findall(r"\d+", t)] + ([999] if "-rc" not in t else [])
cands = [(t, t, (git("rev-list", "-n1", t) or "").strip()) for t in sorted(tags, key=key)]
cands += [(d, "v" + v.lstrip("v"), gh) for d, v, gh in EXTRA]
rel, rejected = {}, {}
for src, tag, gh in cands:
    f = facts(src)
    why = []
    if f["accel"] != ref["accel"]:
        why.append(f"K1 accelerated Nat ops {f['accel']} != {ref['accel']}")
    extra, missing = set(f["consts"]) - set(ref["consts"]), set(ref["consts"]) - set(f["consts"])
    if missing or (extra - NATIVE):
        why.append(f"K2 persistent constants +{sorted(extra)} -{sorted(missing)}")
    if f["string_lit"] != "ofList":
        why.append(f"K3 string literals unfold to String.{f['string_lit']}")
    if f["quot"] != ref["quot"]:
        why.append("K4 quot.cpp/quot.h differ")
    if why:
        rejected[tag[1:]] = why
        continue
    judge = hashlib.sha256("\0".join(x or "" for x in f["cmp"][1:]).encode()).hexdigest()
    if all(x is None for x in f["cmp"]):
        cmp_status = "no lake comparator in this release (external leanprover/comparator era); judge = the 4.36 judge code"
        rules = []
    elif judge in REVIEWED_JUDGE and prim_lists(f["cmp"][0]) == prim_lists(ref["cmp"][0]):
        rules = REVIEWED_JUDGE[judge][1]
        cmp_status = REVIEWED_JUDGE[judge][0] + "; primitive/builtin target lists = 4.36.0's"
    else:
        rejected[tag[1:]] = [f"comparator judge sources (Lake/Check/*.lean sha256 {judge[:16]}) or primitive target list "
                             "not reviewed"]
        continue
    rel[tag[1:]] = {
        "githash": gh,
        "kernel": "src/kernel identical to 4.36.0" if f["kernel"] == ref["kernel"] else
                  ("extension checks K1-K4 hold; in-kernel native reduction present (absent in 4.36: rejects more)"
                   if set(f["consts"]) - set(ref["consts"]) else "extension checks K1-K4 hold; other kernel code differs"),
        "comparator": cmp_status,
        "rules": rules,
    }
table = {"schema": 1, "generated_by": "mkreleases.py (A04)", "reference": {"version": "4.36.0", "githash":
         dict((t[1:], g) for _, t, g in cands).get("4.36.0")}, "export_formats": ["3.1.0"],
         "checks": "K1 accelerated Nat ops = 4.36's; K2 persistent constants = 4.36's (+ native reduction); K3 string "
                   "literals -> String.ofList; K4 quot.cpp/h = 4.36's; see SOUNDNESS-XVERSION.md",
         "releases": rel, "not_admitted": rejected}
json.dump(table, open(OUTF, "w"), indent=1, sort_keys=True)
print(f"{len(rel)} releases admitted, {len(rejected)} not admitted -> {OUTF}")
for k, v in rejected.items():
    print("  not admitted", k, "; ".join(v))

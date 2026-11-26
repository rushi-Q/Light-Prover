#!/usr/bin/python3 -I
"""compare_official.py XVCHECK_PY EXPORT DUMP.jsonl : xvcheck.py's strict reader vs the OFFICIAL reader's view (DUMP made by
OfficialDump.lean with the official toolchain). Checks: (1) the same set of constants with the same kinds; (2) the same
`value.getLambdaBody.isAppOf sorryAx` verdict for every definition (the 4.37 rule, incl. mdata); (3) the official closure of
KERNEL_ROOTS under Lake.Check.runForUsedConsts (what the comparator follows from its primitives) is contained in
xvcheck's kernel closure, and for each constant in it the official runForUsedConsts is contained in xvcheck's dependency
set. Exit 0 iff all hold (or xvcheck refuses the export: stricter, gives no verdict)."""
import importlib.util, json, sys
if hasattr(sys, "set_int_max_str_digits"):   # r3: official dumps may hold > 4300-digit numbers
    sys.set_int_max_str_digits(0)
spec = importlib.util.spec_from_file_location("xvcheck_under_test", sys.argv[1])
X = importlib.util.module_from_spec(spec); spec.loader.exec_module(X)
try:
    m = X.read_export(sys.argv[2])
except X.ExportError as e:   # stricter than the official reader: the gate gives no verdict (DECLINED) - never unsound
    print("XVCHECK-REFUSES-ONLY %s (%s)" % (sys.argv[2], e))
    sys.exit(0)


def tup(comps):
    return tuple(("s", c) if isinstance(c, str) else ("n", c) for c in comps)


def deps(c):
    kind, es, refs = m.decls[c]
    out = set(refs) | {c}
    if kind == "quot" and m.lookup((("s", "Eq"),)) is not None:
        out.add(m.lookup((("s", "Eq"),)))
    seen, st = set(), list(es)
    while st:
        e = st.pop()
        if e in seen:
            continue
        seen.add(e)
        k = m.ek[e]
        if k == X.E_CONST:
            out.add(m.ea[e])
        elif k in (X.E_APP, X.E_LAM, X.E_FORALL):
            st += [m.ea[e], m.eb[e]]
        elif k == X.E_LET:
            st += [m.ea[e], m.eb[e], m.ec[e]]
        elif k == X.E_PROJ:
            st.append(m.ea[e]); out.add(m.eb[e])
        elif k == X.E_MDATA:
            st.append(m.ea[e])
    return out


errs = []
off = {}
nsorried = 0
for l in open(sys.argv[3], encoding="utf-8"):
    o = json.loads(l)
    t = tup(o["name"]); off[t] = o
    c = m.lookup(t)
    if c is None or c not in m.decls:
        errs.append("missing in xvcheck: %r" % (t,)); continue
    if m.decls[c][0] != o["kind"]:
        errs.append("kind %r: official %s xvcheck %s" % (t, o["kind"], m.decls[c][0]))
    if o["kind"] == "def":
        py_sorried = not m.def_not_sorried(t)
        nsorried += py_sorried
        if py_sorried != o["sorried"]:
            errs.append("sorried %r: official %s xvcheck %s" % (t, o["sorried"], py_sorried))
if len(m.decls) != len(off):
    errs.append("constant count: official %d xvcheck %d" % (len(off), len(m.decls)))
# (3) official closure of the roots (runForUsedConsts) vs xvcheck's kernel closure
clo, st = set(), [X.parse_lean_name(r) for r in X.KERNEL_ROOTS]
while st:
    t = st.pop()
    if t in clo:
        continue
    clo.add(t)
    if t in off:
        st.extend(tup(u) for u in off[t]["used"])
hits, nclos = m.kernel_closure_holes([(t, t) for t in clo], X.KERNEL_ROOTS)
py_clo = set(h for h, _ in hits)
missing = [t for t in clo if m.lookup(t) is not None and t not in py_clo]
if missing:
    errs.append("official closure not contained in xvcheck's: %d names, e.g. %r" % (len(missing), missing[:3]))
for t in clo:
    if t in off:
        c = m.lookup(t)
        used = set(m.lookup(tup(u)) for u in off[t]["used"])
        if None in used or not used <= deps(c):
            errs.append("deps of %r: official runForUsedConsts not contained" % (t,))
print(("AGREE" if not errs else "DISAGREE") + " %s constants=%d sorried_defs=%d kernel_closure official=%d xvcheck=%d" % (
    sys.argv[2], len(off), nsorried, len([t for t in clo if t in off]), nclos))
for e in errs[:20]:
    print("  " + e)
sys.exit(1 if errs else 0)

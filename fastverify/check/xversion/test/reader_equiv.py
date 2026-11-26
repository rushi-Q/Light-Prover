#!/usr/bin/python3 -I
"""reader_equiv.py XVCHECK_PY EXPORT... : the strict reader of xvcheck.py gives IDENTICAL tables with the canonical byte
templates (fast path) and with every line parsed as JSON (fast=False), or refuses the export on both paths; exit 0 iff
this holds for every export (standing test)."""
import importlib.util, sys
spec = importlib.util.spec_from_file_location("xvcheck_under_test", sys.argv[1])
X = importlib.util.module_from_spec(spec); spec.loader.exec_module(X)


def tables(m):
    return (m.intern, m.cid_pre, m.cid_comp, m.nidx, m.nlevels, m.ek, m.ea, m.eb, m.ec, m.decls)


def read(p, fast):
    try:
        return tables(X.read_export(p, fast=fast)), None
    except X.ExportError as e:
        return None, str(e)


bad = 0
for p in sys.argv[2:]:
    a, ea = read(p, True)
    b, eb = read(p, False)
    if a is None and b is None:
        print("REFUSED-ALIKE %s (%s)" % (p, ea))
    elif a is not None and a == b:
        print("SAME %s names=%d exprs=%d constants=%d" % (p, len(a[3]), len(a[5]), len(a[9])))
    else:
        print("DIFFERENT %s (fast: %s, json: %s)" % (p, ea or "read", eb or "read"))
        bad += 1
sys.exit(1 if bad else 0)

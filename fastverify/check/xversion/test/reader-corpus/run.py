#!/usr/bin/python3 -I
"""reader-corpus/run.py XVCHECK_PY : standing rows for the reader-exactness corpus in reader-corpus/ and its boundary cases.
OFFICIAL.jsonl holds, per input, the answer of the OFFICIAL reader (LeanExport.parseStream) of Lean v4.36.0 and
v4.37.0-rc1 (identical on every input): the declaration projection [[name components], kind, sorried], or a parse error, or
an abort (lean_internal_panic). EXPECT.tsv holds xvcheck's expected outcome: reader SAME (both reader paths return exactly
the official projection) or REFUSE (ExportError on both paths), and the gate's verdict with config.json (one definition
hole, so the body is read). A row FAILS if xvcheck deviates from EXPECT, and - independently of EXPECT - if xvcheck
returns a projection different from the official one, or reads an input the official reader refuses (the contract:
the official answer, or a refusal). many-lines.ndjson (68 MB) is regenerated from its recipe and sha-checked.
Prints PASS/FAIL rows and RESULT; exit 0 iff no FAIL."""
import hashlib, importlib.util, json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
XVP = os.path.abspath(sys.argv[1])
spec = importlib.util.spec_from_file_location("xvcheck_under_test", XVP)
X = importlib.util.module_from_spec(spec); spec.loader.exec_module(X)
PKG = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))


def view(path, fast):
    try:
        m = X.read_export(path, fast=fast)
    except X.ExportError as e:
        return None, str(e)
    decls = []
    for cid, (kind, _, _) in m.decls.items():
        parts = []
        c = cid
        while c:
            parts.append(m.cid_comp[c]); c = m.cid_pre[c]
        parts.reverse()
        key = tuple(("s" if isinstance(x, str) else "n", x) for x in parts)
        decls.append([parts, kind, kind == "def" and not m.def_not_sorried(key)])
    return decls, None


def many_lines(dst):
    with open(os.path.join(HERE, "digits-v4.36.0.ndjson"), "rb") as f:
        meta = f.readline().rstrip(b"\n")
    body = [b'{"in":1,"str":{"pre":0,"str":"A"}}', b'{"ie":0,"sort":0}',
            b'{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}']
    with open(dst, "wb") as f:
        f.write(b"\n".join([meta, *body]) + b"\n")
        for i in range(1, 65537):
            f.write(json.dumps({"ie": i, "strVal": "%05d" % i + "a" * 1019}, separators=(",", ":")).encode() + b"\n")


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


# the official projections hold numbers with up to 20001 digits: CPython's int(str) limit is lifted only while they are
# loaded, so the reader under test runs with the interpreter's default limit (it must handle such integers itself)
lim = sys.get_int_max_str_digits() if hasattr(sys, "get_int_max_str_digits") else None
if lim is not None:
    sys.set_int_max_str_digits(0)
official = {}
for ln in open(os.path.join(HERE, "OFFICIAL.jsonl"), encoding="utf-8"):
    r = json.loads(ln)
    official[r["file"]] = r
if lim is not None:
    sys.set_int_max_str_digits(lim)
expect = []
for ln in open(os.path.join(HERE, "EXPECT.tsv"), encoding="utf-8"):
    if ln.strip() and not ln.startswith("#"):
        f, reader, gate, note = (ln.rstrip("\n").split("\t") + [""])[:4]
        expect.append((f, reader, gate, note))
tmp = tempfile.mkdtemp(prefix="reader-corpus.")
fails = 0
def row(f, want_reader, want_gate):
    o = official[f]
    if f == "many-lines.ndjson":
        p = os.path.join(tmp, f); many_lines(p)
    elif f == "Challenge.export":
        p = os.path.join(PKG, "tests", "definition-hole", "x", "Challenge.export")
    else:
        p = os.path.join(HERE, f)
    why = []
    if sha(p) != o["sha256"]:
        why.append("input sha256 differs from the reviewed input")
    o36, o37 = o["v4.36.0"], o["v4.37.0-rc1"]
    if o36 != o37:
        why.append("official answers of the two releases differ (unexpected)")
    off_reads = "decls" in o36
    got = {fast: view(p, fast) for fast in (True, False)}
    reads = [got[k][0] is not None for k in (True, False)]
    if reads[0] != reads[1]:
        why.append("fast and JSON paths disagree")
    if reads[0]:
        if not off_reads:
            why.append("xvcheck reads an input the official reader refuses (%s)" % (o36.get("error") or o36.get("abort")))
        elif got[True][0] != o36["decls"] or got[False][0] != o36["decls"]:
            why.append("projection differs from the official one")
    got_reader = "SAME" if reads[0] else "REFUSE"
    if got_reader != want_reader:
        why.append("reader %s, expected %s (%s)" % (got_reader, want_reader, got[True][1] or ""))
    if want_gate != "-":
        q = subprocess.run(["/usr/bin/python3", "-I", XVP, p, os.path.join(HERE, "config.json")], capture_output=True, text=True)
        try:
            gv = json.loads(q.stdout.strip().splitlines()[-1])["verdict"]
        except Exception:
            gv = "NO-JSON"
        if gv != want_gate or q.returncode != {"OK": 0, "DECLINED": 2}.get(want_gate):
            why.append("gate %s rc=%d, expected %s" % (gv, q.returncode, want_gate))
    off = "reads" if off_reads else ("error: " + o36["error"] if "error" in o36 else "abort: " + o36["abort"])[:60]
    if why:
        print("FAIL reader-corpus/%s (official %s): %s" % (f, off, "; ".join(why)))
        return 1
    print("PASS reader-corpus/%s (official %s; xvcheck %s%s)" % (f, off, got_reader, ", gate " + want_gate if want_gate != "-" else ""))
    return 0


for f, want_reader, want_gate, note in expect:
    try:
        fails += row(f, want_reader, want_gate)
    except Exception as e:      # a missing input or a crash of the reader under test is a FAIL row, never a silent stop
        fails += 1
        print("FAIL reader-corpus/%s: %s: %s" % (f, type(e).__name__, str(e)[:160]))
try:
    os.unlink(os.path.join(tmp, "many-lines.ndjson"))
    os.rmdir(tmp)
except OSError:
    pass
print("RESULT reader-corpus rows=%d fail=%d" % (len(expect), fails))
sys.exit(1 if fails else 0)

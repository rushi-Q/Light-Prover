#!/usr/bin/python3 -I
"""mk_rh437_specs.py EXPORT OUTDIR [--targets NAME,..] [--m1 THM] [--m2 THM] [--m3 THM] [--m4 DEF THM]
The published RH mutant classes M1-M4 as fvmut edit specs for ANY
honest export (made for the 4.37 community RH export). Same edits as the originals:
  M1, M2  theorem value := its own type (a proof that is a type: ill-typed; two different theorems)
  M3      `axiom fakeAx : False` inserted in front of a theorem X whose value becomes @False.elim.{0} <X's type> fakeAx, every
          later name/expr index renumbered (fvmut's S directive)  -> illegal axiom + the kernel sees a new axiom
  M4      def D value := True, theorem T value := True.intro (well-typed on its own; T's statement mentions D) -> the comparator's
          statement/definition compare must catch it
Without --m1/--m2/--m3 the theorems are chosen by file position among canonical `thm` lines that are not targets: the FIRST
theorem, the LAST theorem, and the theorem at the middle of the file. --m4 needs the names (RH: RiemannZetaZerosOnLine
riemannZeta_eq_zero_re). Writes OUTDIR/{M1,M2,M3,M4}.spec + specs.json. Lines are checked to be canonical JSON first."""
import json, os, subprocess, sys
args = sys.argv[1:]
EXPORT, OUT = args[0], args[1]; os.makedirs(OUT, exist_ok=True)
def opt(k, n=1):
    if k in args:
        i = args.index(k); return args[i + 1] if n == 1 else args[i + 1:i + 1 + n]
    return None
targets = set((opt("--targets") or "").split(",")) - {""}
def canon(o): return json.dumps(o, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
def line_at(off):
    with open(EXPORT, "rb") as f:
        if off > 0: f.seek(off - 1); assert f.read(1) == b"\n", "offset is not a line start"
        else: f.seek(0)
        return f.readline().rstrip(b"\n").decode("utf-8")
def parsed(line):
    o = json.loads(line); assert canon(o) == line, "line is not canonical: " + line[:120]; return o
def grep_first(needle, limit_off=None):
    r = subprocess.run(["grep", "-F", "-b", "-m1", "--", needle, EXPORT], stdout=subprocess.PIPE, check=False)
    if r.returncode != 0: return None
    off, line = r.stdout.decode().rstrip("\n").split(":", 1); off = int(off)
    return None if (limit_off is not None and off >= limit_off) else (off, line)
# ---- ONE streaming pass over the export (RH scale: tens of GB): every name record (id -> dotted tuple) and every canonical
# `thm` line (offset, object). Names are emitted on first use anywhere in the file, so a full pass is needed anyway.
_NAMES = None; _THMS = None
def _scan():
    global _NAMES, _THMS
    if _NAMES is not None: return
    names = {0: ()}; thms = []; off = 0
    with open(EXPORT, "rb") as f:
        for raw in f:
            if raw.startswith(b'{"in":'):
                o = json.loads(raw)
                if "str" in o: names[o["in"]] = names.get(o["str"]["pre"], ("?",)) + (o["str"]["str"],)
                elif "num" in o: names[o["in"]] = names.get(o["num"]["pre"], ("?",)) + (str(o["num"]["i"]),)
            elif raw.startswith(b'{"thm":'):
                line = raw.rstrip(b"\n").decode(); o = json.loads(line)
                if canon(o) == line: thms.append((off, o))
            off += len(raw)
    _NAMES, _THMS = names, thms
    print(f"scan: {len(names)} names, {len(thms)} canonical theorem lines, {off} bytes", file=sys.stderr)
def scan_names(wanted):
    _scan(); inv = {}
    want = {tuple(w.split(".")): w for w in wanted}
    for nid, t in _NAMES.items():
        if t in want: inv[want[t]] = nid
    missing = set(wanted) - set(inv); assert not missing, f"names not found: {missing}"
    return inv
def name_of_id(nid):
    _scan(); return ".".join(_NAMES.get(nid, ("?",)))
def thm_lines():
    _scan(); return _THMS
def decl_line(name, kind):
    nid = scan_names([name])[name]
    hit = grep_first('{"%s":{' % kind) and None
    r = subprocess.run(["grep", "-F", "-b", "-m1", "--", '"name":%d,' % nid, EXPORT], stdout=subprocess.PIPE, check=False)
    for ln in r.stdout.decode().splitlines():
        off, line = ln.split(":", 1); o = json.loads(line)
        if kind in o and o[kind]["name"] == nid: return int(off), parsed(line)
    # the name may appear first in another record: scan all matches
    r = subprocess.run(["grep", "-F", "-b", "--", '"name":%d,' % nid, EXPORT], stdout=subprocess.PIPE, check=False)
    for ln in r.stdout.decode().splitlines():
        off, line = ln.split(":", 1); o = json.loads(line)
        if kind in o and o[kind]["name"] == nid: return int(off), parsed(line)
    raise SystemExit(f"{kind} {name} not found")
def last_record_ids(off, window=64 << 20):
    ln = le = None; end = off
    with open(EXPORT, "rb") as f:
        while (ln is None or le is None) and end > 0:
            start = max(0, end - window); f.seek(start); buf = f.read(end - start); lines = buf.split(b"\n")
            if start > 0: lines = lines[1:]
            for raw in reversed(lines):
                if not raw: continue
                if ln is None and raw.startswith(b'{"in":'): ln = json.loads(raw)["in"]
                if le is None and b'"ie":' in raw and not raw.startswith((b'{"in":', b'{"il":')):
                    o = json.loads(raw)
                    if "ie" in o: le = o["ie"]
                if ln is not None and le is not None: break
            end = start
    return ln, le
def write_spec(name, edits, shift=None, info=None):
    p = os.path.join(OUT, name + ".spec")
    with open(p, "w", encoding="utf-8") as f:
        f.write(f"# {name}: {info or ''}\n")
        for off, old, new in edits:
            f.write(f"E {off}\nO {old}\n"); [f.write(f"N {l}\n") for l in new]
        if shift: f.write("S %d %d %d %d\n" % shift)
    print("wrote", p, (info or "")[:120])
desc = {}
# choose M1/M2/M3 theorems
chosen = {}
m1, m2, m3 = opt("--m1"), opt("--m2"), opt("--m3")
if not (m1 and m2 and m3):
    tids = scan_names(sorted(targets)) if targets else {}
    tset = set(tids.values())
    rows = [(off, o) for off, o in thm_lines() if o["thm"]["name"] not in tset]
    assert len(rows) >= 3, "fewer than 3 non-target theorems"
    auto = {"M1": rows[0], "M2": rows[-1], "M3": rows[len(rows) // 2]}
for m, given in (("M1", m1), ("M2", m2), ("M3", m3)):
    if given: chosen[m] = decl_line(given, "thm") + (given,)
    else:
        off, o = auto[m]; chosen[m] = (off, o, name_of_id(o["thm"]["name"]))
# ---- M1 / M2
for m in ("M1", "M2"):
    off, o, nm = chosen[m]; old = canon(o); o2 = json.loads(old); o2["thm"]["value"] = o2["thm"]["type"]
    write_spec(m, [(off, old, [canon(o2)])], info=f"theorem {nm}: value {o['thm']['value']} -> {o['thm']['type']} (its own type)")
    desc[m] = dict(decl=nm, off=off)
ids = scan_names(["True", "True.intro", "False", "False.elim"])
assert grep_first('"str":"fakeAx"') is None, "a name component fakeAx already exists"
def const_expr(nameid, us, limit):
    hit = grep_first('{"const":{"name":%d,"us":[%s]},"ie":' % (nameid, ",".join(map(str, us))), limit)
    return None if hit is None else (json.loads(hit[1])["ie"], hit[0])
# ---- M3
off, ox, nm = chosen["M3"]; old = canon(ox)
last_name, last_expr = last_record_ids(off); K, M = last_name + 1, last_expr + 1
eFalse, _ = const_expr(ids["False"], [], off); fe = const_expr(ids["False.elim"], [0], off)
new = [canon({"in": K, "str": {"pre": 0, "str": "fakeAx"}}), canon({"axiom": {"isUnsafe": False, "levelParams": [], "name": K, "type": eFalse}}),
       canon({"const": {"name": K, "us": []}, "ie": M})]
nexpr = 1
if fe is None:
    eFE = M + nexpr; new.append(canon({"const": {"name": ids["False.elim"], "us": [0]}, "ie": eFE})); nexpr += 1
else: eFE = fe[0]
eApp1 = M + nexpr; new.append(canon({"app": {"arg": ox["thm"]["type"], "fn": eFE}, "ie": eApp1})); nexpr += 1
eApp2 = M + nexpr; new.append(canon({"app": {"arg": M, "fn": eApp1}, "ie": eApp2})); nexpr += 1
ox2 = json.loads(old); ox2["thm"]["value"] = eApp2; new.append(canon(ox2))
write_spec("M3", [(off, old, new)], shift=(K, 1, M, nexpr), info=f"axiom fakeAx : False (name {K}, expr {M}) before theorem {nm}; value -> @False.elim.{{0}} T fakeAx; names >= {K} +1, exprs >= {M} +{nexpr}")
desc["M3"] = dict(decl=nm, off=off, name_k=K, expr_k=M, expr_d=nexpr)
# ---- M4
m4 = opt("--m4", 2)
if m4:
    dn, tn = m4
    doff, do = decl_line(dn, "def"); toff, to = decl_line(tn, "thm")
    eTrue, _ = const_expr(ids["True"], [], doff); eIntro, _ = const_expr(ids["True.intro"], [], toff)
    assert eTrue is not None and eIntro is not None, "const True / True.intro not found before the edited lines"
    d2 = json.loads(canon(do)); d2["def"]["value"] = eTrue; t2 = json.loads(canon(to)); t2["thm"]["value"] = eIntro
    write_spec("M4", [(doff, canon(do), [canon(d2)]), (toff, canon(to), [canon(t2)])], info=f"def {dn} value -> {eTrue} (True); theorem {tn} value -> {eIntro} (True.intro)")
    desc["M4"] = dict(def_=dn, thm=tn, doff=doff, toff=toff)
json.dump(desc, open(os.path.join(OUT, "specs.json"), "w"), indent=1); print("specs.json written")

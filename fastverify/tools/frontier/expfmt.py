"""expfmt.py - a small reader/writer for the lean4export NDJSON format 3.1.0 (UNTRUSTED helper of tools/frontier).

Nothing here decides a verdict: every export this module writes is judged by the unchanged trusted check
(check/sound/check-sound.sh). A bug here can only make that check reject or give no verdict.

Index spaces: names ("in", 0 = anonymous), levels ("il", 0 = zero), expressions ("ie"). Declaration records: axiom, def,
thm, opaque, quot, inductive (types + ctors + recs of one block)."""
import json

DECL_KINDS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
EXPR_KINDS = ("bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj", "natVal", "strVal", "mdata")
LEVEL_KINDS = ("succ", "max", "imax", "param")


def dumps(obj):
    """compact JSON with sorted keys, as lean4export writes it (byte-identity is not needed, validity is)."""
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False, sort_keys=True)


class ExportError(Exception):
    pass


def classify(obj):
    """-> ('name'|'level'|'expr'|'decl'|'meta', kind, index or None)"""
    if "in" in obj:
        for k in ("str", "num"):
            if k in obj:
                return "name", k, obj["in"]
        raise ExportError("bad name record")
    if "il" in obj:
        for k in LEVEL_KINDS:
            if k in obj:
                return "level", k, obj["il"]
        raise ExportError("bad level record")
    if "ie" in obj:
        for k in EXPR_KINDS:
            if k in obj:
                return "expr", k, obj["ie"]
        raise ExportError("bad expr record")
    for k in DECL_KINDS:
        if k in obj:
            return "decl", k, None
    if "meta" in obj:
        return "meta", "meta", None
    raise ExportError("unknown record: %r" % (list(obj.keys()),))


def expr_children(kind, body):
    """expression children (expr indices) of an expression record body."""
    if kind == "app":
        return (body["fn"], body["arg"])
    if kind in ("lam", "forallE"):
        return (body["type"], body["body"])
    if kind == "letE":
        return (body["type"], body["value"], body["body"])
    if kind == "proj":
        return (body["struct"],)
    if kind == "mdata":
        return (body["expr"],)
    return ()


def decl_members(kind, body):
    """[(member name index, member kind, member body)] of a declaration record."""
    if kind != "inductive":
        return [(body["name"], kind, body)]
    out = []
    for t in body.get("types", []):
        out.append((t["name"], "inductType", t))
    for c in body.get("ctors", []):
        out.append((c["name"], "ctor", c))
    for r in body.get("recs", []):
        out.append((r["name"], "rec", r))
    return out


def decl_expr_roots(kind, body):
    """every expression index a declaration record refers to (types, values, recursor rule right-hand sides)."""
    roots = []
    for _, mk, mb in decl_members(kind, body):
        roots.append(mb["type"])
        if mk in ("def", "thm", "opaque") and "value" in mb:
            roots.append(mb["value"])
        if mk == "rec":
            for rule in mb.get("rules", []):
                roots.append(rule["rhs"])
    return roots


def decl_name_refs(kind, body):
    """constant names (name indices) a declaration record refers to directly, besides the constants in its expressions
    (runForUsedConsts: inductive ctors/all, ctor induct, rec rule ctors)."""
    refs = []
    for _, mk, mb in decl_members(kind, body):
        if mk == "inductType":
            refs += list(mb.get("ctors", [])) + list(mb.get("all", []))
        elif mk == "ctor":
            refs.append(mb["induct"])
        elif mk == "rec":
            refs += [rule["ctor"] for rule in mb.get("rules", [])] + list(mb.get("all", []))
    return refs


class Export:
    """a whole export in memory (structure only; the original lines are kept for declarations)."""

    def __init__(self, path, keep_lines=False):
        self.path = path
        self.names = {0: None}         # idx -> ("str"|"num", pre, value)
        self.levels = {0: ("zero",)}   # idx -> (kind, payload)
        self.exprs = {}                # idx -> (kind, body)
        self.decls = []                # [(kind, body, line_no)]
        self.by_name = {}              # name string -> decl position in self.decls
        self.meta = None
        self._nstr = {0: ""}
        self.lines = [] if keep_lines else None
        self.max_in = 0
        self.max_il = 0
        self.max_ie = -1
        self._read()

    def _read(self):
        with open(self.path, "rb") as f:
            for no, raw in enumerate(f):
                if self.lines is not None:
                    self.lines.append(raw)
                raw = raw.strip()
                if not raw:
                    continue
                try:
                    obj = json.loads(raw)
                except ValueError as e:
                    raise ExportError("line %d: not JSON (%s)" % (no + 1, e))
                cls, kind, idx = classify(obj)
                if cls == "name":
                    b = obj[kind]
                    self.names[idx] = (kind, b["pre"], b["str"] if kind == "str" else b["i"])
                    self.max_in = max(self.max_in, idx)
                elif cls == "level":
                    self.levels[idx] = (kind, obj[kind])
                    self.max_il = max(self.max_il, idx)
                elif cls == "expr":
                    self.exprs[idx] = (kind, obj[kind])
                    self.max_ie = max(self.max_ie, idx)
                elif cls == "decl":
                    pos = len(self.decls)
                    self.decls.append((kind, obj[kind], no))
                    for nidx, _, _ in decl_members(kind, obj[kind]):
                        s = self.name_str(nidx)
                        if s in self.by_name:
                            raise ExportError("duplicate declaration %s" % s)
                        self.by_name[s] = pos
                else:
                    self.meta = obj["meta"]

    def name_str(self, idx):
        s = self._nstr.get(idx)
        if s is not None:
            return s
        parts = []
        i = idx
        while i != 0:
            if i in self._nstr:
                parts.append(self._nstr[i])
                break
            n = self.names.get(i)
            if n is None:
                raise ExportError("unknown name index %d" % i)
            kind, pre, val = n
            parts.append(_esc(val) if kind == "str" else str(val))
            i = pre
        s = ".".join(reversed([p for p in parts if p != ""]))
        self._nstr[idx] = s
        return s

    def member(self, name):
        """-> (member kind, member body, decl position) of a constant name, or None"""
        pos = self.by_name.get(name)
        if pos is None:
            return None
        kind, body, _ = self.decls[pos]
        for nidx, mk, mb in decl_members(kind, body):
            if self.name_str(nidx) == name:
                return mk, mb, pos
        return None

    def expr_consts(self, roots, memo=None):
        """constant names (strings) occurring in the expression DAGs below roots."""
        seen = set()
        out = set()
        stack = list(roots)
        exprs = self.exprs
        while stack:
            e = stack.pop()
            if e in seen:
                continue
            seen.add(e)
            node = exprs.get(e)
            if node is None:
                raise ExportError("unknown expression index %d" % e)
            kind, body = node
            if kind == "const":
                out.add(self.name_str(body["name"]))
            elif kind == "proj":
                out.add(self.name_str(body["typeName"]))
            stack.extend(expr_children(kind, body))
        return out

    def member_refs(self, name, follow_value=True):
        """constants a constant refers to (runForUsedConsts semantics; follow_value=False: its type only)."""
        m = self.member(name)
        if m is None:
            return None
        mk, mb, pos = m
        roots = [mb["type"]]
        if follow_value:
            if mk in ("def", "thm", "opaque"):
                roots.append(mb["value"])
            if mk == "rec":
                roots += [r["rhs"] for r in mb.get("rules", [])]
        refs = self.expr_consts(roots)
        if follow_value:
            if mk == "inductType":
                refs |= {self.name_str(x) for x in list(mb.get("ctors", [])) + list(mb.get("all", []))}
            elif mk == "ctor":
                refs.add(self.name_str(mb["induct"]))
            elif mk == "rec":
                refs |= {self.name_str(r["ctor"]) for r in mb.get("rules", [])}
        refs.discard(name)
        return refs


def _esc(s):
    """name component as Lean prints it (guillemets when it is not a plain identifier piece)."""
    if s and all(ch.isalnum() or ch in "_'!?" or ord(ch) > 127 for ch in s) and not s[0].isdigit():
        return s
    return "«" + s + "»"

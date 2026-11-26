#!/usr/bin/python3 -I
"""ref_digest.py — Independent Python (OpenSSL hashlib.sha256) reference implementation of
R7 `fv-env-sha256-v1` and `fv-env-strict-sha256-v1` directly over NDJSON exports.

Used to cross-verify C (`ccmp-notary`, `pleanchecker-notary`) and Rust (`gruszka-r7`)
implementations bit-for-bit across 3 independent languages and 3 independent SHA-256 engines.

The reader enforces the official reader's schema
(Lean 4.36 `src/lean/LeanExport/Parse.lean`) before anything is hashed, so the oracle never emits a digest for
records the official reader rejects:
  * line 1 (metadata) is skipped as the official `parseMdata` does; every other line up to EOF is one JSON object
    (a blank line is an error: Lean's `Json.parse` of an empty line fails); duplicate keys refused (Lean's parser does);
  * the record shapes of `parseItem` exactly: {"in"|"il"|"ie": Nat, <one kind>} or {<decl kind>: {...}};
    numbers are Lean JSON numbers that are naturals (`.num (n : Nat)`: exponent 0 after Lean's normalisation),
    booleans are JSON booleans, strings JSON strings (Python truthiness is never used); nested objects may carry extra
    keys (looked up by name, as the official reader does);
  * an index bound twice, a reference to an unbound index, and a duplicate declaration are errors;
  * `letE.nondep` is required; `mdata.data` must be an object; `opaque.isUnsafe` defaults to false only when absent;
  * a regular reducibility height is converted as the official reader does (`Nat.toUInt32`: modulo 2^32);
  * string escapes: a lone surrogate becomes U+FFFD (Lean's `Json.parse`); natVal = `String.toNat?` (digits, single '_'
    separators).
Any exception, malformed record or resource error -> the line `status=DECLINED` + `reason=...` on stdout and exit 2
(never a traceback, never a digest). Success: the four key=value lines as before, exit 0.
"""
import hashlib
import json
import re
import struct
import sys
import time

try:
    sys.set_int_max_str_digits(0)   # big natVal literals (Python >= 3.10.7 limits int <-> str conversions)
except AttributeError:
    pass


class Declined(Exception):
    pass


def fail(msg):
    raise Declined(msg)


def _sha_nat(h, n: int):
    if n == 0:
        h.update(struct.pack("<I", 0))
    else:
        b = n.to_bytes((n.bit_length() + 7) // 8, "little")
        h.update(struct.pack("<I", len(b)))
        h.update(b)


def _sha_bytes(h, b: bytes):
    h.update(struct.pack("<I", len(b)))
    if b:
        h.update(b)


def _sha_list(h, items):
    h.update(struct.pack("<I", len(items)))
    for x in items:
        h.update(x)


class LeanNum:
    """A JSON number exactly as Lean's `Json.Parser.num` builds a `JsonNumber` (mantissa, exponent)."""
    __slots__ = ("m", "e")

    def __init__(self, m, e):
        self.m, self.e = m, e


_NUM = re.compile(r"(-?)(0|[1-9][0-9]*)(?:\.([0-9]+))?(?:[eE]([+-]?)([0-9]+))?")


def _lean_num(s):
    mm = _NUM.fullmatch(s)
    if not mm:
        fail("bad JSON number %r" % s[:40])
    sign, whole, frac, esign, ex = mm.groups()
    m, e = int(whole), 0
    if frac is not None:
        m, e = m * 10 ** len(frac) + int(frac), len(frac)
    if sign:
        m = -m
    if ex is not None:
        n = int(ex)
        if esign == "-":
            e += n
        else:
            if n > 100000:
                fail("JSON number exponent too large")
            if n <= e:
                e -= n
            else:
                m, e = m * 10 ** (n - e), 0
    return LeanNum(m, e)


def _no_dups(pairs):
    d = {}
    for k, v in pairs:
        k = _lean_str(k)
        if k in d:
            fail("duplicate object key %r" % k[:40])
        d[k] = v
    return d


_SURR = re.compile("[\ud800-\udfff]")


def _lean_str(s):
    return _SURR.sub("\ufffd", s)


def _bad_const(x):
    fail("non-standard JSON constant %s" % x)


def parse_line(line):
    return json.loads(line, object_pairs_hook=_no_dups, parse_int=_lean_num, parse_float=_lean_num,
                      parse_constant=_bad_const)


def is_nat(x):
    return isinstance(x, LeanNum) and x.e == 0 and x.m >= 0


def nat(x, what):
    if not is_nat(x):
        fail("%s: natural number expected" % what)
    return x.m


def jbool(x, what):
    if not isinstance(x, bool):
        fail("%s: boolean expected" % what)
    return x


def jstr(x, what):
    if not isinstance(x, str):
        fail("%s: string expected" % what)
    return _lean_str(x)


def jarr(x, what):
    if not isinstance(x, list):
        fail("%s: array expected" % what)
    return x


def jobj(x, what):
    if not isinstance(x, dict):
        fail("%s: object expected" % what)
    return x


def field(o, k, what):
    if k not in o:
        fail("%s: missing %r" % (what, k))
    return o[k]


_NATSTR = re.compile(r"[0-9]+(?:_[0-9]+)*")


def digest_ndjson(path: str):
    t0 = time.monotonic()
    h_anon = hashlib.sha256(b"\x01").digest()
    h_lzero = hashlib.sha256(b"\x10").digest()
    names = {0: h_anon}
    levels = {0: h_lzero}
    exprs_v1 = {}
    exprs_st = {}
    # official reader: a duplicate declaration is an error ("Duplicate declaration")
    consts_v1 = {}
    consts_st = {}

    bi_map = {"default": 0, "implicit": 1, "strictImplicit": 2, "instImplicit": 3}
    safety_map = {"safe": 0, "unsafe": 1, "partial": 2}
    quot_map = {"type": 0, "ctor": 1, "lift": 2, "ind": 3}

    def get(m, i, what):
        if i not in m:
            fail("%s not found %d" % (what, i))
        return m[i]

    def bind(m, i, v, what):
        if i in m:
            fail("%s index %d bound twice" % (what, i))
        m[i] = v

    def name_list(o, k, what):
        return [get(names, nat(x, what + "." + k), "Name") for x in jarr(field(o, k, what), what + "." + k)]

    def hash_const(kind, obj, strict):
        em = exprs_st if strict else exprs_v1
        h = hashlib.sha256()
        nh = get(names, nat(field(obj, "name", kind), kind + ".name"), "Name")
        lps = name_list(obj, "levelParams", kind)
        ty = get(em, nat(field(obj, "type", kind), kind + ".type"), "Expr")

        def put_head():
            h.update(nh)
            _sha_list(h, lps)
            h.update(ty)

        def val():
            return get(em, nat(field(obj, "value", kind), kind + ".value"), "Expr")

        if kind == "axiom":
            h.update(b"\x40"); put_head(); h.update(bytes([1 if jbool(field(obj, "isUnsafe", kind), "isUnsafe") else 0]))
        elif kind == "def":
            h.update(b"\x41"); put_head(); h.update(val())
            hints = field(obj, "hints", kind)
            if hints == "opaque":
                h.update(b"\x00")
            elif hints == "abbrev":
                h.update(b"\x01")
            elif isinstance(hints, dict):
                # official: `.regular level.toUInt32` (modulo 2^32)
                lvl = nat(field(hints, "regular", "def.hints"), "def.hints.regular")
                h.update(b"\x02"); h.update(struct.pack("<I", lvl % (1 << 32)))
            else:
                fail("defnInfo invalid (hints)")
            sf = jstr(field(obj, "safety", kind), "def.safety")
            if sf not in safety_map:
                fail("Unknown safety parameter: %s" % sf[:40])
            h.update(bytes([safety_map[sf]]))
            _sha_list(h, name_list(obj, "all", kind))
        elif kind == "thm":
            h.update(b"\x42"); put_head(); h.update(val())
            _sha_list(h, name_list(obj, "all", kind))
        elif kind == "opaque":
            h.update(b"\x43"); put_head(); h.update(val())
            iu = obj["isUnsafe"] if "isUnsafe" in obj else False   # official: getD (.bool false) only when absent
            h.update(bytes([1 if jbool(iu, "opaque.isUnsafe") else 0]))
            _sha_list(h, name_list(obj, "all", kind))
        elif kind == "quot":
            h.update(b"\x44"); put_head()
            qk = jstr(field(obj, "kind", kind), "quot.kind")
            if qk not in quot_map:
                fail("unknown quot kind: %s" % qk[:40])
            h.update(bytes([quot_map[qk]]))
        elif kind == "induct":
            h.update(b"\x45"); put_head()
            _sha_nat(h, nat(field(obj, "numParams", kind), "numParams"))
            _sha_nat(h, nat(field(obj, "numIndices", kind), "numIndices"))
            _sha_list(h, name_list(obj, "all", kind))
            _sha_list(h, name_list(obj, "ctors", kind))
            _sha_nat(h, nat(field(obj, "numNested", kind), "numNested"))
            h.update(bytes(1 if jbool(field(obj, k, kind), k) else 0 for k in ("isRec", "isUnsafe", "isReflexive")))
        elif kind == "ctor":
            h.update(b"\x46"); put_head()
            h.update(get(names, nat(field(obj, "induct", kind), "ctor.induct"), "Name"))
            _sha_nat(h, nat(field(obj, "cidx", kind), "cidx"))
            _sha_nat(h, nat(field(obj, "numParams", kind), "numParams"))
            _sha_nat(h, nat(field(obj, "numFields", kind), "numFields"))
            h.update(bytes([1 if jbool(field(obj, "isUnsafe", kind), "isUnsafe") else 0]))
        elif kind == "rec":
            h.update(b"\x47"); put_head()
            _sha_list(h, name_list(obj, "all", kind))
            _sha_nat(h, nat(field(obj, "numParams", kind), "numParams"))
            _sha_nat(h, nat(field(obj, "numIndices", kind), "numIndices"))
            _sha_nat(h, nat(field(obj, "numMotives", kind), "numMotives"))
            _sha_nat(h, nat(field(obj, "numMinors", kind), "numMinors"))
            k_flag = jbool(field(obj, "k", kind), "k")
            rules = jarr(field(obj, "rules", kind), "rules")
            iu = jbool(field(obj, "isUnsafe", kind), "isUnsafe")
            h.update(struct.pack("<I", len(rules)))
            for r in rules:
                r = jobj(r, "recInfo rule")
                rh = hashlib.sha256()
                rh.update(b"\x48")
                rh.update(get(names, nat(field(r, "ctor", "rule"), "rule.ctor"), "Name"))
                _sha_nat(rh, nat(field(r, "nfields", "rule"), "rule.nfields"))
                rh.update(get(em, nat(field(r, "rhs", "rule"), "rule.rhs"), "Expr"))
                h.update(rh.digest())
            h.update(bytes([1 if k_flag else 0, 1 if iu else 0]))
        else:
            fail("unknown const kind %s" % kind)
        return nh, h.digest()

    def add_const(kind, obj):
        obj = jobj(obj, kind)
        nh, ch = hash_const(kind, obj, False)
        if nh in consts_v1:
            fail("Duplicate declaration")
        consts_v1[nh] = ch
        nh2, ch2 = hash_const(kind, obj, True)
        consts_st[nh2] = ch2

    IDX = {"in": ("str", "num"), "il": ("succ", "max", "imax", "param"),
           "ie": ("bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj", "natVal", "strVal", "mdata")}
    DECL = ("axiom", "def", "thm", "opaque", "quot", "inductive")

    with open(path, "rb") as f:
        lineno = 0
        for raw in f:
            lineno += 1
            if lineno == 1:
                continue   # official parseMdata: the first line is read and ignored
            try:
                line = raw.decode("utf-8")
            except UnicodeDecodeError:
                fail("line %d: invalid UTF-8" % lineno)
            if line.endswith("\n"):
                line = line[:-1]
            try:
                rec = parse_line(line)
            except Declined as e:
                fail("line %d: %s" % (lineno, e))
            except ValueError as e:
                fail("line %d: invalid JSON (%s)" % (lineno, str(e)[:80]))
            if not isinstance(rec, dict):
                fail("line %d: Expected JSON object" % lineno)
            keys = list(rec)
            try:
                ik = [k for k in keys if k in IDX]
                if len(keys) == 2 and len(ik) == 1:
                    ix = ik[0]
                    kind = [k for k in keys if k != ix][0]
                    if kind not in IDX[ix]:
                        fail("Unknown export object with keys %s" % keys)
                    idx = nat(rec[ix], ix)
                    o = rec[kind]
                    if ix == "in":
                        o = jobj(o, "Name." + kind)
                        pre = get(names, nat(field(o, "pre", "Name"), "Name.pre"), "Name")
                        h = hashlib.sha256()
                        if kind == "str":
                            h.update(b"\x02"); h.update(pre); _sha_bytes(h, jstr(field(o, "str", "Name.str"), "Name.str").encode("utf-8"))
                        else:
                            h.update(b"\x03"); h.update(pre); _sha_nat(h, nat(field(o, "i", "Name.num"), "Name.num.i"))
                        bind(names, idx, h.digest(), "Name")
                    elif ix == "il":
                        h = hashlib.sha256()
                        if kind == "succ":
                            h.update(b"\x11"); h.update(get(levels, nat(o, "Level.succ"), "Level"))
                        elif kind in ("max", "imax"):
                            a = jarr(o, "Level." + kind)
                            if len(a) != 2:
                                fail("Level.%s invalid" % kind)
                            h.update(b"\x12" if kind == "max" else b"\x13")
                            h.update(get(levels, nat(a[0], "Level"), "Level")); h.update(get(levels, nat(a[1], "Level"), "Level"))
                        else:
                            h.update(b"\x14"); h.update(get(names, nat(o, "Level.param"), "Name"))
                        bind(levels, idx, h.digest(), "Level")
                    else:
                        if idx in exprs_v1:
                            fail("Expr index %d bound twice" % idx)
                        if kind == "bvar":
                            h = hashlib.sha256(); h.update(b"\x20"); _sha_nat(h, nat(o, "Expr.bvar"))
                            d = h.digest(); exprs_v1[idx] = d; exprs_st[idx] = d
                        elif kind == "sort":
                            h = hashlib.sha256(); h.update(b"\x23"); h.update(get(levels, nat(o, "Expr.sort"), "Level"))
                            d = h.digest(); exprs_v1[idx] = d; exprs_st[idx] = d
                        elif kind == "const":
                            o = jobj(o, "Expr.const")
                            nm = get(names, nat(field(o, "name", "Expr.const"), "Expr.const.name"), "Name")
                            us = [get(levels, nat(u, "Expr.const.us"), "Level") for u in jarr(field(o, "us", "Expr.const"), "Expr.const.us")]
                            h = hashlib.sha256(); h.update(b"\x24"); h.update(nm); _sha_list(h, us)
                            d = h.digest(); exprs_v1[idx] = d; exprs_st[idx] = d
                        elif kind == "app":
                            o = jobj(o, "Expr.app")
                            fi, ai = nat(field(o, "fn", "Expr.app"), "fn"), nat(field(o, "arg", "Expr.app"), "arg")
                            r = []
                            for em in (exprs_v1, exprs_st):
                                h = hashlib.sha256(); h.update(b"\x25"); h.update(get(em, fi, "Expr")); h.update(get(em, ai, "Expr"))
                                r.append(h.digest())
                            exprs_v1[idx], exprs_st[idx] = r
                        elif kind in ("lam", "forallE"):
                            tag = b"\x26" if kind == "lam" else b"\x27"
                            o = jobj(o, "Expr." + kind)
                            nm = get(names, nat(field(o, "name", kind), kind + ".name"), "Name")
                            ti, bi_ = nat(field(o, "type", kind), "type"), nat(field(o, "body", kind), "body")
                            bis = jstr(field(o, "binderInfo", kind), "binderInfo")
                            if bis not in bi_map:
                                fail("Invalid binder info: %s" % bis[:40])
                            bi = bytes([bi_map[bis]])
                            r = []
                            for em in (exprs_v1, exprs_st):
                                h = hashlib.sha256(); h.update(tag); h.update(bi); h.update(nm)
                                h.update(get(em, ti, "Expr")); h.update(get(em, bi_, "Expr"))
                                r.append(h.digest())
                            exprs_v1[idx], exprs_st[idx] = r
                        elif kind == "letE":
                            o = jobj(o, "Expr.letE")
                            nm = get(names, nat(field(o, "name", "letE"), "letE.name"), "Name")
                            ti, vi, bi_ = (nat(field(o, k, "letE"), "letE." + k) for k in ("type", "value", "body"))
                            nondep = jbool(field(o, "nondep", "letE"), "letE.nondep")
                            h1 = hashlib.sha256(); h1.update(b"\x28"); h1.update(nm)
                            h1.update(get(exprs_v1, ti, "Expr")); h1.update(get(exprs_v1, vi, "Expr")); h1.update(get(exprs_v1, bi_, "Expr"))
                            h2 = hashlib.sha256(); h2.update(b"\x2b"); h2.update(nm)
                            h2.update(get(exprs_st, ti, "Expr")); h2.update(get(exprs_st, vi, "Expr")); h2.update(get(exprs_st, bi_, "Expr"))
                            h2.update(bytes([1 if nondep else 0]))
                            exprs_v1[idx], exprs_st[idx] = h1.digest(), h2.digest()
                        elif kind == "natVal":
                            sv = jstr(o, "Expr.lit natVal")
                            if not _NATSTR.fullmatch(sv):
                                fail("Expr.lit natVal invalid")
                            h = hashlib.sha256(); h.update(b"\x29"); _sha_nat(h, int(sv.replace("_", "")))
                            d = h.digest(); exprs_v1[idx] = d; exprs_st[idx] = d
                        elif kind == "strVal":
                            h = hashlib.sha256(); h.update(b"\x2a"); _sha_bytes(h, jstr(o, "Expr.lit strVal").encode("utf-8"))
                            d = h.digest(); exprs_v1[idx] = d; exprs_st[idx] = d
                        elif kind == "mdata":
                            o = jobj(o, "Expr.mdata")
                            xi = nat(field(o, "expr", "Expr.mdata"), "Expr.mdata.expr")
                            jobj(field(o, "data", "Expr.mdata"), "Expr.mdata.data")
                            v1 = get(exprs_v1, xi, "Expr")
                            h2 = hashlib.sha256(); h2.update(b"\x2c"); h2.update(get(exprs_st, xi, "Expr"))
                            exprs_v1[idx], exprs_st[idx] = v1, h2.digest()
                        else:   # proj
                            o = jobj(o, "Expr.proj")
                            tn = get(names, nat(field(o, "typeName", "proj"), "proj.typeName"), "Name")
                            pi = nat(field(o, "idx", "proj"), "proj.idx")
                            si = nat(field(o, "struct", "proj"), "proj.struct")
                            r = []
                            for em in (exprs_v1, exprs_st):
                                h = hashlib.sha256(); h.update(b"\x2d"); h.update(tn); _sha_nat(h, pi); h.update(get(em, si, "Expr"))
                                r.append(h.digest())
                            exprs_v1[idx], exprs_st[idx] = r
                elif len(keys) == 1 and keys[0] in DECL:
                    k = keys[0]
                    o = jobj(rec[k], k)
                    if k == "inductive":
                        types = jarr(field(o, "types", "Inductive"), "Inductive.types")
                        ctors = jarr(field(o, "ctors", "Inductive"), "Inductive.ctors")
                        recs = jarr(field(o, "recs", "Inductive"), "Inductive.recs")
                        for t in types:
                            add_const("induct", t)
                        for c in ctors:
                            add_const("ctor", c)
                        for r in recs:
                            add_const("rec", r)
                    else:
                        add_const(k, o)
                else:
                    fail("Unknown export object with keys %s" % keys[:4])
            except Declined as e:
                fail("line %d: %s" % (lineno, e))

    def finalize(cmap, dom):
        pairs = sorted(nh + ch for nh, ch in cmap.items())
        h = hashlib.sha256()
        h.update(dom)
        h.update(struct.pack("<Q", len(pairs)))
        for p in pairs:
            h.update(p)
        return h.hexdigest()

    v1 = finalize(consts_v1, b"FV-ENV-SHA256-V1\x00")
    st = finalize(consts_st, b"FV-ENV-STRICT-SHA256-V1\x00")
    return v1, st, len(consts_v1), round((time.monotonic() - t0) * 1000)


def main(argv):
    if len(argv) != 2:
        print("status=DECLINED\nreason=usage: ref_digest.py EXPORT.ndjson")
        return 2
    try:
        v1, st, n, ms = digest_ndjson(argv[1])
    except Declined as e:
        print("status=DECLINED\nreason=%s" % " ".join(str(e).split())[:500])
        return 2
    except BaseException as e:   # never a traceback: any failure is no digest
        if isinstance(e, KeyboardInterrupt):
            raise
        print("status=DECLINED\nreason=%s: %s" % (type(e).__name__, " ".join(str(e).split())[:400]))
        return 2
    print(f"env_sha256_v1={v1}")
    print(f"env_strict_sha256_v1={st}")
    print(f"const_count={n}")
    print(f"digest_ms={ms}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

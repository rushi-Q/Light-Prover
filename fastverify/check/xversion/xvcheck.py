#!/usr/bin/python3 -I
"""xvcheck.py CHALLENGE_EXPORT COMPARATOR_JSON [--releases FILE] [--json FILE] [--require-sorried-holes]
           [--caller-resolves-kernels]

Cross-version gate of the sound check. The trusted check CS judges every export with the judge
code of the Lean 4.36 `lake comparator` and the official Lean 4.36 kernel. A challenge exported by the official Lean of
ANOTHER release R is judged soundly by them only if R is in the verified-release table (releases.json, next to this
script): R's string-literal convention and kernel built-in extension code equal 4.36's (so the 4.36 kernel's assumptions
about the kernel primitives - which `compareAt` forces to be R's official definitions - are the assumptions R's own
kernel makes), and R's official comparator judges with the same rules as 4.36's, plus R's extra rules applied here.

The release is read from the challenge export's own meta line (the challenge export is the TRUSTED, sha256-pinned output of
the official Lean of R); `lean.version` and `lean.githash` must both match the table. The meta line is parsed strictly
with the exact official shape and the table strictly with known rules only (parse_meta_line, load_release_table):
a duplicate key, BOM, unexpected field or type -> no verdict.

Definition holes. If the config has `definition_names`, the WHOLE challenge export is read by a
strict reader (read_export) that is fail-closed: it returns exactly the constants / expressions the official reader
(LeanExport.parseStream, which ccmp's FastParse reproduces exactly) builds from the same bytes, or the gate gives no
verdict. Every line is parsed as JSON (a byte template of the canonical compact layout is only a shortcut for lines it
matches in full, with the same result as the JSON parse); unknown shapes, duplicate keys, non-UTF-8, lone surrogates,
non-dense or forward indices, duplicate declarations -> DECLINED. Expression children are bound before their parents
(as the official reader requires), so every walk terminates. JSON numbers must be integer tokens (bounded digits);
natVal spellings, bound variable indices and universe level depths are validated as the official reader does.

Rules (vetoes):
  kernel-closure (every release): a `definition_names` entry that lies in the dependency closure, in the
    challenge, of a name the 4.36 kernel evaluates natively / constructs / looks up by itself (the comparator's
    primitiveTargets + builtinTargets + the kernel-implicit names, KERNEL_ROOTS) is refused (DECLINED): the solution
    could otherwise redefine e.g. Nat.shiftLeft._f, and the GMP-accelerated Nat.shiftLeft would disagree with its
    unfolding (a proof of False). The official 4.36 comparator accepts such a config; 4.37 rejects it unless sorried.
  challenge-definitions-sorried (4.37.0-rc1 and later, Lake/Check/Compare.lean): every `definition_names` entry that is a
    definition in the challenge must have the value `fun .. => sorryAx ..` (Expr.getLambdaBody.isAppOf sorryAx, where
    getLambdaBody strips `lam` AND `mdata` exactly as Lean/Expr.lean does, and getAppFn strips `app` only); else the
    official comparator of R rejects: "Challenge definition is not sorried: 'NAME'". With --require-sorried-holes the
    rule applies to every release (a violation for a release without the rule -> DECLINED).

exit 0 = release verified, all rules hold (the 4.36 check may decide); 1 = an extra rule of R fails (REJECTED, same as
R's official comparator); 2 = release not in the table / unreadable or unsupported input / refused (no verdict). Last
stdout line = JSON. This gate can only turn a verdict into REJECTED or no verdict; it never produces an acceptance.
"""
import json, os, re, sys
from array import array

HERE = os.path.dirname(os.path.realpath(__file__))
SORRY_AX = (("s", "sorryAx"),)

# the roots of the kernel closure rule. (1) the comparator's primitiveTargets (Lake/CLI/Check.lean, identical in
# v4.36.0 and v4.37.0-rc1) and builtinTargets; (2) every constant the 4.36 / 4.37-rc1 C++ kernel constructs itself
# (git grep new_persistent_expr_const / name{..} / mk_constant in src/kernel,
# = overlap/src/r9d/PChk/Incr.lean implicitNames); (3) Lean.reduceBool / Lean.reduceNat, constructed by the kernels of
# the admitted releases before 4.35 (v4.33.1). Extra names only cost refusals.
KERNEL_ROOTS = (
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land",
    "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat",
    "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
    "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
    "Nat.zero", "Nat.succ", "List.cons", "List.nil", "Bool", "Bool.true", "Bool.false", "Eq", "Eq.refl", "dontcare",
    "Lean.reduceBool", "Lean.reduceNat",
)


def _is_letter_like(c):
    v = ord(c)
    return (
        (0x3B1 <= v <= 0x3C9 and v != 0x3BB)
        or (0x391 <= v <= 0x3A9 and v != 0x3A0 and v != 0x3A3)
        or (0x3CA <= v <= 0x3FB)
        or (0x1F00 <= v <= 0x1FFE)
        or (0x2100 <= v <= 0x214F)
        or (0x1D49C <= v <= 0x1D59F)
        or (0x00C0 <= v <= 0x00FF and v != 0x00D7 and v != 0x00F7)
        or (0x0100 <= v <= 0x017F)
    )


def _is_subscript_alnum(c):
    v = ord(c)
    return (0x2080 <= v <= 0x2089) or (0x2090 <= v <= 0x209C) or (0x1D62 <= v <= 0x1D6A) or v == 0x2C7C


def _is_id_first(c):
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or c == "_" or _is_letter_like(c)


def _is_id_rest(c):
    return (
        ("a" <= c <= "z")
        or ("A" <= c <= "Z")
        or ("0" <= c <= "9")
        or c in ("_", "'", "!", "?")
        or _is_letter_like(c)
        or _is_subscript_alnum(c)
    )


def parse_lean_name(s):
    """Exact mirror of Lean 4 `String.toName` (`Init/Meta/Defs.lean:splitNameLitAux` + `Substring.Raw.toName`).
    Returns a canonical component tuple: `()` for `Name.anonymous`, `(("s", str) | ("n", int), ...)` otherwise."""
    n = len(s)
    if n == 0:
        return ()
    i = 0
    comps = []
    while True:
        if i >= n:
            return ()
        c = s[i]
        if c == "«":
            j = s.find("»", i + 1)
            if j < 0:
                return ()
            comps.append(("s", s[i + 1 : j]))
            i = j + 1
        elif _is_id_first(c):
            j = i + 1
            while j < n and _is_id_rest(s[j]):
                j += 1
            comps.append(("s", s[i:j]))
            i = j
        elif "0" <= c <= "9":
            j = i + 1
            while j < n and ("0" <= s[j] <= "9"):
                j += 1
            comps.append(("n", _decimal(s[i:j])))
            i = j
        else:
            return ()
        if i == n:
            return tuple(comps)
        if s[i] == ".":
            i += 1
        else:
            return ()


def _has_surrogate(s):
    """True if s holds a UTF-16 surrogate code point, i.e. came from a LONE surrogate escape (Python's JSON reader keeps
    it, Lean's replaces it by U+FFFD: the readers would disagree on the name, so no verdict). A valid escaped pair decodes
    to one non-surrogate code point in both readers and is accepted."""
    return any(0xD800 <= ord(ch) <= 0xDFFF for ch in s)


def _no_dups(pairs):
    d = {}
    for k, v in pairs:
        if k in d:
            raise ValueError("duplicate key %r" % (k,))
        d[k] = v
    return d


def _bad_const(x):
    raise ValueError("non-JSON constant %s" % x)


def load_json_strict(path):
    """RFC 8259 JSON of a whole file: strict UTF-8, no duplicate keys, no NaN/Infinity (as Lean's Json.parse)."""
    with open(path, "rb") as f:
        text = f.read().decode("utf-8", errors="strict")
    _check_depth(text)                 # explicit nesting bound (not the interpreter's recursion limit)
    return json.loads(text, object_pairs_hook=_no_dups, parse_constant=_bad_const)


KNOWN_RULES = ("challenge-definitions-sorried",)


def parse_meta_line(raw):
    """(lean version, lean githash, export format) from line 1 of an export, else ExportError. The line is read
    under the same rules as every other line - strict UTF-8 without a byte-order mark, one JSON value, no duplicate keys,
    no NaN/Infinity, no surrogate code point - and must have EXACTLY the shape both official exporters print
    (LeanExport/Basic.lean exportMetadata = lean4export 3.1.0 Export.lean):
      {"meta":{"exporter":{"name":"lean4export","version":S},"format":{"version":S},"lean":{"githash":S,"version":S}}}
    The official readers skip this line unread (parseMdata), so it means nothing to them; for this gate it names the
    release, and any ambiguous or unexpected spelling is no verdict (never "the last duplicate key wins")."""
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ExportError("meta line starts with a UTF-8 byte-order mark")
    try:
        o = _json_value(raw.decode("utf-8", errors="strict"))
    except (ValueError, RecursionError) as e:
        raise ExportError("meta line is not one strict JSON value: %s" % str(e)[:160])
    _check_strings(o)

    def shape(v, keys, what):
        if type(v) is not dict or set(v) != set(keys):
            raise ExportError("meta line: %s must be an object with exactly the keys %s" % (what, sorted(keys)))
        return v
    m = shape(shape(o, ("meta",), "the line")["meta"], ("exporter", "format", "lean"), "meta")
    ex = shape(m["exporter"], ("name", "version"), "meta.exporter")
    fm = shape(m["format"], ("version",), "meta.format")
    ln = shape(m["lean"], ("githash", "version"), "meta.lean")
    for v in (ex["name"], ex["version"], fm["version"], ln["githash"], ln["version"]):
        _str(v)
    if ex["name"] != "lean4export":
        raise ExportError("meta line: exporter %r is not lean4export" % (ex["name"],))
    return ln["version"], ln["githash"], fm["version"]


def load_release_table(path):
    """releases.json (trusted; generated by mkreleases.py), read strictly (load_json_strict) and checked for the shape the
    gate relies on: releases = {version: {githash: str, rules: [known rule, ..], ..}}, export_formats = [str, ..]. A rule
    this gate does not implement -> ExportError (no verdict, never a silently skipped veto)."""
    t = load_json_strict(path)
    rel = t.get("releases") if type(t) is dict else None
    fmts = t.get("export_formats") if type(t) is dict else None
    if type(rel) is not dict or type(fmts) is not list or not all(type(x) is str for x in fmts):
        raise ExportError("release table: malformed 'releases' / 'export_formats'")
    for k, r in rel.items():
        rules = r.get("rules") if type(r) is dict else None     # required (never defaulted)
        if type(r) is not dict or type(r.get("githash")) is not str or type(rules) is not list or \
                not all(type(x) is str and x in KNOWN_RULES for x in rules):
            raise ExportError("release table: malformed entry or rule not implemented by this gate for %r" % (k,))
    return t


def out(obj, rc, jf):
    """one record on stdout (and in --json FILE); if FILE cannot be written, ONE DECLINED record and exit 2"""
    s = json.dumps(obj, sort_keys=True)
    if jf:
        try:
            with open(jf, "w") as f:
                f.write(s + "\n")
        except OSError as e:
            print(json.dumps({"gate": "xversion", "challenge_export": obj.get("challenge_export"), "verdict": "DECLINED",
                              "reason": "cannot write --json %s: %s" % (jf, e)}, sort_keys=True))
            return 2
    print(s)
    return rc


def main(argv):
    jf = None
    require_sorried = False
    caller_kernels = False
    rel_path = os.path.join(HERE, "releases.json")
    pos = []
    i = 0
    while i < len(argv):
        if argv[i] == "--caller-resolves-kernels":   # the caller resolves the configuration's kernels itself
            caller_kernels = True; i += 1
        elif argv[i] == "--require-sorried-holes":   # the 4.37 rule for every release
            require_sorried = True; i += 1
        elif argv[i] == "--json":
            if i + 1 >= len(argv):
                sys.stderr.write("--json needs a value\n" + __doc__)
                return 2
            jf = argv[i + 1]; i += 2
        elif argv[i] == "--releases":
            if i + 1 >= len(argv):
                sys.stderr.write("--releases needs a value\n" + __doc__)
                return 2
            rel_path = argv[i + 1]; i += 2
        else:
            pos.append(argv[i]); i += 1
    if len(pos) != 2:
        sys.stderr.write(__doc__)
        return 2
    chal, cfgp = pos
    res = {"gate": "xversion", "challenge_export": chal}
    try:
        return gate(res, chal, cfgp, rel_path, require_sorried, jf, caller_kernels)
    except Exception as e:   # fail closed: an unexpected error is never an OK (and never rc 1)
        res.update(verdict="DECLINED", reason=f"cross-version gate error: {type(e).__name__}: {str(e)[:200]}")
        return out(res, 2, jf)


def gate(res, chal, cfgp, rel_path, require_sorried, jf, caller_kernels=False):
    try:
        table = load_release_table(rel_path)
        cfg = load_json_strict(cfgp)
        _check_strings(cfg)
        with open(chal, "rb") as f:
            raw0 = f.readline()
    except (OSError, ValueError, RecursionError, ExportError) as e:
        res.update(verdict="DECLINED", reason=f"cannot read inputs: {e}")
        return out(res, 2, jf)
    if not isinstance(cfg, dict):
        res.update(verdict="DECLINED", reason="comparator config is not a JSON object")
        return out(res, 2, jf)
    why = config_schema_error(cfg)     # before any release-rule veto (the official comparator stops here, exit 2)
    if why:
        res.update(verdict="DECLINED", reason=f"comparator config refused, as by the official comparator's config decoding: {why}")
        return out(res, 2, jf)
    # the release identity comes from line 1 alone; it is parsed strictly with the exact official shape
    try:
        ver, gh, fmt = parse_meta_line(raw0)
    except ExportError as e:
        res.update(verdict="DECLINED", reason=f"challenge export meta line (release identity) refused: {e}")
        return out(res, 2, jf)
    res.update(lean_version=ver, lean_githash=gh, export_format=fmt)
    r = table["releases"].get(ver)
    if r is None or r["githash"] != gh:
        res.update(verdict="DECLINED", reason=f"challenge exported by Lean {ver} ({gh}): release not in the verified "
                   f"table of the 4.36 trusted check ({', '.join(sorted(table['releases']))})")
        return out(res, 2, jf)
    if fmt not in table["export_formats"]:
        res.update(verdict="DECLINED", reason=f"export format {fmt} not verified for the 4.36 parser")
        return out(res, 2, jf)
    rules = r["rules"]
    res.update(release_kernel=r.get("kernel"), release_comparator=r.get("comparator"), rules=rules)
    raw_defs = cfg.get("definition_names")
    if raw_defs is None:
        defs = []
    elif isinstance(raw_defs, list) and all(isinstance(x, str) for x in raw_defs):
        defs = list(raw_defs)
    else:
        res.update(verdict="DECLINED", reason="malformed definition_names in comparator config")
        return out(res, 2, jf)
    if defs:
        canon = []
        for d in defs:
            if any(len(r) > MAX_INT_DIGITS for r in re.findall("[0-9]+", d)):   # the export integer bound
                res.update(verdict="DECLINED", reason="definition_names entry with a digit run over %d digits" % MAX_INT_DIGITS)
                return out(res, 2, jf)
            t = parse_lean_name(d) if not _has_surrogate(d) else ()
            if not t:
                res.update(verdict="DECLINED", reason=f"definition_names entry {d!r} is not a Lean name")
                return out(res, 2, jf)
            canon.append(t)
        try:
            model = read_export(chal)
        except ExportError as e:
            res.update(verdict="DECLINED", reason=f"cannot parse the challenge export (strict reader): {e}")
            return out(res, 2, jf)
        except MemoryError:
            res.update(verdict="DECLINED", reason="cannot parse the challenge export: out of memory")
            return out(res, 2, jf)
        res.update(export_read={"names": len(model.nidx), "exprs": len(model.ek), "constants": len(model.decls)})
        if "challenge-definitions-sorried" in rules or require_sorried:
            bad = [d for d, t in zip(defs, canon) if model.def_not_sorried(t)]
            if bad and "challenge-definitions-sorried" not in rules:
                res.update(verdict="DECLINED", reason=f"--require-sorried-holes: challenge definition is not sorried: '{bad[0]}' "
                           f"(the official Lean {ver} comparator does not require it; refused on request)", not_sorried=bad,
                           require_sorried_holes=True)
                return out(res, 2, jf)
            # before comparing, the official comparator resolves every configured kernel binary in ITS environment
            # (`which`; exit 2 if one is missing); the gate runs no kernels, so with kernels named it claims no REJECTED
            kern = sorted(cfg.get("external_kernels") or {}) + (["nanoda (enable_nanoda)"] if cfg.get("enable_nanoda") is True else [])
            if bad and kern and not caller_kernels:
                res.update(verdict="DECLINED", reason=f"Challenge definition is not sorried: '{bad[0]}', but the official Lean "
                           f"{ver} comparator first resolves the configured kernel binaries ({', '.join(kern)}) in its own "
                           f"environment (exit 2 if one is missing); the gate runs no kernels, so it claims no REJECTED "
                           f"(a caller that resolves them passes --caller-resolves-kernels)", not_sorried=bad)
                return out(res, 2, jf)
            if bad:
                res.update(verdict="REJECTED", reason=f"Challenge definition is not sorried: '{bad[0]}' (rule of the "
                           f"official Lean {ver} comparator, Lake/Check/Compare.lean)", not_sorried=bad)
                return out(res, 1, jf)
        hits, nclos = model.kernel_closure_holes(list(zip(defs, canon)), KERNEL_ROOTS)
        res.update(kernel_closure_size=nclos)
        if hits:
            d, path = hits[0]
            res.update(verdict="DECLINED", reason=f"definition hole '{d}' lies in the dependency closure of the kernel "
                       f"primitive / builtin / kernel-implicit name '{path[0]}' in the challenge ({' -> '.join(path)}): "
                       f"the solution could redefine what the kernel evaluates natively; refused (kernel-closure rule)",
                       kernel_closure_holes=[h for h, _ in hits])
            return out(res, 2, jf)
    if require_sorried:
        res.update(require_sorried_holes=True)
    res.update(verdict="OK", reason=f"Lean {ver} is verified for the 4.36 trusted check" +
               (f"; extra rules hold: {', '.join(rules)}" if rules else ""))
    return out(res, 0, jf)


# ---------------------------------------------------------------------------------------------------------------------
# Strict reader of the lean4export NDJSON format (3.1.0), mirror of LeanExport.parseStream (Lean v4.36.0 = v4.37.0-rc1
# src/lean/LeanExport/Parse.lean) for everything this gate decides on.
#
# Contract: read_export(path) either raises ExportError or returns a Model whose name / expression / constant tables are
# exactly those the official reader builds from the same file (names compared as Lean Names, i.e. canonical component
# tuples). Why (see check/xversion/README.md):
#  * lines are split at b"\n" like IO.FS.Stream.getLine; the first line (meta) is skipped like parseMdata;
#  * each line is strict UTF-8 (else ExportError; the official reader's lossy conversion is not reproduced) and is one
#    JSON value under RFC 8259 (Python's json with duplicate keys and NaN/Infinity refused = Lean's Json.parse, which also
#    refuses duplicate keys), except that a decoded string still holding a surrogate code point is refused: a LONE
#    surrogate escape becomes U+FFFD in Lean but stays a surrogate in Python; a valid escaped surrogate PAIR decodes to
#    the same single code point in both and is accepted;
#  * numbers: a fraction / exponent token anywhere is refused (Python would round it to a binary float, Lean keeps
#    an exact decimal and bounds the exponent; official exports print integers only); an integer token has at most
#    MAX_INT_DIGITS digits, converted exactly in INT_CHUNK-digit pieces without touching CPython's interpreter-wide
#    int(str) limit; above the bound: refused;
#  * the top-level key set must be one of the official parseItem shapes; required fields have the official JSON types
#    (index = non-negative JSON integer: Python int, never bool / float); extra keys INSIDE a record are ignored, as the
#    official reader ignores them (it looks fields up by name);
#  * indices are dense and bound before use (each new name / level / expression index = current table size; every
#    reference < table size): in any export the official reader accepts with this numbering, "bound" <-> "< size". The
#    official exporter numbers densely (ccmp's FastParse relies on the same); anything else -> ExportError (no verdict);
#  * duplicate constant names (as Lean Names) -> ExportError (the official reader fails);
#  * FAST PATH: a line that matches IN FULL one of the byte templates below (the canonical compact layout: fixed key
#    order, JSON integers without sign / leading zeros, strings without '\\', '"' or control bytes) has exactly the JSON
#    value the template spells out, so it is handled without json.loads, with the same table updates; every other line
#    (any spacing, key order, escape, unknown kind) takes the JSON path.
# Fields the gate does not use are validated as the official reader validates them where it can fail on them (a
# natVal spelling must pass String.toNat?; a bvar index and a level depth must be representable - the kernel aborts
# beyond them), otherwise only type-checked. Standing comparisons: check/xversion/test/reader-corpus (the reader corpus with the
# official answers of v4.36.0 and v4.37.0-rc1) and check/xversion/test/oracle (official reader run on the spot).
# ---------------------------------------------------------------------------------------------------------------------
class ExportError(Exception):
    pass


E_BVAR, E_SORT, E_CONST, E_APP, E_LAM, E_FORALL, E_LET, E_PROJ, E_NAT, E_STR, E_MDATA = range(11)
# Limits and checks of the official reader that the tables do not keep.
MAX_BVAR_INDEX = 1048574     # Expr.bvar i has looseBVarRange i+1 <= 1048575: src/kernel/expr.cpp lean_expr_mk_data
#                              (v4.36.0 = v4.37.0-rc1), beyond it lean_internal_panic "too many bound variables" (abort)
MAX_LEVEL_DEPTH = 16777215   # Level depth <= 2^24-1: src/kernel/level.cpp lean_level_mk_data (v4.36.0 = v4.37.0-rc1),
#                              beyond it lean_internal_panic "universe level depth is too big" (abort)
MAX_INT_DIGITS = 20000       # explicit bound on one JSON integer token (official exports may carry e.g. a 4301-digit
#                              name component, beyond CPython's default 4300-digit int(str) limit)
INT_CHUNK = 600              # int() on <= 600 digits is allowed under ANY CPython int_max_str_digits setting (0 or >= 640)
RX_NATVAL = re.compile(r"[0-9]+(?:_[0-9]+)*")   # String.toNat? (= String.isNat): non-empty, ASCII digits, '_' only
#                              between two digits (Init/Data/String/Slice.lean, Slice/Numeric.lean; v4.36.0 = v4.37.0-rc1)


MAX_JSON_DEPTH = 512        # nesting bound of every JSON value the gate parses, checked BEFORE parsing so the
#                             outcome does not depend on the interpreter's recursion limit (3.10 vs 3.12); below the
#                             official readers' limits (4.37.0-rc1: 10000; 4.36.0: none), official exports nest <= ~5


def _check_depth(text):
    """ValueError if a JSON text nests arrays / objects more than MAX_JSON_DEPTH deep (strings skipped, as the JSON
    lexer does); a text with at most MAX_JSON_DEPTH brackets cannot, and is not scanned"""
    if text.count("{") + text.count("[") <= MAX_JSON_DEPTH:
        return
    depth, in_str, esc = 0, False, False
    for ch in text:
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
        elif ch == '"':
            in_str = True
        elif ch == "{" or ch == "[":
            depth += 1
            if depth > MAX_JSON_DEPTH:
                raise ValueError("JSON nesting deeper than %d" % MAX_JSON_DEPTH)
        elif ch == "}" or ch == "]":
            depth -= 1


def _bad_float(s):
    raise ValueError("non-integer JSON number %s (refused: Python would round it to a binary float, Lean keeps an exact "
                     "decimal; official exports print integers only)" % s[:40])


def _decimal(d):
    """the value of a string of ASCII digits, exact for any length, without CPython's int(str) digit limit and without
    touching the interpreter-wide setting (chunks of INT_CHUNK digits)"""
    if len(d) <= INT_CHUNK:
        return int(d)
    v = 0
    for j in range(0, len(d), INT_CHUNK):
        c = d[j:j + INT_CHUNK]
        v = v * 10 ** len(c) + int(c)
    return v


def _exact_int(s):
    """the exact value of a JSON integer token, at most MAX_INT_DIGITS digits. No interpreter-wide state is touched
    (the earlier temporary sys.set_int_max_str_digits lift was not thread-safe): tokens longer than INT_CHUNK digits are
    converted in INT_CHUNK-digit pieces, each within every possible CPython limit."""
    neg = s[:1] == "-"
    d = s[1:] if neg else s
    if len(d) > MAX_INT_DIGITS:
        raise ValueError("JSON integer with more than %d digits (reader bound)" % MAX_INT_DIGITS)
    if len(d) <= INT_CHUNK:
        return int(s)
    v = _decimal(d)
    return -v if neg else v


def _json_value(text):
    """one JSON value of an export line: duplicate keys, NaN/Infinity and fraction/exponent tokens refused, integers exact,
    nesting bounded by MAX_JSON_DEPTH"""
    _check_depth(text)
    return json.loads(text, object_pairs_hook=_no_dups, parse_constant=_bad_const, parse_float=_bad_float,
                      parse_int=_exact_int)


def _comp_str(v):
    if type(v) is int:
        try:
            return str(v)
        except ValueError:            # beyond CPython's int->str limit: messages only
            return "<%d-bit number>" % v.bit_length()
    return v


def _vstr(v):
    """a value for an error message (never raises: large ints are not converted beyond CPython's limit)"""
    return _comp_str(v) if type(v) is int else repr(v)[:60]


def config_schema_error(c):
    """None, or the first error of the OFFICIAL comparator's config decoding: Lake/CLI/Check.lean `structure Config`
    (identical in v4.36.0 and v4.37.0-rc1) `deriving Lean.FromJson` = for each field in order, fromJson? of
    getObjValD json key (a missing key reads as null; a `?` field drops the `?` from its key); Option fields accept null;
    extra keys are ignored. The official comparator stops with a configuration error (exit 2) on any of these, before it
    compares anything - so must the gate, before any release-rule veto."""
    def strs(v):
        return type(v) is list and all(type(x) is str for x in v)
    fields = (("challenge_module", lambda v: type(v) is str, False), ("solution_module", lambda v: type(v) is str, False),
              ("theorem_names", strs, False), ("definition_names", strs, True), ("permitted_axioms", strs, False),
              ("enable_nanoda", lambda v: type(v) is bool, True),
              ("external_kernels", lambda v: type(v) is dict and all(strs(x) for x in v.values()), True))
    if type(c) is not dict:
        return "the config is not a JSON object"
    for k, ok, optional in fields:
        v = c.get(k)
        if v is None and optional:
            continue
        if not ok(v):
            return "Config.%s: %s" % (k, "missing or null" if v is None else "wrong type")
    # the deterministic checks of resolveExternalKernels (v4.36.0 = v4.37.0-rc1, TreeMap = key order) and the
    # v4.37.0-rc1 own-kernel name clash (refused for every release): the official comparator exits 2 on each
    ek = c.get("external_kernels") or {}
    if c.get("enable_nanoda") is True and ek:
        return "cannot use `enable_nanoda` and `external_kernels` at the same time; register nanoda in the list instead"
    for name in sorted(ek):
        if not ek[name]:
            return "`%s` has an empty command" % name
    if "Lean default" in ek:
        return "the external kernel `Lean default` has the name of a kernel Lake runs itself"
    return None
_N = rb"(0|[1-9][0-9]{0,17})"
_S = rb'"([^"\\\x00-\x1f]*)"'
_BI = rb'"(default|implicit|strictImplicit|instImplicit)"'
_NL = rb"((?:0|[1-9][0-9]{0,17})(?:,(?:0|[1-9][0-9]{0,17}))*)?"
RX_APP = re.compile(rb'\{"app":\{"arg":' + _N + rb',"fn":' + _N + rb'\},"ie":' + _N + rb"\}")
RX_LAM = re.compile(rb'\{"ie":' + _N + rb',"lam":\{"binderInfo":' + _BI + rb',"body":' + _N + rb',"name":' + _N +
                    rb',"type":' + _N + rb"\}\}")
RX_FORALL = re.compile(rb'\{"forallE":\{"binderInfo":' + _BI + rb',"body":' + _N + rb',"name":' + _N + rb',"type":' + _N +
                       rb'\},"ie":' + _N + rb"\}")
RX_NAME = re.compile(rb'\{"in":' + _N + rb',"str":\{"pre":' + _N + rb',"str":' + _S + rb"\}\}")
RX_CONST = re.compile(rb'\{"const":\{"name":' + _N + rb',"us":\[' + _NL + rb'\]\},"ie":' + _N + rb"\}")
RX_BVAR = re.compile(rb'\{"bvar":' + _N + rb',"ie":' + _N + rb"\}")
RX_SORT = re.compile(rb'\{"ie":' + _N + rb',"sort":' + _N + rb"\}")
BINDER_INFOS = ("default", "implicit", "strictImplicit", "instImplicit")


def _nat(v):
    if type(v) is not int or v < 0:
        raise ExportError("expected a non-negative integer, got %s" % (_vstr(v),))
    return v


def _str(v):
    if type(v) is not str:
        raise ExportError("expected a string, got %r" % (v,))
    return v


def _bool(v):
    if type(v) is not bool:
        raise ExportError("expected a boolean, got %r" % (v,))
    return v


def _obj(v):
    if type(v) is not dict:
        raise ExportError("expected an object")
    return v


def _arr(v):
    if type(v) is not list:
        raise ExportError("expected an array")
    return v


def _check_strings(v):
    """refuse surrogate code points anywhere in a decoded JSON value (keys included)"""
    st = [v]
    while st:
        x = st.pop()
        if type(x) is str:
            if _has_surrogate(x):
                raise ExportError("string with a surrogate code point")
        elif type(x) is dict:
            for k, y in x.items():
                if _has_surrogate(k):
                    raise ExportError("key with a surrogate code point")
                st.append(y)
        elif type(x) is list:
            st.extend(x)


class Model:
    """Tables of a challenge export. Names: canonical ids (cid; 0 = anonymous), interned on (prefix cid, component), so two
    export indices of the same Lean Name get the same cid. Expressions: kind ek[i] and children ea[i], eb[i] (+ ec for
    letE bodies): const -> ea = name cid; app -> ea = fn, eb = arg; lam / forallE -> ea = type, eb = body; letE -> ea =
    type, eb = value, ec[i] = body; proj -> ea = struct, eb = typeName cid; mdata -> ea = expr. Constants: decls[cid] =
    (kind, expression indices (type first; value second for def / thm / opaque), referenced name cids)."""

    def __init__(self):
        self.intern = {}
        self.cid_pre = array("q", [-1])
        self.cid_comp = [None]
        self.nidx = array("q", [0])
        self.nlevels = 1
        self.ldepth = array("q", [0])
        self.ek = bytearray()
        self.ea = array("q")
        self.eb = array("q")
        self.ec = {}
        self.decls = {}

    def lookup(self, t):
        c = 0
        for kind, v in t:
            c = self.intern.get((c, 0, v) if kind == "s" else (c, 1, v))
            if c is None:
                return None
        return c

    def show(self, c):
        parts = []
        while c > 0:
            parts.append(_comp_str(self.cid_comp[c]))
            c = self.cid_pre[c]
        return ".".join(reversed(parts)) or "[anonymous]"

    def def_not_sorried(self, t):
        """True iff t is a definition in the challenge whose value is not `fun .. => sorryAx ..`:
        not (Expr.getLambdaBody value).isAppOf sorryAx, with Lean v4.37.0-rc1 Lean/Expr.lean
          getLambdaBody : .lam _ _ b _ => getLambdaBody b | .mdata _ b => getLambdaBody b | e => e
          getAppFn      : .app f _ => getAppFn f | e => e
          isAppOf e n   : match e.getAppFn with | .const c _ => c == n | _ => false
        Non-definitions / absent names: False (the comparator itself rejects them: 'Const not found in challenge' /
        'Challenge constant is not a definition'). Each step goes to a child, whose index is smaller (bound before)."""
        c = self.lookup(t)
        d = self.decls.get(c) if c is not None else None
        if d is None or d[0] != "def":
            return False
        ek, ea, eb = self.ek, self.ea, self.eb
        e = d[1][1]
        while ek[e] == E_LAM or ek[e] == E_MDATA:
            nxt = eb[e] if ek[e] == E_LAM else ea[e]
            if not 0 <= nxt < e:
                raise ExportError("expression walk does not descend")
            e = nxt
        while ek[e] == E_APP:
            nxt = ea[e]
            if not 0 <= nxt < e:
                raise ExportError("expression walk does not descend")
            e = nxt
        sorry = self.lookup(SORRY_AX)
        return not (ek[e] == E_CONST and sorry is not None and ea[e] == sorry)

    def kernel_closure_holes(self, holes, roots):
        """([(hole as given, path root -> .. -> hole)], closure size): the definition holes in the dependency closure of
        the roots. Dependencies of a constant = every constant of its type / value / recursor-rule right-hand sides
        (Expr.getUsedConstants, plus proj type names) and every name it lists (inductive all / ctors, ctor induct,
        recursor all / rule ctors, def / thm / opaque all; quot -> Eq): a superset of Lake.Check.runForUsedConsts, which
        the comparator follows from its primitiveTargets."""
        ek, ea, eb, ec, decls = self.ek, self.ea, self.eb, self.ec, self.decls
        parent = {}
        stack = []
        for r in roots:
            c = self.lookup(parse_lean_name(r))
            if c is not None and c not in parent:
                parent[c] = -1
                stack.append(c)
        seen = bytearray(len(ek))
        eq = self.lookup((("s", "Eq"),))
        while stack:
            c = stack.pop()
            d = decls.get(c)
            if d is None:
                continue
            for n in d[2] + ((eq,) if d[0] == "quot" and eq is not None else ()):
                if n not in parent:
                    parent[n] = c
                    stack.append(n)
            es = list(d[1])
            while es:
                e = es.pop()
                if seen[e]:
                    continue
                seen[e] = 1
                k = ek[e]
                if k == E_CONST:
                    n = ea[e]
                    if n not in parent:
                        parent[n] = c
                        stack.append(n)
                elif k == E_APP or k == E_LAM or k == E_FORALL:
                    es.append(ea[e]); es.append(eb[e])
                elif k == E_LET:
                    es.append(ea[e]); es.append(eb[e]); es.append(ec[e])
                elif k == E_PROJ:
                    es.append(ea[e])
                    n = eb[e]
                    if n not in parent:
                        parent[n] = c
                        stack.append(n)
                elif k == E_MDATA:
                    es.append(ea[e])
        hits = []
        for raw, t in holes:
            c = self.lookup(t)
            if c is not None and c in parent:
                path = []
                x = c
                while x != -1 and len(path) < 64:
                    path.append(self.show(x))
                    x = parent[x]
                hits.append((raw, list(reversed(path))))
        return hits, len(parent)


def read_export(path, fast=True):
    """the strict reader (see the contract above). Touches no interpreter-wide state (integer tokens beyond CPython's
    int(str) digit limit are converted in chunks by _exact_int), so concurrent calls are safe"""
    return _read_export(path, fast)


def _read_export(path, fast):
    m = Model()
    intern, cid_pre, cid_comp, nidx = m.intern, m.cid_pre, m.cid_comp, m.nidx
    ek, ea, eb, ec, decls = m.ek, m.ea, m.eb, m.ec, m.decls

    def name_cid(i):
        if type(i) is not int or not 0 <= i < len(nidx):
            raise ExportError("name index %s not bound" % (_vstr(i),))
        return nidx[i]

    def name_list(v):
        return [name_cid(x) for x in _arr(v)]

    def expr_ref(i, cur):
        if type(i) is not int or not 0 <= i < cur:
            raise ExportError("expression index %s not bound" % (_vstr(i),))
        return i

    def level_ref(i):
        if type(i) is not int or not 0 <= i < m.nlevels:
            raise ExportError("level index %s not bound" % (_vstr(i),))

    def add_name(i, pre, key, comp):
        if i != len(nidx):
            raise ExportError("name index %s bound twice or sparse" % _vstr(i))
        p = name_cid(pre)
        k = (p,) + key
        c = intern.get(k)
        if c is None:
            c = len(cid_pre)
            intern[k] = c
            cid_pre.append(p)
            cid_comp.append(comp)
        nidx.append(c)

    def add_expr(i, kind, a, b):
        if i != len(ek):
            raise ExportError("expression index %s bound twice or sparse" % _vstr(i))
        ek.append(kind); ea.append(a); eb.append(b)

    def add_const(c, kind, exprs, refs):
        if c in decls:
            raise ExportError("duplicate declaration: %s" % m.show(c))
        decls[c] = (kind, tuple(exprs), tuple(refs))

    def expr_obj(i, kind, data):
        cur = len(ek)
        if kind == "bvar":
            if _nat(data) > MAX_BVAR_INDEX:     # r3: Expr.bvar constructor range (the official reader aborts)
                raise ExportError("too many bound variables: bvar %s" % _vstr(data))
            add_expr(i, E_BVAR, 0, 0)
        elif kind == "sort":
            level_ref(data); add_expr(i, E_SORT, 0, 0)
        elif kind == "const":
            data = _obj(data)
            n = name_cid(data.get("name"))
            for u in _arr(data.get("us")):
                level_ref(u)
            add_expr(i, E_CONST, n, 0)
        elif kind == "app":
            data = _obj(data)
            f = expr_ref(data.get("fn"), cur); a = expr_ref(data.get("arg"), cur)
            add_expr(i, E_APP, f, a)
        elif kind in ("lam", "forallE"):
            data = _obj(data)
            name_cid(data.get("name")); t = expr_ref(data.get("type"), cur); b = expr_ref(data.get("body"), cur)
            if _str(data.get("binderInfo")) not in BINDER_INFOS:
                raise ExportError("invalid binder info")
            add_expr(i, E_LAM if kind == "lam" else E_FORALL, t, b)
        elif kind == "letE":
            data = _obj(data)
            name_cid(data.get("name")); t = expr_ref(data.get("type"), cur); v = expr_ref(data.get("value"), cur)
            b = expr_ref(data.get("body"), cur); _bool(data.get("nondep"))
            add_expr(i, E_LET, t, v)
            ec[i] = b
        elif kind == "proj":
            data = _obj(data)
            tn = name_cid(data.get("typeName")); _nat(data.get("idx")); s = expr_ref(data.get("struct"), cur)
            add_expr(i, E_PROJ, s, tn)
        elif kind == "natVal":
            if RX_NATVAL.fullmatch(_str(data)) is None:   # r3: String.toNat? fails -> 'Expr.lit natVal invalid'
                raise ExportError("Expr.lit natVal invalid: %r" % data[:40])
            add_expr(i, E_NAT, 0, 0)
        elif kind == "strVal":
            _str(data); add_expr(i, E_STR, 0, 0)
        elif kind == "mdata":
            data = _obj(data)
            x = expr_ref(data.get("expr"), cur); _obj(data.get("data"))
            add_expr(i, E_MDATA, x, 0)
        else:
            raise ExportError("unknown expression kind %r" % (kind,))

    def cur_expr(v):
        return expr_ref(v, len(ek))

    def decl_obj(kind, data):
        data = _obj(data)
        n = name_cid(data.get("name"))
        name_list(data.get("levelParams"))
        t = cur_expr(data.get("type"))
        if kind == "axiom":
            _bool(data.get("isUnsafe"))
            add_const(n, "axiom", [t], [])
        elif kind == "def":
            v = cur_expr(data.get("value"))
            h = data.get("hints")
            if type(h) is dict:
                _nat(h.get("regular"))
            elif h not in ("opaque", "abbrev") or type(h) is not str:
                raise ExportError("invalid hints")
            if _str(data.get("safety")) not in ("unsafe", "safe", "partial"):
                raise ExportError("invalid safety")
            add_const(n, "def", [t, v], name_list(data.get("all")))
        elif kind == "thm":
            v = cur_expr(data.get("value"))
            add_const(n, "thm", [t, v], name_list(data.get("all")))
        elif kind == "opaque":
            v = cur_expr(data.get("value"))
            if "isUnsafe" in data:
                _bool(data["isUnsafe"])
            add_const(n, "opaque", [t, v], name_list(data.get("all")))
        elif kind == "quot":
            if _str(data.get("kind")) not in ("type", "ctor", "lift", "ind"):
                raise ExportError("invalid quot kind")
            add_const(n, "quot", [t], [])   # + Eq, resolved in kernel_closure_holes (quot.cpp: Eq / Eq.refl)

    def inductive_obj(data):
        data = _obj(data)
        types, ctors, recs = _arr(data.get("types")), _arr(data.get("ctors")), _arr(data.get("recs"))
        for ty in types:
            ty = _obj(ty)
            n = name_cid(ty.get("name")); name_list(ty.get("levelParams")); t = cur_expr(ty.get("type"))
            for f in ("numParams", "numIndices", "numNested"):
                _nat(ty.get(f))
            for f in ("isRec", "isUnsafe", "isReflexive"):
                _bool(ty.get(f))
            add_const(n, "inductive", [t], name_list(ty.get("all")) + name_list(ty.get("ctors")))
        for ct in ctors:
            ct = _obj(ct)
            n = name_cid(ct.get("name")); name_list(ct.get("levelParams")); t = cur_expr(ct.get("type"))
            ind = name_cid(ct.get("induct"))
            for f in ("cidx", "numParams", "numFields"):
                _nat(ct.get(f))
            _bool(ct.get("isUnsafe"))
            add_const(n, "ctor", [t], [ind])
        for rc in recs:
            rc = _obj(rc)
            n = name_cid(rc.get("name")); name_list(rc.get("levelParams")); t = cur_expr(rc.get("type"))
            refs = name_list(rc.get("all"))
            for f in ("numParams", "numIndices", "numMotives", "numMinors"):
                _nat(rc.get(f))
            _bool(rc.get("k")); _bool(rc.get("isUnsafe"))
            es = [t]
            for ru in _arr(rc.get("rules")):
                ru = _obj(ru)
                refs.append(name_cid(ru.get("ctor"))); _nat(ru.get("nfields")); es.append(cur_expr(ru.get("rhs")))
            add_const(n, "rec", es, refs)

    def json_line(ln):
        o = _json_value(ln.decode("utf-8", errors="strict"))
        if type(o) is not dict:
            raise ExportError("line is not a JSON object")
        _check_strings(o)
        ks = sorted(o)
        if len(ks) == 2 and ks[0] == "in" and ks[1] in ("str", "num"):
            i = _nat(o["in"])
            data = _obj(o[ks[1]])
            pre = _nat(data.get("pre"))
            if ks[1] == "str":
                s = _str(data.get("str"))
                add_name(i, pre, (0, s), s)
            else:
                v = _nat(data.get("i"))
                add_name(i, pre, (1, v), v)
        elif len(ks) == 2 and ks[0] == "il" and ks[1] in ("succ", "max", "imax", "param"):
            i = _nat(o["il"])
            if i != m.nlevels:
                raise ExportError("level index %s bound twice or sparse" % _vstr(i))
            v = o[ks[1]]
            if ks[1] == "succ":
                level_ref(v)
                d = m.ldepth[v] + 1
            elif ks[1] == "param":
                name_cid(v)
                d = 0
            else:
                v = _arr(v)
                if len(v) != 2:
                    raise ExportError("invalid level")
                level_ref(v[0]); level_ref(v[1])
                d = max(m.ldepth[v[0]], m.ldepth[v[1]]) + 1
            if d > MAX_LEVEL_DEPTH:      # r3: the official reader's Level constructor aborts beyond this depth
                raise ExportError("universe level depth %d is too big (> %d)" % (d, MAX_LEVEL_DEPTH))
            m.ldepth.append(d)
            m.nlevels += 1
        elif len(ks) == 2 and "ie" in ks:
            kind = ks[1] if ks[0] == "ie" else ks[0]
            expr_obj(_nat(o["ie"]), kind, o[kind])
        elif len(ks) == 1 and ks[0] in ("axiom", "def", "thm", "opaque", "quot"):
            decl_obj(ks[0], o[ks[0]])
        elif len(ks) == 1 and ks[0] == "inductive":
            inductive_obj(o["inductive"])
        else:
            raise ExportError("unknown export object with keys %s" % ks)

    lineno = 0
    try:
        with open(path, "rb") as f:
            if not f.readline():
                raise ExportError("empty export")
            for ln in f:
                lineno += 1
                body = ln[:-1] if ln.endswith(b"\n") else ln
                if fast:
                    mt = RX_APP.fullmatch(body)
                    if mt:
                        a, fn, i = int(mt.group(1)), int(mt.group(2)), int(mt.group(3))
                        if i != len(ek) or fn >= i or a >= i:
                            raise ExportError("app: index not dense / child not bound")
                        ek.append(E_APP); ea.append(fn); eb.append(a)
                        continue
                    mt = RX_LAM.fullmatch(body)
                    if mt:
                        i, b, n, t = int(mt.group(1)), int(mt.group(3)), int(mt.group(4)), int(mt.group(5))
                        if i != len(ek) or b >= i or t >= i or n >= len(nidx):
                            raise ExportError("lam: index not dense / child not bound")
                        ek.append(E_LAM); ea.append(t); eb.append(b)
                        continue
                    mt = RX_FORALL.fullmatch(body)
                    if mt:
                        b, n, t, i = int(mt.group(2)), int(mt.group(3)), int(mt.group(4)), int(mt.group(5))
                        if i != len(ek) or b >= i or t >= i or n >= len(nidx):
                            raise ExportError("forallE: index not dense / child not bound")
                        ek.append(E_FORALL); ea.append(t); eb.append(b)
                        continue
                    mt = RX_NAME.fullmatch(body)
                    if mt:
                        s = mt.group(3).decode("utf-8", errors="strict")
                        add_name(int(mt.group(1)), int(mt.group(2)), (0, s), s)
                        continue
                    mt = RX_CONST.fullmatch(body)
                    if mt:
                        n, us, i = int(mt.group(1)), mt.group(2), int(mt.group(3))
                        if i != len(ek) or n >= len(nidx):
                            raise ExportError("const: index not dense / name not bound")
                        if us:
                            for u in us.split(b","):
                                if int(u) >= m.nlevels:
                                    raise ExportError("const: level not bound")
                        ek.append(E_CONST); ea.append(nidx[n]); eb.append(0)
                        continue
                    mt = RX_BVAR.fullmatch(body)
                    if mt:
                        i = int(mt.group(2))
                        if i != len(ek):
                            raise ExportError("bvar: index not dense")
                        if int(mt.group(1)) > MAX_BVAR_INDEX:   # r3: same check as the JSON path
                            raise ExportError("too many bound variables: bvar %s" % mt.group(1).decode())
                        ek.append(E_BVAR); ea.append(0); eb.append(0)
                        continue
                    mt = RX_SORT.fullmatch(body)
                    if mt:
                        i, u = int(mt.group(1)), int(mt.group(2))
                        if i != len(ek) or u >= m.nlevels:
                            raise ExportError("sort: index not dense / level not bound")
                        ek.append(E_SORT); ea.append(0); eb.append(0)
                        continue
                json_line(ln)
    except ExportError as e:
        raise ExportError("line %d: %s" % (lineno + 1, e))
    except (OSError, ValueError, OverflowError, KeyError, TypeError, IndexError, RecursionError) as e:
        raise ExportError("line %d: %s: %s" % (lineno + 1, type(e).__name__, str(e)[:160]))
    return m


if __name__ == "__main__":
    try:
        rc = main(sys.argv[1:])
    except Exception:          # never exit 1 (REJECTED) on an internal error
        rc = 2
    sys.exit(rc)

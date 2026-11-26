#!/usr/bin/python3 -I
"""tools/frontier/frontier.py - SOUND conditional verification modulo an explicit `sorry` frontier.
Fast preparer: check/frontier/src FrontierPrep.lean (scan + mint with ccmp's reader); CONDITIONAL interface.

During development a project always has `sorry` lemmas; the sound check then only says REJECTED (sorryAx). This tool
answers the question a mathematician / proving agent actually has: "are the challenge's theorems PROVED, modulo exactly
these open lemmas, with everything else kernel-checked and no other axiom?" - with NO change to the trusted check.

  frontier.py scan    EXPORT CONFIG [--json FILE]
  frontier.py prepare EXPORT CHALLENGE_EXPORT CONFIG OUTDIR [--frontier auto|NAME,...|@FILE] [--axioms NAME,...|@FILE]
                      [--pinned PINDIR]
  frontier.py check   OUTDIR [--threads N] [--svc DIR] [--json FILE]
  frontier.py verify  EXPORT CHALLENGE_EXPORT CONFIG OUTDIR [prepare options] [check options]   (= prepare + check)
                      [--challenge-sha256 HEX --comparator-sha256 HEX]   (the challenge pin needs the comparator pin)
  frontier.py pin     EXPORT CHALLENGE_EXPORT CONFIG PINDIR [--frontier ...] [--threads N]   (mint + verify a frontier
                      challenge once; later runs use --pinned PINDIR so the open lemmas' statements cannot drift)
  frontier.py run     PROJECT CHALLENGE_DIR OUT --challenge-sha256 HEX --comparator-sha256 HEX [--frontier ...] [--pinned PINDIR]
                      [--threads N] [-- EXTRA bin/fastverify ARGS]   (build + export with bin/fastverify, then verify)
  A pinned input (run: CHALLENGE_DIR/comparator.json, then the challenge export; verify: both, when pinned) is read
  ONCE into a private copy OUT/pinned/* whose sha256 must equal the pin; only that copy is used afterwards (run passes it to
  bin/fastverify with --comparator-config; prepare, the trusted checks and check()'s re-verification read it). run takes
  the frontier path only for an export bin/fastverify JUDGED (ACCEPTED 0 / REJECTED 1) on exactly the pinned inputs, and
  judges that export as recorded (sha256 in result.json, copied once). OUT must be new, empty or an earlier run's OUT
  (marker .frontier-run-out); run first removes its own earlier outputs there, so nothing of an earlier run is judged.
  scan / prepare / check / pin refuse the pin options (they cannot enforce them).
  check() requires prepare's measured hashes to BE the pins (run / verify) and passes pins to both trusted runs
  (check-sound verifies its private copies: official / frontier challenge, and the sha256 of the very config bytes
  check() validated). Every ending without a verdict - refused input, OSError / internal error, SIGTERM / SIGINT / SIGHUP
  (handled once: the whole descendant tree is killed) - is one NO_VERDICT JSON line, exit 2. run locks OUT (flock on the
  marker, never followed through a link): one run per OUT. The comparator sha256 prepare records is that of exactly
  the bytes it parsed; children stay in frontier.py's process group (a supervisor's group SIGKILL takes them all).
  Options take `--opt VALUE` or `--opt=VALUE`; a missing value or a wrong number of positional arguments: exit 2.

Exit: 0 = ACCEPTED (no frontier left: the plain sound verdict), 3 = CONDITIONAL (verdict string "CONDITIONAL": proved from
the listed open lemmas), 1 = REJECTED, 2 = no verdict. For rewards / CI gates: only exit 0 means "proved".
GOAL S1(3): a CONFIG whose permitted_axioms leave {propext, Quot.sound, Classical.choice} (canonical Lean names,
the judges' parser) is refused by every subcommand: NO_VERDICT, exit 2. The trusted check's --extra-axioms only ever carries
the internal lists (check A: sorryAx iff the official challenge has it; check B: exactly the frontier F, reported, verdict
at most CONDITIONAL); a plain ACCEPTED (exit 0) is given only for an empty frontier, by a run without --extra-axioms.

How (README.md has the full soundness argument):
  S  = the solution export (untrusted build + exporter), C = the OFFICIAL challenge export (sha256-pinned), F = frontier.
  S' = S with every frontier theorem record turned into an axiom record of the same name, universe parameters and type
       (in place; nothing else changes).
  C' = C (verbatim) + the closure in S' of the frontier axioms (their types and every constant those mention, with
       definition bodies), re-indexed into C's index space ("frontier challenge"; with --pinned: a previously pinned C').
  check A = check-sound.sh C' C  {theorem_names = T, definition_names = D, permitted_axioms = A + [sorryAx if C has it]}
            -> C' agrees with the official C on every target statement and every definition it mentions.
  check B = check-sound.sh S' C' {theorem_names = T, definition_names = D, permitted_axioms = A + F}
            -> S' agrees with C' on the targets and on the frontier axioms' statements; every declaration of S' is accepted
               by the official Lean 4.36 kernel and gruszka; only A + F occur in the targets' closure.
  A and B ACCEPTED  =>  every target statement of the official challenge is derivable from the permitted axioms A plus
  the frontier hypotheses {L : type of L in C'} (C' sha256 reported). Both checks are the unchanged trusted check; this
  driver only builds their inputs (untrusted: a fault gives REJECTED / no verdict) and takes the conjunction."""
import hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, HERE)
import expfmt  # noqa: E402
from expfmt import Export, dumps, classify, expr_children, decl_members  # noqa: E402

PKG = os.environ.get("FASTVERIFY_ROOT") or os.path.dirname(os.path.dirname(HERE))
CHECK = os.path.join(PKG, "check", "sound", "check-sound.sh")
CHECK_SVC = os.path.join(PKG, "check", "sound", "check-sound-svc.sh")
SORRY = "sorryAx"
VERSION = "frontier-v2"


def prep_binary():
    """the pinned fast preparer (UNTRUSTED: scan + mint), or None -> the Python implementation below"""
    if os.environ.get("FRONTIER_NO_FAST") == "1":
        return None
    try:
        for ln in open(os.path.join(PKG, "check", "frontier", "pins.env"), encoding="utf-8"):
            f = ln.split()
            if len(f) >= 4 and f[0] == "PIN" and f[1] == "fvfrontier_prep" and os.path.isfile(f[3]) \
                    and os.access(f[3], os.X_OK) and sha256(f[3]) == f[2]:
                return f[3]
    except OSError:
        pass
    return None


def run_prep(binary, args):
    p = subprocess.run([binary] + args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env={"PATH": "/usr/bin:/bin"})
    try:
        j = json.loads(p.stdout.decode("utf-8").strip().splitlines()[-1])
    except Exception:
        j = {"error": "no JSON (exit %d): %s" % (p.returncode, p.stderr.decode("utf-8", "replace")[-500:])}
    if p.returncode != 0 or "error" in j:
        raise SystemExit("fvfrontier-prep %s failed: %s" % (args[0], j.get("error")))
    return j


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 22)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


# ---------------------------------------------------------------------------------------------------------------------
# GOAL S1(3) on the challenge's configuration. This driver judges ONLY a configuration
# whose permitted_axioms are inside S1(3) = {propext, Quot.sound, Classical.choice} (canonical Lean names, the judges'
# parser below); anything else is refused with NO verdict (exit 2). The two internal runs of the trusted check get an
# --extra-axioms list that is built HERE from internal data only (check A: sorryAx iff the official challenge has it;
# check B: exactly the frontier F) - never from a configuration file - and a plain ACCEPTED (exit 0) is only ever given
# for an empty frontier, i.e. a run without --extra-axioms (the check then holds the configuration to S1(3) itself).
# ---------------------------------------------------------------------------------------------------------------------
class Refuse(Exception):
    """no verdict (exit 2): the input is outside what this tool may judge"""


S1_AXIOMS = ("propext", "Quot.sound", "Classical.choice")   # GOAL S1(3)
# bin/fastverify options `run -- EXTRA` may forward: build / scheduling only; never the inputs, pins or deciding
# check. NOT --export-dir (run needs OUT/fv/solution.export itself: an export
# elsewhere was removed by bin/fastverify -> false REJECTED) and NOT --extra-kernel / --require-kernel (the deciding runs are
# check()'s, which do not take them: a requested extra-kernel veto would be silently skipped) - refused like any other option
RUN_EXTRA_ALLOWED = frozenset({
    "--threads", "--build", "--official-timeout", "--build-cache",
    "--parallel-checks", "--sequential-checks", "--no-confirm-build-failure", "--confirm-build-failure-full",
    "--no-build-fallback", "--require-fast", "--no-integrity-cache", "--keep-work", "--overlap", "--overlap-targeted",
    "--require-sorried-holes", "--confirm-reject",
})
TRUST_AXIOMS = ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")   # never open lemmas


# --- verbatim copy of the judges' name parser (check/sound/check-sound.sh, check/frontier/check-frontier.sh heredocs;
#     tests/frontier-axiom-scope/run.sh compares the two on a corpus): exact mirror of Lean 4 `String.toName` ---
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
            comps.append(("n", int(s[i:j])))
            i = j
        else:
            return ()
        if i == n:
            return tuple(comps)
        if s[i] == ".":
            i += 1
        else:
            return ()
# --- end of the verbatim copy ---


def q02_canon(x, what="config"):
    t = parse_lean_name(x) if isinstance(x, str) else ()
    if not t:
        raise Refuse("%s: name %r is not a Lean name" % (what, x))
    return t


Q02_S1 = frozenset(q02_canon(n) for n in S1_AXIOMS)
Q02_SORRY = q02_canon(SORRY)


def _no_dups(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate key in the configuration")
    return dict(pairs)


def _bad_const(x):
    raise ValueError("non-standard JSON constant %s" % x)


def load_json_strict(path, what="config", sha_out=None):
    """strict JSON exactly as the judges read comparator.json (UTF-8 strict, no duplicate keys, no NaN/Infinity, object);
    sha_out (a list): the sha256 of exactly the bytes parsed is appended (the pin given to the trusted check)"""
    try:
        with open(path, "rb") as f:
            raw = f.read()
        if sha_out is not None:
            sha_out.append(hashlib.sha256(raw).hexdigest())
        c = json.loads(raw.decode("utf-8", errors="strict"), object_pairs_hook=_no_dups, parse_constant=_bad_const)
    except (OSError, ValueError) as e:
        raise Refuse("%s %s is not strict JSON (%s)" % (what, path, e))
    if not isinstance(c, dict):
        raise Refuse("%s %s is not a JSON object" % (what, path))
    for k in ("theorem_names", "permitted_axioms"):
        if not isinstance(c.get(k), list) or not all(isinstance(x, str) for x in c[k]):
            raise Refuse("%s %s: %s missing or not a list of names" % (what, path, k))
    dn = c.get("definition_names")
    if dn is not None and (not isinstance(dn, list) or not all(isinstance(x, str) for x in dn)):
        raise Refuse("%s %s: definition_names is not a list of names" % (what, path))
    return c


def s1_extra(axioms, what="config"):
    """the permitted axioms outside GOAL S1(3), canonical comparison (a name that is not a Lean name: refused)"""
    return sorted(set(x for x in axioms if q02_canon(x, what) not in Q02_S1))


def load_cfg(path, sha_out=None):
    """the challenge's own configuration: strict JSON + GOAL S1(3); anything else -> Refuse (no verdict).
    sha_out (a list): the sha256 of exactly the bytes parsed is appended"""
    c = load_json_strict(path, sha_out=sha_out)
    extra = s1_extra(c["permitted_axioms"])
    if extra:
        # (short: check-frontier.sh shows the last 300 bytes of this message)
        raise Refuse("config: permitted_axioms %s outside GOAL S1(3) (propext, Quot.sound, Classical.choice)"
                     % extra)
    return c


def validate_frontier(F, T, D, A):
    """the frontier as check-frontier.sh validates it (canonical): Lean names, no duplicates, never a target / definition
    target / permitted axiom / sorryAx / compiler-trust axiom / native_decide axiom. Returns F sorted."""
    if not isinstance(F, list) or not all(isinstance(x, str) and x and "\n" not in x for x in F) or len(set(F)) != len(F):
        raise Refuse("frontier list malformed")
    # (same order and wording as check-frontier.sh: string checks first, then the canonical ones)
    bad = sorted(set(F) & (set(T) | set(D) | set(A) | {SORRY}))
    if bad:
        raise Refuse("frontier contains a target / definition target / permitted axiom / sorryAx: %s" % bad)
    trust = sorted(n for n in F if n in TRUST_AXIOMS or "._native.native_decide.ax_" in n
                   or n.startswith("_native.native_decide.ax_"))
    if trust:
        raise Refuse("frontier contains a compiler / native_decide trust axiom: %s" % trust)
    canon = [q02_canon(n, "frontier") for n in F]
    if len(set(canon)) != len(canon):
        raise Refuse("frontier list contains duplicate names (canonical)")
    forb = set(q02_canon(n) for n in list(T) + list(D) + list(A) + [SORRY] + list(TRUST_AXIOMS))

    def native_ax(t):
        return any(t[i] == ("s", "_native") and t[i + 1] == ("s", "native_decide") and t[i + 2][0] == "s"
                   and t[i + 2][1].startswith("ax_") for i in range(len(t) - 2))
    bad = sorted(n for n, t in zip(F, canon) if t in forb or native_ax(t))
    if bad:
        raise Refuse("frontier contains a target / definition target / permitted axiom / sorryAx / trust axiom "
                     "(canonical): %s" % bad)
    return sorted(F)


FRONTIER_AXIOM_SUFFIX = ("s", "_fv_frontier_axiom")


def check_listed(F, listed, axioms=()):
    """an explicit (--frontier NAME,...|@FILE) or pinned frontier list is a contract on EXACT canonical
    Lean names, as check-frontier.sh enforces it in trusted code: every member of F - an open lemma L as its redirect axiom
    L._fv_frontier_axiom or as L itself - must be listed exactly (a private declaration only as _private.<module>.0.<x>,
    never by its source spelling); a declared --axioms name may be in F as itself. Otherwise no verdict (exit 2)."""
    # an entry ending in the reserved redirect suffix names nothing (only L itself allows the open lemma L)
    allowed = set(t for t in (parse_lean_name(x) for x in listed) if t and t[-1] != FRONTIER_AXIOM_SUFFIX)
    ax = set(t for t in (parse_lean_name(x) for x in axioms) if t and t[-1] != FRONTIER_AXIOM_SUFFIX)
    out = []
    for n in F:
        t = parse_lean_name(n)
        if not (t and (t in allowed or t in ax or (len(t) > 1 and t[-1] == FRONTIER_AXIOM_SUFFIX and t[:-1] in allowed))):
            out.append(n)
    if out:
        raise Refuse("frontier outside the allowed / pinned list (exact canonical names; a private declaration is listed "
                     "as _private.<module>.0.<name>): %s" % sorted(out)[:20])


def copy_pinned(src, dst, pin, what, opt):
    """read `src` ONCE into the fresh private file `dst` (0400, in a 0700 dir), hashing the bytes
    copied; the copy - never `src` again - is what is used afterwards. sha256 != pin, or an unreadable / non-regular
    source: Refuse (exit 2). Returns dst."""
    import stat as _st
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    os.chmod(os.path.dirname(dst), 0o700)
    tmp = dst + ".tmp.%d" % os.getpid()
    h = hashlib.sha256()
    try:
        fd = os.open(src, os.O_RDONLY | os.O_NONBLOCK | os.O_CLOEXEC)
        if not _st.S_ISREG(os.fstat(fd).st_mode):
            os.close(fd)
            raise Refuse("%s %s is not a regular file" % (what, src))
        with os.fdopen(fd, "rb") as f:
            out_fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
            with os.fdopen(out_fd, "wb") as g:
                while True:
                    b = f.read(1 << 22)
                    if not b:
                        break
                    h.update(b)
                    g.write(b)
    except OSError as e:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise Refuse("cannot read %s %s: %s" % (what, src, e))
    if h.hexdigest() != pin:
        os.unlink(tmp)
        raise Refuse("%s sha256 %s differs from %s %s" % (what, h.hexdigest(), opt, pin))
    os.chmod(tmp, 0o400)
    os.replace(tmp, dst)
    return dst


def clear_outputs(out, names):
    """remove this tool's own outputs of an earlier run in OUT (names relative to OUT) so
    every artefact judged afterwards was produced by THIS run; a symlink / file is unlinked, a directory removed without
    following links (write bits restored first). Failure: Refuse (exit 2)."""
    def _onerr(fn, path, _exc):
        try:
            os.chmod(os.path.dirname(path), 0o700)
            if os.path.isdir(path) and not os.path.islink(path):
                os.chmod(path, 0o700)
            fn(path)
        except OSError as e:
            raise Refuse("cannot clear the earlier output %s: %s" % (path, e))
    for n in names:
        q = os.path.join(out, n)
        try:
            if os.path.islink(q) or (os.path.lexists(q) and not os.path.isdir(q)):
                os.unlink(q)
            elif os.path.isdir(q):
                shutil.rmtree(q, onerror=_onerr)
        except OSError as e:
            raise Refuse("cannot clear the earlier output %s: %s" % (q, e))
        if os.path.lexists(q):
            raise Refuse("cannot clear the earlier output %s" % q)


def challenge_has_sorry(challenge):
    """does the official challenge export name sorryAx (the same streaming test prepare uses for check A's config)"""
    return subprocess.run(["grep", "-q", "-F", '"pre":0,"str":"sorryAx"}', challenge]).returncode == 0


# ---------------------------------------------------------------------------------------------------------------------
# scan: which open lemmas does the targets' closure depend on (untrusted analysis; the checks decide)
# ---------------------------------------------------------------------------------------------------------------------
def scan(ex, cfg, frontier=None, extra_axioms=()):
    """Walk the targets' closure as checkAxioms does. A theorem (not a target) whose own value contains sorryAx is a
    frontier lemma (with frontier=None: every such theorem met; with an explicit frontier: only the listed ones); its
    value is not followed. Returns a report dict."""
    T = list(cfg["theorem_names"])
    D = list(cfg.get("definition_names") or [])
    A = set(cfg["permitted_axioms"])
    listed = None if frontier is None else set(frontier)
    allowed_ax = set(extra_axioms)
    has_sorry = {}

    def value_has_sorry(name):
        if name not in has_sorry:
            m = ex.member(name)
            ok = False
            if m and m[0] in ("thm", "def", "opaque"):
                ok = SORRY in ex.expr_consts([m[1]["value"]])
            has_sorry[name] = ok
        return has_sorry[name]

    frontier_found, sorry_defs, sorry_targets, other_axioms, missing = [], [], [], [], []
    seen = set()
    stack = [(n, None) for n in reversed(T + D)]
    parent = {}
    while stack:
        name, via = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        parent[name] = via
        m = ex.member(name)
        if m is None:
            missing.append(name)
            continue
        mk, mb, _ = m
        follow_value = True
        if mk == "axiom":
            if name not in A and name != SORRY:
                (frontier_found if name in allowed_ax else other_axioms).append(name)
        elif mk == "thm" and name not in T and (listed is None or name in listed) and value_has_sorry(name):
            frontier_found.append(name)
            follow_value = False
        elif mk == "thm" and name in T and value_has_sorry(name):
            sorry_targets.append(name)
        elif mk in ("def", "opaque") and value_has_sorry(name):
            sorry_defs.append(name)
        refs = ex.member_refs(name, follow_value=follow_value)
        for r in sorted(refs or ()):
            if r not in seen:
                stack.append((r, name))
    if listed is not None:
        # listed lemmas that are already proved (or not in the closure): not axiomatized, reported as closed
        closed = sorted(listed - set(frontier_found))
    else:
        closed = []

    def path(n):
        p = []
        while n is not None and len(p) < 12:
            p.append(n)
            n = parent.get(n)
        return list(reversed(p))
    sorry_reached = SORRY in seen
    return {
        "targets": T, "definition_targets": D,
        "frontier": sorted(set(frontier_found)),
        "frontier_closed": closed,
        "sorry_in_targets": sorted(sorry_targets),
        "sorry_in_definitions": [{"name": d, "path": path(d)} for d in sorted(sorry_defs)],
        "other_axioms": [{"name": a, "path": path(a)} for a in sorted(other_axioms)],
        "missing": sorted(missing),
        "closure_size": len(seen),
        "sorry_reached_outside_frontier": sorry_reached,
        "blockers": bool(sorry_targets or sorry_defs or other_axioms or missing),
    }


# ---------------------------------------------------------------------------------------------------------------------
# pretty printer (informational only: the authoritative statements are the records of the frontier challenge C')
# ---------------------------------------------------------------------------------------------------------------------
def pp_level(ex, idx, depth=0):
    lv = ex.levels.get(idx)
    if lv is None or depth > 50:
        return "?"
    k = lv[0]
    if k == "zero":
        return "0"
    if k == "succ":
        n, cur = 1, lv[1]
        while ex.levels.get(cur, ("?",))[0] == "succ" and n < 64:
            n += 1
            cur = ex.levels[cur][1]
        base = pp_level(ex, cur, depth + 1)
        return str(n) if base == "0" else "%s+%d" % (base, n)
    if k in ("max", "imax"):
        a, b = lv[1]
        return "%s (%s) (%s)" % (k, pp_level(ex, a, depth + 1), pp_level(ex, b, depth + 1))
    if k == "param":
        return ex.name_str(lv[1])
    return "?"


def pp_expr(ex, idx, binders=None, depth=0, budget=None):
    """a compact, Lean-like rendering (no notation, no implicit-argument hiding beyond binders)."""
    if budget is None:
        budget = [4000]
    binders = binders or []
    budget[0] -= 1
    if budget[0] < 0 or depth > 200:
        return "…"
    node = ex.exprs.get(idx)
    if node is None:
        return "?"
    k, b = node
    if k == "bvar":
        i = b
        return binders[-1 - i] if i < len(binders) else "#%d" % i
    if k == "sort":
        lv = pp_level(ex, b)
        return "Prop" if lv == "0" else ("Type" if lv == "1" else "Sort (%s)" % lv)
    if k == "const":
        return ex.name_str(b["name"])
    if k == "app":
        fn, args = idx, []
        while ex.exprs.get(fn, ("",))[0] == "app" and len(args) < 64:
            args.append(ex.exprs[fn][1]["arg"])
            fn = ex.exprs[fn][1]["fn"]
        args.reverse()
        parts = [pp_expr(ex, fn, binders, depth + 1, budget)] + [
            _paren(pp_expr(ex, a, binders, depth + 1, budget)) for a in args]
        return " ".join(parts)
    if k in ("lam", "forallE"):
        nm = ex.name_str(b["name"]) or "x"
        if "_hyg" in nm or nm.startswith("_"):
            nm = "x%d" % len(binders)
        ty = pp_expr(ex, b["type"], binders, depth + 1, budget)
        body = pp_expr(ex, b["body"], binders + [nm], depth + 1, budget)
        bi = b.get("binderInfo", "default")
        lp, rp = {"implicit": ("{", "}"), "strictImplicit": ("⦃", "⦄"), "instImplicit": ("[", "]")}.get(bi, ("(", ")"))
        if k == "forallE" and bi == "default" and not _uses_bvar0(ex, b["body"]):
            return "%s → %s" % (_paren(ty), body)
        return "%s %s%s : %s%s, %s" % ("fun" if k == "lam" else "∀", lp, nm, ty, rp, body)
    if k == "letE":
        nm = ex.name_str(b["name"]) or "x"
        return "let %s := %s; %s" % (nm, pp_expr(ex, b["value"], binders, depth + 1, budget),
                                     pp_expr(ex, b["body"], binders + [nm], depth + 1, budget))
    if k == "proj":
        return "%s.%d" % (_paren(pp_expr(ex, b["struct"], binders, depth + 1, budget)), b["idx"] + 1)
    if k == "natVal":
        return str(b)
    if k == "strVal":
        return json.dumps(b, ensure_ascii=False)
    if k == "mdata":
        return pp_expr(ex, b["expr"], binders, depth + 1, budget)
    return "?"


def _paren(s):
    return s if (" " not in s or s[0] in "(⟨[{") else "(" + s + ")"


def _uses_bvar0(ex, idx, limit=20000):
    """does the body refer to its innermost binder (loose bvar 0)? (bounded search; True when unsure)"""
    stack = [(idx, 0)]
    seen = set()
    while stack:
        e, d = stack.pop()
        if (e, d) in seen:
            continue
        seen.add((e, d))
        if len(seen) > limit:
            return True
        node = ex.exprs.get(e)
        if node is None:
            return True
        k, b = node
        if k == "bvar":
            if b == d:
                return True
            continue
        if k in ("lam", "forallE"):
            stack.append((b["type"], d))
            stack.append((b["body"], d + 1))
        elif k == "letE":
            stack.append((b["type"], d))
            stack.append((b["value"], d))
            stack.append((b["body"], d + 1))
        else:
            for c in expr_children(k, b):
                stack.append((c, d))
    return False


# ---------------------------------------------------------------------------------------------------------------------
# rewrite S -> S' (frontier theorems become axioms, in place)
# ---------------------------------------------------------------------------------------------------------------------
def rewrite(src, dst, frontier):
    """stream src to dst; every thm record whose name is in frontier becomes an axiom record (same name, levelParams,
    type). Returns the set of names converted."""
    want = set(frontier)
    names = {0: ""}
    done = set()
    with open(src, "rb") as f, open(dst, "wb") as g:
        for raw in f:
            if raw.startswith(b'{"in":'):
                o = json.loads(raw)
                if "str" in o:
                    names[o["in"]] = (o["str"]["pre"], expfmt._esc(o["str"]["str"]))
                else:
                    names[o["in"]] = (o["num"]["pre"], str(o["num"]["i"]))
            elif raw.startswith(b'{"thm":'):
                o = json.loads(raw)["thm"]
                nm = _name(names, o["name"])
                if nm in want:
                    if nm in done:
                        raise SystemExit("rewrite: duplicate theorem %s" % nm)
                    rec = {"axiom": {"isUnsafe": False, "levelParams": o["levelParams"], "name": o["name"],
                                     "type": o["type"]}}
                    g.write(dumps(rec).encode("utf-8") + b"\n")
                    done.add(nm)
                    continue
            g.write(raw)
    return done


def _name(names, idx):
    parts = []
    while idx != 0:
        pre, s = names[idx]
        parts.append(s)
        idx = pre
    return ".".join(reversed(parts))


# ---------------------------------------------------------------------------------------------------------------------
# mint C' = C + closure_{S'}(frontier), re-indexed into C's index space
# ---------------------------------------------------------------------------------------------------------------------
def mint(c_path, sp, frontier, dst):
    """sp = Export of S'. Writes C' to dst. Returns stats."""
    C = Export(c_path)
    # constants to append: closure of the frontier axioms in S', stopping at constants C already has
    need, stack = set(), list(frontier)
    while stack:
        n = stack.pop()
        if n in need or n in C.by_name:
            continue
        m = sp.member(n)
        if m is None:
            raise SystemExit("mint: constant %s not in the solution export" % n)
        need.add(n)
        # whole declaration blocks (inductives) go together
        kind, body, _ = sp.decls[m[2]]
        for nidx, _, _ in decl_members(kind, body):
            stack.append(sp.name_str(nidx))
        stack.extend(sp.member_refs(n) or ())
    positions = sorted({sp.by_name[n] for n in need})
    # re-indexing maps S' index -> C' index
    name_key = {}
    for idx, v in C.names.items():
        if v is not None:
            name_key[(v[0], v[1], v[2])] = idx
    level_key = {}
    for idx, v in C.levels.items():
        if v[0] != "zero":
            level_key[(v[0], json.dumps(v[1]))] = idx
    nmap, lmap, emap = {0: 0}, {0: 0}, {}
    out = []
    nxt = {"in": C.max_in + 1, "il": C.max_il + 1, "ie": C.max_ie + 1}

    def mname(i):
        if i in nmap:
            return nmap[i]
        # iterative over the prefix chain
        chain = []
        j = i
        while j not in nmap:
            chain.append(j)
            j = sp.names[j][1]
        for j in reversed(chain):
            kind, pre, val = sp.names[j]
            key = (kind, nmap[pre], val)
            if key in name_key:
                nmap[j] = name_key[key]
            else:
                k = nxt["in"]
                nxt["in"] += 1
                body = {"pre": nmap[pre], "str": val} if kind == "str" else {"pre": nmap[pre], "i": val}
                out.append({"in": k, kind: body})
                name_key[key] = k
                nmap[j] = k
        return nmap[i]

    def mlevel(i):
        if i in lmap:
            return lmap[i]
        kind, payload = sp.levels[i]
        if kind == "succ":
            p = mlevel(payload)
        elif kind in ("max", "imax"):
            p = [mlevel(payload[0]), mlevel(payload[1])]
        elif kind == "param":
            p = mname(payload)
        else:
            raise SystemExit("mint: bad level")
        key = (kind, json.dumps(p))
        if key in level_key:
            lmap[i] = level_key[key]
        else:
            k = nxt["il"]
            nxt["il"] += 1
            out.append({"il": k, kind: p})
            level_key[key] = k
            lmap[i] = k
        return lmap[i]

    def mexpr(root):
        # iterative post-order so that children are emitted before parents
        stack = [(root, False)]
        while stack:
            e, ready = stack.pop()
            if e in emap:
                continue
            kind, body = sp.exprs[e]
            if not ready:
                stack.append((e, True))
                for c in expr_children(kind, body):
                    if c not in emap:
                        stack.append((c, False))
                continue
            if kind == "bvar":
                nb = body
            elif kind == "sort":
                nb = mlevel(body)
            elif kind == "const":
                nb = {"name": mname(body["name"]), "us": [mlevel(u) for u in body["us"]]}
            elif kind == "app":
                nb = {"fn": emap[body["fn"]], "arg": emap[body["arg"]]}
            elif kind in ("lam", "forallE"):
                nb = {"name": mname(body["name"]), "type": emap[body["type"]], "body": emap[body["body"]],
                      "binderInfo": body["binderInfo"]}
            elif kind == "letE":
                nb = {"name": mname(body["name"]), "type": emap[body["type"]], "value": emap[body["value"]],
                      "body": emap[body["body"]], "nondep": body["nondep"]}
            elif kind == "proj":
                nb = {"typeName": mname(body["typeName"]), "idx": body["idx"], "struct": emap[body["struct"]]}
            elif kind in ("natVal", "strVal"):
                nb = body
            elif kind == "mdata":
                nb = {"expr": emap[body["expr"]], "data": body["data"]}
            else:
                raise SystemExit("mint: bad expression kind %s" % kind)
            k = nxt["ie"]
            nxt["ie"] += 1
            out.append({"ie": k, kind: nb})
            emap[e] = k
        return emap[root]

    def mdecl_member(mk, mb):
        nb = dict(mb)
        nb["name"] = mname(mb["name"])
        nb["levelParams"] = [mname(x) for x in mb["levelParams"]]
        nb["type"] = mexpr(mb["type"])
        if "value" in mb:
            nb["value"] = mexpr(mb["value"])
        if "all" in mb:
            nb["all"] = [mname(x) for x in mb["all"]]
        if mk == "inductType":
            nb["ctors"] = [mname(x) for x in mb["ctors"]]
        if mk == "ctor":
            nb["induct"] = mname(mb["induct"])
        if mk == "rec":
            nb["rules"] = [{"ctor": mname(r["ctor"]), "nfields": r["nfields"], "rhs": mexpr(r["rhs"])}
                           for r in mb["rules"]]
        return nb

    decl_out = []
    for pos in positions:
        kind, body, _ = sp.decls[pos]
        if kind == "inductive":
            nb = {"types": [mdecl_member("inductType", t) for t in body["types"]],
                  "ctors": [mdecl_member("ctor", c) for c in body["ctors"]],
                  "recs": [mdecl_member("rec", r) for r in body["recs"]]}
        else:
            nb = mdecl_member(kind, body)
        out.append({kind: nb})
        decl_out.append(kind)
    with open(c_path, "rb") as f, open(dst + ".tmp", "wb") as g:
        shutil.copyfileobj(f, g)
        for o in out:
            g.write(dumps(o).encode("utf-8") + b"\n")
    os.replace(dst + ".tmp", dst)
    return {"appended_declarations": len(decl_out), "appended_records": len(out), "constants": sorted(need)}


# ---------------------------------------------------------------------------------------------------------------------
# prepare / check / verify
# ---------------------------------------------------------------------------------------------------------------------
def read_name_list(path):
    """a name-list file read exactly as check-frontier.sh's trusted step and fvfrontier-prep's readNames read it:
    split at LF only, each line trimmed of ASCII space / tab / CR / LF (Lean's String.trimAscii), empty and '#' lines
    (after trimming) skipped"""
    with open(path, "rb") as f:
        data = f.read().decode("utf-8", errors="strict")
    out = []
    for ln in data.split("\n"):
        t = ln.strip(" \t\r\n")
        if t and not t.startswith("#"):
            out.append(t)
    return out


def parse_frontier(arg):
    if arg is None or arg == "auto":
        return None
    if arg.startswith("@"):
        return read_name_list(arg[1:])
    return [x for x in arg.split(",") if x]


def prepare(export, challenge, cfgp, outdir, frontier_arg="auto", axioms=(), pinned=None, log=print, probe=None):
    t0 = time.time()
    for _p, _w in ((export, "solution export"), (challenge, "challenge export")):
        if not os.path.isfile(_p):
            raise Refuse("%s %s is not a readable file" % (_w, _p))
    _cfg_sha = []
    cfg = load_cfg(cfgp, _cfg_sha)   # GOAL S1(3) before anything is written; + sha256 of THESE bytes
    os.makedirs(outdir, exist_ok=True)
    os.chmod(outdir, 0o700)
    T = list(cfg["theorem_names"])
    D = list(cfg.get("definition_names") or [])
    A = list(cfg["permitted_axioms"])
    pin = None
    if pinned:
        pin = json.load(open(os.path.join(pinned, "frontier.json"), encoding="utf-8"))
        if pin.get("challenge_sha256") != sha256(challenge):
            raise Refuse("pinned frontier was minted against another challenge export")
    listed = parse_frontier(frontier_arg)
    # the caller's lists themselves: never a target / permitted axiom / sorryAx / trust axiom (exit 2)
    if listed is not None:
        validate_frontier(sorted(set(listed)), T, D, A)
    if axioms:
        validate_frontier(sorted(set(axioms)), T, D, A)
    SUF = "._fv_frontier_axiom"
    pin_lemmas = None
    if pin is not None:
        pin_lemmas = list(pin.get("frontier_lemmas") or [n[:-len(SUF)] if n.endswith(SUF) else n for n in pin["frontier"]])
    if listed is None and pin is not None:
        listed = list(pin_lemmas)    # auto + pinned: only the pinned lemmas may stay open
    fast = prep_binary()
    fastprep = None
    if fast:   # ONE fast pass (ccmp's reader, Lean): scan + rewrite + mint, S and C read once each
        args = ["prepare", cfgp, export, challenge, outdir]
        if probe:
            args += ["--probe", probe]
        if listed is not None:
            lf = os.path.join(outdir, "frontier.list")
            open(lf, "w", encoding="utf-8").write("".join(n + "\n" for n in listed))
            args += ["--list", lf]
        if axioms:
            af = os.path.join(outdir, "axioms.list")
            open(af, "w", encoding="utf-8").write("".join(n + "\n" for n in axioms))
            args += ["--axioms", af]
        fastprep = run_prep(fast, args)
        rep = fastprep["scan"]
        S = None
        t_parse = time.time() - t0
        F_thm = list(rep["frontier"])
        F_ax = list(rep.get("frontier_axioms") or [])
        rep["frontier"] = sorted(set(F_thm) | set(F_ax))
        # REDIRECT (default of the fast preparer): the open lemmas stay theorems whose value is a fresh axiom
        # L._fv_frontier_axiom; those axioms are what check B permits
        lemma_of = dict(fastprep.get("frontier_lemma_of") or {})
        permitted = list(fastprep.get("permitted_frontier") or rep["frontier"])
    else:
        S = Export(export)
        t_parse = time.time() - t0
        rep = scan(S, cfg, listed, axioms)
        F_thm = [n for n in rep["frontier"] if (S.member(n) or ("",))[0] == "thm"]
        F_ax = [n for n in rep["frontier"] if (S.member(n) or ("",))[0] == "axiom"]
    validate_frontier(sorted(set(rep["frontier"])), T, D, A)   # as check-frontier.sh (string + canonical): exit 2
    if pin is not None:
        extra = sorted(set(rep["frontier"]) - set(pin_lemmas))
        rep["outside_pinned_frontier"] = extra
    F = sorted(set(F_thm) | set(F_ax))
    if fastprep is not None:
        F = sorted(set(permitted))
    else:
        lemma_of = {}
    if listed is not None:   # exact names, also when the (untrusted) preparer matched more loosely
        check_listed(F, listed, axioms)
    sp_path = os.path.join(outdir, "solution.frontier.export")
    t1 = time.time()
    if fastprep is not None:
        pass   # S' written by fvfrontier-prep prepare (it checked that every frontier theorem was converted)
    elif F_thm:
        conv = rewrite(export, sp_path, F_thm)
        if conv != set(F_thm):
            raise Refuse("rewrite: not converted: %s" % sorted(set(F_thm) - conv))
    else:
        shutil.copyfile(export, sp_path)
    t_rewrite = time.time() - t1
    fdir = os.path.join(outdir, "frontier")
    os.makedirs(fdir, exist_ok=True)
    t2 = time.time()
    if pin is not None:
        shutil.copyfile(os.path.join(pinned, "challenge.export"), os.path.join(fdir, "challenge.export"))
        if sha256(os.path.join(fdir, "challenge.export")) != pin["frontier_challenge_sha256"]:
            raise Refuse("pinned frontier challenge export does not match its recorded sha256")
        mstats = {"pinned": pinned}
        sp = None
    else:
        if fastprep is not None:
            mstats = fastprep["mint"]   # C' written by fvfrontier-prep prepare
        elif F:
            sp = Export(sp_path)
            mstats = mint(challenge, sp, F, os.path.join(fdir, "challenge.export"))
        else:
            shutil.copyfile(challenge, os.path.join(fdir, "challenge.export"))
            mstats = {"appended_declarations": 0}
    t_mint = time.time() - t2
    # configs: B (main) and A (frontier challenge vs official challenge)
    cfgB = dict(cfg)
    cfgB["permitted_axioms"] = A + [n for n in F if n not in A]
    C = None
    c_has_sorry = subprocess.run(["grep", "-q", "-F", '"pre":0,"str":"sorryAx"}', challenge]).returncode == 0
    cfgA = dict(cfg)
    cfgA["permitted_axioms"] = A + ([SORRY] if c_has_sorry else [])
    for k in ("external_kernels", "enable_nanoda"):
        cfgA.pop(k, None)
    # written from bytes whose sha256 is kept in memory: check() (run / verify) requires the files it judges to be these
    _cfg_bytes = {"main": json.dumps(cfgB, indent=1).encode("utf-8"), "compare": json.dumps(cfgA, indent=1).encode("utf-8")}
    for _k, _n in (("main", "comparator.frontier.json"), ("compare", "comparator.compare.json")):
        with open(os.path.join(outdir, _n), "wb") as _f:
            _f.write(_cfg_bytes[_k])
    cprime = os.path.join(fdir, "challenge.export")
    # informational statements of the frontier (from C')
    stm = {}
    if F and fast:   # printed by Lean's Expr printer from the solution's records (= C' records by construction)
        ax_of = {l: a for a, l in lemma_of.items()}
        for e in rep.get("statements") or []:
            t = e.get("type") or ""
            lp = e.get("level_params") or []
            key = ax_of.get(e["name"], e["name"])
            stm[key] = {"lemma": e["name"], "kind": e.get("kind"), "levelParams": lp, "type": t,
                        "type_sha256": hashlib.sha256(json.dumps([lp, t], ensure_ascii=False).encode("utf-8")).hexdigest(),
                        "used_by": e.get("used_by")}
        for n in F_ax:
            stm.setdefault(n, {"lemma": n, "kind": "axiom", "type": None})
        # sorry abstraction: open subgoals inside a target's or a definition's value, closed over their local context
        for ab in rep.get("abstracted") or []:
            for e in ab.get("lemmas") or []:
                t = e.get("type") or ""
                stm[e["name"] + "._fv_frontier_axiom"] = {
                    "lemma": e["name"], "kind": "sorry inside %s (abstracted with its local context)" % ab.get("decl"),
                    "levelParams": [], "type": t, "in_declaration": ab.get("decl"),
                    "type_sha256": hashlib.sha256(json.dumps([[], t], ensure_ascii=False).encode("utf-8")).hexdigest()}
    elif F:
        CP = Export(cprime)
        for n in F:
            m = CP.member(n)
            if m:
                lp = [CP.name_str(x) for x in m[1]["levelParams"]]
                t = pp_expr(CP, m[1]["type"])
                stm[n] = {"kind": m[0], "levelParams": lp, "type": t,
                          "type_sha256": hashlib.sha256(json.dumps([lp, t], ensure_ascii=False).encode("utf-8")).hexdigest()}
            else:
                stm[n] = {"kind": None, "type": None}
    info = {
        "version": VERSION, "solution_export": os.path.abspath(export), "solution_sha256": sha256(export),
        "challenge_export": os.path.abspath(challenge), "challenge_sha256": sha256(challenge),
        # the sha256 of exactly the bytes parsed above - the derived configurations come
        # from that parse - never a second read of the file; check() compares it with the caller's pin
        "comparator_config": os.path.abspath(cfgp), "comparator_sha256": _cfg_sha[0],
        "pinned_config": cfg,   # the parse of exactly those bytes; check() compares the derived configs with it
        "derived_config_sha256": {k: hashlib.sha256(v).hexdigest() for k, v in _cfg_bytes.items()},
        "frontier_mode": "pinned" if pin else ("auto" if frontier_arg in (None, "auto") else "listed"),
        "rewrite": "redirect" if (fastprep or {}).get("redirect") else "in-place", "frontier_lemma_of": lemma_of,
        "frontier": F, "frontier_theorems": F_thm, "frontier_axioms": F_ax, "statements": stm,
        "frontier_challenge_sha256": sha256(cprime), "scan": rep, "mint": mstats,
        "seconds": {"parse": round(t_parse, 3), "rewrite": round(t_rewrite, 3), "mint": round(t_mint, 3),
                    "total": round(time.time() - t0, 3)},
        "fast_preparer_ms": (fastprep or {}).get("ms"),
    }
    json.dump(info, open(os.path.join(outdir, "frontier.json"), "w"), indent=1, ensure_ascii=False)
    return info


def run_check(e, c, cfgp, threads, logf, jsonf, svc=None, extra=(), pins=None):
    """one run of the unchanged trusted check. `extra` is the exact internal --extra-axioms list of this run
    (check A: [sorryAx] or []; check B: the frontier F) computed by check() - it is never derived from the config file.
    An empty list passes no --extra-axioms: the check then holds the configuration to GOAL S1(3) itself."""
    cmd = [CHECK_SVC if svc else CHECK, e, c, cfgp, "--threads", str(threads), "--json", jsonf, "--log", logf]
    if svc:
        cmd += ["--integrity-cache", svc]
    extra = sorted(set(extra))
    if extra:
        xf = cfgp + ".extra-axioms"
        with open(xf, "w", encoding="utf-8") as f:
            f.write("".join(n + "\n" for n in extra))
        cmd += ["--extra-axioms", xf]
    if pins:   # the trusted check verifies its private copies against these pins
        cmd += ["--challenge-sha256", pins[0], "--comparator-sha256", pins[1]]
    t0 = time.time()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env={"PATH": "/usr/bin:/bin"})
    _CHILDREN.append(p)
    return p, t0


def check_configs(outdir, info):
    """re-derive and validate the two internal configurations from OUTDIR (written by prepare, but `check OUTDIR`
    may get any directory): check A's permitted axioms = A (inside GOAL S1(3)) + [sorryAx iff the official challenge has
    it]; check B's = A + F exactly (canonical); same targets in both. Returns (F, extra_A, extra_B) or raises Refuse."""
    shas = []   # sha256 of the bytes validated here = the --comparator-sha256 pins of the two trusted runs
    cfgA = load_json_strict(os.path.join(outdir, "comparator.compare.json"), "compare config", shas)
    cfgB = load_json_strict(os.path.join(outdir, "comparator.frontier.json"), "main config", shas)
    for k in ("theorem_names", "definition_names"):
        if (cfgA.get(k) or []) != (cfgB.get(k) or []):
            raise Refuse("the two internal configurations disagree on %s" % k)
    for k in set(cfgA) | set(cfgB):
        if k not in ("permitted_axioms", "external_kernels", "enable_nanoda") and cfgA.get(k) != cfgB.get(k):
            raise Refuse("the two internal configurations disagree on %s" % k)
    csorry = challenge_has_sorry(info["challenge_export"])
    A = [x for x in cfgA["permitted_axioms"] if q02_canon(x) != Q02_SORRY]
    if s1_extra(A):
        raise Refuse("compare config: permitted_axioms %s outside GOAL S1(3)" % s1_extra(A))
    if len(A) != len(cfgA["permitted_axioms"]) and not csorry:
        raise Refuse("compare config permits sorryAx but the official challenge export has none")
    F = validate_frontier(info["frontier"], cfgB["theorem_names"], cfgB.get("definition_names") or [], A)
    want = set(q02_canon(x) for x in A) | set(q02_canon(x) for x in F)
    got = set(q02_canon(x) for x in cfgB["permitted_axioms"])
    if got != want:
        raise Refuse("main config permits %s, expected exactly A + F" % sorted(cfgB["permitted_axioms"]))
    extra_A = [SORRY] if len(A) != len(cfgA["permitted_axioms"]) else []
    check_configs.shas = tuple(shas)   # read by check(); the 3-tuple return value is kept for other callers
    check_configs.cfgs = (cfgA, cfgB)
    return F, extra_A, list(F)


def check(outdir, threads=8, svc=None, pins=None, info=None):
    """run / verify pass prepare()'s IN-MEMORY info: nothing prepare() measured is re-read from OUTDIR"""
    mem = info is not None
    try:
        if not mem:
            info = json.load(open(os.path.join(outdir, "frontier.json"), encoding="utf-8"))
        if not isinstance(info, dict) or not all(k in info for k in ("frontier", "challenge_export", "challenge_sha256",
                                                                     "frontier_challenge_sha256", "scan")):
            raise ValueError("missing fields")
    except (OSError, ValueError) as e:
        raise Refuse("OUTDIR/frontier.json unreadable or malformed (%s)" % e)
    F, extra_A, extra_B = check_configs(outdir, info)   # Refuse -> no verdict (main)
    sha_cmp, sha_main = check_configs.shas
    if mem:
        # (defence in depth) the derived configurations judged are exactly the ones prepare() wrote,
        # and every key except permitted_axioms equals the pinned comparator's (as parsed from the hashed bytes)
        want = info.get("derived_config_sha256") or {}
        if (sha_cmp, sha_main) != (want.get("compare"), want.get("main")):
            raise Refuse("the internal configurations changed after prepare (OUTDIR modified during the run)")
        base = info.get("pinned_config") or {}
        cA, cB = check_configs.cfgs
        for cfgX, skip in ((cB, {"permitted_axioms"}), (cA, {"permitted_axioms", "external_kernels", "enable_nanoda"})):
            for k in (set(cfgX) | set(base)) - skip:
                if cfgX.get(k) != base.get(k):
                    raise Refuse("internal configuration differs from the pinned comparator on %s" % k)
    if pins is not None and (info["challenge_sha256"] != pins[0] or info.get("comparator_sha256") != pins[1]):
        # run / verify: what prepare measured must BE the caller's pins
        raise Refuse("the prepared inputs are not the pinned ones (challenge %s, comparator %s)"
                     % (info["challenge_sha256"], info.get("comparator_sha256")))
    cprime = os.path.join(outdir, "frontier", "challenge.export")
    sp = os.path.join(outdir, "solution.frontier.export")
    res = {}
    t0 = time.time()
    if info["scan"].get("outside_pinned_frontier"):
        pass   # still run the trusted check: it decides (an open lemma outside the pinned frontier -> REJECTED)
    # check A (small: C' vs official C) and check B (main) run concurrently; B gets most threads
    ta = max(1, min(8, threads // 8)) if threads > 2 else 1
    tb = max(1, threads - ta) if threads > 2 else threads
    jobs = {}
    clear_outputs(outdir, ["check_compare.json", "check_main.json", "check_compare.log", "check_main.log"])   # THIS run's JSON only
    if F:
        jobs["compare"] = run_check(cprime, info["challenge_export"], os.path.join(outdir, "comparator.compare.json"), ta,
                                    os.path.join(outdir, "check_compare.log"), os.path.join(outdir, "check_compare.json"),
                                    svc, extra=extra_A, pins=(info["challenge_sha256"], sha_cmp))
    # no open lemma: the main check judges S' against the OFFICIAL challenge export (as check-frontier.sh) -
    # C' (minted or a --pinned copy) is only ever trusted after check A compared it with the official challenge
    jobs["main"] = run_check(sp, cprime if F else info["challenge_export"], os.path.join(outdir, "comparator.frontier.json"),
                             tb, os.path.join(outdir, "check_main.log"), os.path.join(outdir, "check_main.json"), svc,
                             extra=extra_B, pins=(info["frontier_challenge_sha256"] if F else info["challenge_sha256"], sha_main))
    for k, (p, ts) in jobs.items():
        p.communicate()
        try:
            j = json.load(open(os.path.join(outdir, "check_%s.json" % k)))
        except Exception:
            j = {"verdict": "DECLINED", "exit": 2, "reason": "no JSON from check-sound"}
        j["rc"] = p.returncode
        j["seconds"] = round(time.time() - ts, 3)
        res[k] = j
    # the challenge export given to check A must still be the pinned official one (the caller pinned it)
    ok_c = sha256(info["challenge_export"]) == info["challenge_sha256"]
    ok_cp = sha256(cprime) == info["frontier_challenge_sha256"]
    try:   # the configuration the run was prepared from is unchanged too (when prepare recorded it)
        ok_c = ok_c and ("comparator_sha256" not in info or sha256(info["comparator_config"]) == info["comparator_sha256"])
    except OSError:
        ok_c = False
    main, comp = res["main"], res.get("compare")
    # a plain ACCEPTED never rests on extra axioms: no frontier, no --extra-axioms given to the main run, and the
    # trusted check itself reports none (extra_permitted_axioms [] / absent); anything else is no verdict
    main_xax = main.get("extra_permitted_axioms")
    if not (ok_c and ok_cp):
        verdict, ex, why = "NO_VERDICT", 2, "an input changed during the check"
    elif main["rc"] == 0 and main.get("verdict") == "ACCEPTED" and not F and (extra_B or main_xax not in (None, [])):
        verdict, ex, why = "NO_VERDICT", 2, "internal: an acceptance without open lemmas reported extra axioms %s" % main_xax
    elif main["rc"] == 0 and main.get("verdict") == "ACCEPTED" and (comp is None or (comp["rc"] == 0 and comp.get("verdict") == "ACCEPTED")):
        if F:
            verdict, ex = "CONDITIONAL", 3
            why = "every target statement of the official challenge is derivable from the permitted axioms plus the %d frontier hypotheses (statements = frontier challenge export sha256 %s)" % (len(F), info["frontier_challenge_sha256"][:16])
        else:
            verdict, ex, why = "ACCEPTED", 0, "no open lemma in the targets' closure: plain sound acceptance"
    elif main["rc"] == 1:
        verdict, ex, why = "REJECTED", 1, "main check: %s" % main.get("reason")
    elif comp is not None and comp["rc"] == 1:
        verdict, ex, why = "NO_VERDICT", 2, "the frontier challenge does not agree with the official challenge (%s)" % comp.get("reason")
    else:
        verdict, ex, why = "NO_VERDICT", 2, "main: %s; compare: %s" % (main.get("reason"), comp and comp.get("reason"))
    out = {
        "tool": VERSION, "verdict": verdict, "exit": ex, "why": why,
        "claim": ("the official challenge's targets %s follow from the permitted axioms %s plus the frontier hypotheses "
                  "listed below" % (info["scan"]["targets"], [a for a in json.load(open(os.path.join(outdir, "comparator.compare.json")))["permitted_axioms"] if a != SORRY]))
        if verdict == "CONDITIONAL" else None,
        "frontier": [{"name": n, **info["statements"].get(n, {})} for n in F],
        "frontier_size": len(F),
        "frontier_closed": info["scan"].get("frontier_closed", []),
        "outside_pinned_frontier": info["scan"].get("outside_pinned_frontier"),
        "blockers": {k: info["scan"][k] for k in ("sorry_in_targets", "sorry_in_definitions", "other_axioms", "missing")},
        "frontier_challenge_sha256": info["frontier_challenge_sha256"],
        "challenge_sha256": info["challenge_sha256"], "solution_sha256": info["solution_sha256"],
        "checks": res,
        "basis": "two runs of the unchanged trusted check (check/sound/check-sound.sh): compare = frontier challenge vs "
                 "official challenge, main = rewritten solution vs frontier challenge",
        "seconds": {"prepare": info["seconds"]["total"], "checks": round(time.time() - t0, 3)},
    }
    json.dump(out, open(os.path.join(outdir, "verdict.json"), "w"), indent=1, ensure_ascii=False)
    return out


def summary_line(v):
    s = "frontier: %s (exit %d): %s" % (v["verdict"], v["exit"], v["why"])
    if v["frontier"]:
        s += "\n  open lemmas (%d):" % v["frontier_size"]
        for f in v["frontier"][:50]:
            s += "\n    %s : %s" % (f["name"], (f.get("type") or "?")[:300])
    b = v["blockers"]
    for k in ("sorry_in_targets", "sorry_in_definitions", "other_axioms", "missing"):
        if b.get(k):
            s += "\n  %s: %s" % (k, ", ".join(x if isinstance(x, str) else x["name"] for x in b[k][:20]))
    if v.get("outside_pinned_frontier"):
        s += "\n  open lemmas outside the pinned frontier: %s" % ", ".join(v["outside_pinned_frontier"])
    return s


# ---------------------------------------------------------------------------------------------------------------------
def opts(argv, spec):
    """tiny option parser: spec = {"--x": default}; returns (positional, options)"""
    o = dict(spec)
    pos = []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a.startswith("--") and "=" in a and a.split("=", 1)[0] in spec:   # --opt=value
            k, v = a.split("=", 1)
            o[k] = v
            i += 1
        elif a in spec:
            if i + 1 >= len(argv):   # a missing value is a refused input (exit 2), not a crash
                raise Refuse("option %s needs a value" % a)
            o[a] = argv[i + 1]
            i += 2
        elif a == "--":
            o["--"] = argv[i + 1:]
            break
        elif a.startswith("-") and len(a) > 1:   # a misspelled option is not a positional
            raise Refuse("unknown option %s" % a.split("=", 1)[0])
        else:
            pos.append(a)
            i += 1
    return pos, o


_CHILDREN = []   # child processes (each its own process group): killed when frontier.py gets a signal
_HELD_FDS = []   # the OUT lock (flock on OUT/.frontier-run-out) of a run


class Interrupted(Exception):
    pass


def _descendants(root):
    """live (non-zombie) descendants of `root` from /proc (frontier.py is a child subreaper, so orphans stay here)"""
    kids = {}
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % d, "rb") as f:
                st = f.read()
            rest = st[st.rindex(b")") + 2:].split()
            if rest[0] == b"Z":
                continue
            kids.setdefault(int(rest[1]), []).append(int(d))
        except (OSError, ValueError, IndexError):
            continue
    out, todo = [], [root]
    while todo:
        for c in kids.get(todo.pop(), []):
            out.append(c)
            todo.append(c)
    return out


def _kill_tree(grace=5.0):
    """TERM every descendant, wait up to `grace` s, then KILL whatever is left"""
    import signal as _sg
    me = os.getpid()
    for p in _descendants(me):
        try:
            os.kill(p, _sg.SIGTERM)
        except OSError:
            pass
    t_end = time.time() + grace
    while time.time() < t_end and _descendants(me):
        try:
            while os.waitpid(-1, os.WNOHANG)[0] > 0:
                pass
        except ChildProcessError:
            pass
        time.sleep(0.05)
    for p in _descendants(me):
        try:
            os.kill(p, _sg.SIGKILL)
        except OSError:
            pass


def _on_signal(signum, _frame):
    """SIGTERM / SIGINT / SIGHUP: entered ONCE (all three are ignored
    from here on), kills frontier.py's whole descendant tree (TERM, KILL after 5 s), prints one NO_VERDICT line and exits 2
    at once - never 130 / 143, never a RecursionError, never an orphan writing into OUT. The children stay in frontier.py's
    process group, so a supervisor's group SIGKILL (timeout -s KILL, a job controller) takes them too."""
    import signal as _sg
    for sg in (_sg.SIGTERM, _sg.SIGINT, _sg.SIGHUP):
        _sg.signal(sg, _sg.SIG_IGN)
    _kill_tree()
    why = "interrupted (signal %d): no verdict" % signum
    try:
        sys.stderr.write("frontier: NO_VERDICT (exit 2): %s\n" % why)
        sys.stdout.write(json.dumps({"tool": VERSION, "verdict": "NO_VERDICT", "exit": 2, "why": why, "frontier": [],
                                     "frontier_size": 0, "blockers": {}}) + "\n")
        sys.stdout.flush()
    finally:
        os._exit(2)


def main(argv):
    """a refused input (configuration outside GOAL S1(3), malformed internal configuration / frontier) is NO
    verdict: one JSON line with verdict NO_VERDICT, exit 2 (never 0 / 3). So is every
    other way this tool can end without a verdict: an OSError / ValueError / internal error, a SystemExit with a message,
    a signal - exit 2, never 1 (the REJECTED code)."""
    import signal as _sg
    try:   # orphaned grandchildren are re-parented to frontier.py, so _kill_tree still finds them
        import ctypes
        ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0)   # PR_SET_CHILD_SUBREAPER
    except Exception:   # noqa: BLE001
        pass
    for sg in (_sg.SIGTERM, _sg.SIGINT, _sg.SIGHUP):
        _sg.signal(sg, _on_signal)
    try:
        return _main(argv)
    except SystemExit as e:
        if isinstance(e.code, int) or e.code is None:
            raise
        why = "refused: %s" % e.code
    except Refuse as e:
        why = "refused: %s" % e
    except Interrupted as e:
        why = "interrupted (%s): no verdict" % e
    except Exception as e:   # noqa: BLE001
        why = "error: %s: %s" % (type(e).__name__, e)
    v = {"tool": VERSION, "verdict": "NO_VERDICT", "exit": 2, "why": why, "frontier": [], "frontier_size": 0,
         "blockers": {}}
    sys.stderr.write("frontier: NO_VERDICT (exit 2): %s\n" % why)
    print(json.dumps(v, ensure_ascii=False))
    return 2


def _main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        sys.stderr.write(__doc__)
        return 2
    cmd, rest = argv[0], argv[1:]
    common = {"--frontier": "auto", "--axioms": "", "--pinned": None, "--probe": None, "--threads": str(os.cpu_count() or 8),
              "--svc": None, "--json": None, "--challenge-sha256": None, "--comparator-sha256": None}
    pos, o = opts(rest, common)
    nposs = {"scan": 2, "prepare": 4, "check": 1, "verify": 4, "pin": 4, "run": 3}
    if cmd in ("scan", "prepare", "check", "pin") and (o["--challenge-sha256"] is not None or o["--comparator-sha256"] is not None):
        # an integrity constraint a subcommand cannot enforce is refused, not ignored
        raise Refuse("%s does not take --challenge-sha256 / --comparator-sha256 (only run and verify enforce pins)" % cmd)
    if cmd in nposs and len(pos) != nposs[cmd]:   # a wrong number of positional arguments: refused (exit 2)
        raise Refuse("%s takes %d positional arguments, got %d (%s)" % (cmd, nposs[cmd], len(pos), " ".join(pos)[:200]))
    if o["--axioms"].startswith("@"):   # @FILE: one name per line (check-frontier.sh --axioms FILE)
        axioms = read_name_list(o["--axioms"][1:])
    else:
        axioms = [x for x in o["--axioms"].split(",") if x]
    if cmd == "scan":
        export, cfgp = pos
        rep = scan(Export(export), load_cfg(cfgp), parse_frontier(o["--frontier"]), axioms)
        js = json.dumps(rep, indent=1, ensure_ascii=False)
        if o["--json"]:
            open(o["--json"], "w").write(js)
        print(js)
        return 0
    if cmd == "prepare":
        export, challenge, cfgp, outdir = pos
        info = prepare(export, challenge, cfgp, outdir, o["--frontier"], axioms, o["--pinned"], probe=o["--probe"])
        print(json.dumps({k: info[k] for k in ("frontier", "frontier_challenge_sha256", "seconds")}))
        return 0
    if cmd == "check":
        (outdir,) = pos
        v = check(outdir, int(o["--threads"]), o["--svc"])
        sys.stderr.write(summary_line(v) + "\n")
        print(json.dumps(v, ensure_ascii=False))
        return v["exit"]
    if cmd == "verify":
        export, challenge, cfgp, outdir = pos
        # pins come together (the challenge pin needs the comparator pin); a pinned input is read ONCE into a private copy under
        # OUTDIR/pinned and only that copy is used (prepare, the trusted checks, check()'s re-verification)
        if (o["--challenge-sha256"] is None) != (o["--comparator-sha256"] is None) or \
                (o["--challenge-sha256"] and not o["--comparator-sha256"]):
            # the two pins come together, either way round
            raise Refuse("verify: --challenge-sha256 and --comparator-sha256 are given together (both or neither)")
        if os.path.islink(os.path.join(outdir, "verdict.json")) or os.path.isfile(os.path.join(outdir, "verdict.json")):
            os.unlink(os.path.join(outdir, "verdict.json"))   # an earlier run's verdict never survives a failure
        for k in ("--challenge-sha256", "--comparator-sha256"):
            if o[k] is not None and not re.fullmatch(r"[0-9a-f]{64}", o[k]):
                raise Refuse("verify: %s must be 64 lowercase hex" % k)
        if o["--challenge-sha256"]:
            challenge = copy_pinned(challenge, os.path.join(outdir, "pinned", "challenge.export"), o["--challenge-sha256"],
                                    "challenge export", "--challenge-sha256")
        if o["--comparator-sha256"]:
            cfgp = copy_pinned(cfgp, os.path.join(outdir, "pinned", "comparator.json"), o["--comparator-sha256"],
                               "comparator config", "--comparator-sha256")
        pinfo = prepare(export, challenge, cfgp, outdir, o["--frontier"], axioms, o["--pinned"])
        v = check(outdir, int(o["--threads"]), o["--svc"],
                  pins=(o["--challenge-sha256"], o["--comparator-sha256"]) if o["--challenge-sha256"] else None, info=pinfo)
        sys.stderr.write(summary_line(v) + "\n")
        print(json.dumps(v, ensure_ascii=False))
        return v["exit"]
    if cmd == "pin":
        export, challenge, cfgp, pindir = pos
        if os.path.exists(pindir) and os.listdir(pindir):
            raise Refuse("pin: %s exists and is not empty" % pindir)
        work = tempfile.mkdtemp(prefix="frontier-pin.", dir=os.path.dirname(os.path.abspath(pindir)) or ".")
        info = prepare(export, challenge, cfgp, work, o["--frontier"], axioms, None)
        v = check(work, int(o["--threads"]), o["--svc"])
        print(summary_line(v))
        if v["exit"] not in (0, 3):
            print("pin: not pinned (the frontier verdict is not an acceptance); work dir kept: %s" % work)
            return v["exit"]
        os.makedirs(pindir, exist_ok=True)
        shutil.copyfile(os.path.join(work, "frontier", "challenge.export"), os.path.join(pindir, "challenge.export"))
        rec = {"version": VERSION, "frontier": info["frontier"],
               "frontier_lemmas": [(info.get("frontier_lemma_of") or {}).get(n, n) for n in info["frontier"]],
               "rewrite": info.get("rewrite"), "statements": info["statements"],
               "frontier_challenge_sha256": info["frontier_challenge_sha256"],
               "challenge_sha256": info["challenge_sha256"], "pinned_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "pin_verdict": {k: v[k] for k in ("verdict", "why", "checks")}}
        json.dump(rec, open(os.path.join(pindir, "frontier.json"), "w"), indent=1, ensure_ascii=False)
        shutil.rmtree(work, ignore_errors=True)
        print("pinned %d open lemmas in %s (frontier challenge sha256 %s)" % (len(info["frontier"]), pindir,
                                                                           info["frontier_challenge_sha256"]))
        return v["exit"]
    if cmd == "run":
        project, chdir, out = pos
        sha = o["--challenge-sha256"]
        csha = o["--comparator-sha256"]
        # both pins are required, 64 lowercase hex, before anything runs (exit 2)
        if not sha or not re.fullmatch(r"[0-9a-f]{64}", sha):
            raise Refuse("run: --challenge-sha256 HEX (64 lowercase hex) is required (the official challenge export's pin)")
        if not csha or not re.fullmatch(r"[0-9a-f]{64}", csha):
            raise Refuse("run: --comparator-sha256 HEX (64 lowercase hex) is required together with --challenge-sha256 "
                         "(the pin of the problem's comparator.json)")
        # comparator.json is read ONCE, into OUT/pinned/comparator.json (verified against the pin);
        # only that copy is used: load_cfg, bin/fastverify (--comparator-config), prepare, check()
        # nothing of an earlier run in OUT is ever judged: bin/fastverify gets a fresh OUT/fv,
        # and verdict.json / frontier / pinned copies are rewritten by this run only. Only an OUT that is new, empty or marked
        # as a frontier.py run output (.frontier-run-out) is used, so clearing never touches anything else
        import fcntl
        import stat as _st
        mark = os.path.join(out, ".frontier-run-out")
        if os.path.lexists(out) and not os.path.isdir(out):
            raise Refuse("run: OUT %s exists and is not a directory" % out)
        mst = os.lstat(mark) if os.path.lexists(mark) else None   # the marker is never followed
        if mst is not None and not _st.S_ISREG(mst.st_mode):
            raise Refuse("run: %s is not a regular file (a link / directory is never followed)" % mark)
        if os.path.isdir(out) and os.listdir(out) and mst is None:
            raise Refuse("run: OUT %s is not empty and is not a frontier.py run output (no .frontier-run-out): give a new or "
                         "empty OUT" % out)
        os.makedirs(out, exist_ok=True)
        mfd = os.open(mark, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
        if not _st.S_ISREG(os.fstat(mfd).st_mode):
            raise Refuse("run: %s is not a regular file" % mark)
        try:   # one run per OUT at a time
            fcntl.flock(mfd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            raise Refuse("run: OUT %s is in use by another frontier.py run" % out)
        os.ftruncate(mfd, 0)
        os.write(mfd, b"frontier.py run output directory (earlier outputs in it are removed by the next run)\n")
        _HELD_FDS.append(mfd)   # the lock is held until frontier.py exits
        clear_outputs(out, ["fv", "frontier", "pinned", "verdict.json", "fastverify.log"])
        cfg_priv = copy_pinned(os.path.join(chdir, "comparator.json"), os.path.join(out, "pinned", "comparator.json"), csha,
                               "comparator config", "--comparator-sha256")
        load_cfg(cfg_priv)   # refuse a configuration outside GOAL S1(3) up front
        ce_priv = None
        if os.path.lexists(os.path.join(chdir, "challenge.export")):   # both pins checked before
            ce_priv = copy_pinned(os.path.join(chdir, "challenge.export"), os.path.join(out, "pinned", "challenge.export"),
                                  sha, "challenge export", "--challenge-sha256")   # bin/fastverify starts
        extra = o.get("--", [])
        bad_x = [t for t in extra if t.startswith("-") and (t == "--" or t.split("=", 1)[0] not in RUN_EXTRA_ALLOWED)]
        if bad_x:   # what is judged, against what pins, and the deciding check come from run's own arguments
            raise Refuse("run: EXTRA bin/fastverify option(s) %s not allowed (allowed: %s)" % (bad_x, " ".join(sorted(RUN_EXTRA_ALLOWED))))
        cfg_sha_here = csha   # = sha256 of the private copy (verified by copy_pinned)
        fvout = os.path.join(out, "fv")
        os.makedirs(out, exist_ok=True)
        t0 = time.time()
        int(o["--threads"])   # a malformed --threads: no verdict before anything starts
        with open(os.path.join(out, "fastverify.log"), "w") as lf:
            r = subprocess.Popen([os.path.join(PKG, "bin", "fastverify"), project, chdir, fvout, "--preset", "sound",
                                  "--threads", o["--threads"], "--challenge-sha256", sha, "--comparator-sha256", csha,
                                  "--comparator-config", cfg_priv, "--export-dir", "none"] + extra,
                                 stdout=lf, stderr=subprocess.STDOUT,
                                 env={"HOME": os.environ.get("HOME", "/tmp"), "PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"})
            _CHILDREN.append(r)   # its process group is killed if frontier.py gets a signal
            r.wait()
        t_fv = time.time() - t0
        try:
            res = json.load(open(os.path.join(fvout, "result.json")))
        except Exception:
            res = {}
        v0 = res.get("verdict")
        exp = os.path.join(fvout, "solution.export")
        base = {"fastverify_verdict": v0, "fastverify_seconds": round(t_fv, 3), "fastverify_exit": r.returncode}
        # OUT/fv did not exist before the child ran, so its result.json is this child's; it
        # counts only with the exit code that goes with it (ACCEPTED 0 / REJECTED 1) - a refusal / crash is no verdict
        judged = (v0, r.returncode) in (("ACCEPTED", 0), ("REJECTED", 1))
        # the shortcut is a plain SOUND acceptance only if bin/fastverify really ran the sound check (the
        # EXTRA args may override --preset / --check: trust UNSAFE / official / exact-by-design is never 'sound'); any
        # other acceptance goes through the frontier path below (the trusted check judges the export itself)
        sound_run = res.get("trust") == "sound" and (res.get("mode") or {}).get("sound") is True
        ins = res.get("inputs") if isinstance(res.get("inputs"), dict) else {}
        same_inputs = (res.get("mode") or {}).get("export_given") is False \
            and (ins.get("challenge_export") or {}).get("sha256") == sha \
            and (ins.get("comparator_config") or {}).get("sha256") == cfg_sha_here
        if v0 == "ACCEPTED" and r.returncode == 0 and sound_run and same_inputs:
            v = {"tool": VERSION, "verdict": "ACCEPTED", "exit": 0, "why": "plain sound acceptance (no open lemma)",
                 "frontier": [], "frontier_size": 0, "blockers": {}, **base}
            json.dump(v, open(os.path.join(out, "verdict.json"), "w"), indent=1)
            print(summary_line(v))
            return 0
        if not judged:
            v = {"tool": VERSION, "verdict": "NO_VERDICT", "exit": 2,
                 "why": "bin/fastverify gave no verdict (exit %s, verdict %s): %s" % (r.returncode, v0, res.get("verdict_basis")),
                 "frontier": [], "frontier_size": 0, "blockers": {}, **base}
            json.dump(v, open(os.path.join(out, "verdict.json"), "w"), indent=1)
            print(summary_line(v))
            return 2
        if not os.path.isfile(exp) or (res.get("export") or {}).get("exit") not in (0, None) or \
                (res.get("build") or {}).get("exit") not in (0, None):
            v = {"tool": VERSION, "verdict": v0 if v0 == "REJECTED" else "NO_VERDICT", "exit": 1 if v0 == "REJECTED" else 2,
                 "why": "build/export did not produce an export: %s" % (res.get("verdict_basis")),
                 "frontier": [], "frontier_size": 0, "blockers": {}, **base}
            json.dump(v, open(os.path.join(out, "verdict.json"), "w"), indent=1)
            print(summary_line(v))
            return v["exit"]
        # the frontier path only for an export bin/fastverify JUDGED on exactly the pinned inputs:
        # a declined / refused / errored run, or one whose recorded input hashes are not the pins, is no verdict
        if v0 not in ("ACCEPTED", "REJECTED") or (ins.get("comparator_config") or {}).get("sha256") != csha \
                or (ins.get("challenge_export") or {}).get("sha256") != sha:
            v = {"tool": VERSION, "verdict": "NO_VERDICT", "exit": 2,
                 "why": "bin/fastverify did not judge the pinned inputs (verdict %s, comparator sha256 %s, challenge sha256 %s)"
                        % (v0, (ins.get("comparator_config") or {}).get("sha256"), (ins.get("challenge_export") or {}).get("sha256")),
                 "frontier": [], "frontier_size": 0, "blockers": {}, **base}
            json.dump(v, open(os.path.join(out, "verdict.json"), "w"), indent=1)
            print(summary_line(v))
            return 2
        if ce_priv is not None:
            ce = ce_priv
        else:
            ce_src = (res.get("inputs") or {}).get("challenge_export", {}).get("path") or os.path.join(chdir, "challenge.export")
            ce = copy_pinned(ce_src, os.path.join(out, "pinned", "challenge.export"), sha, "challenge export", "--challenge-sha256")
        # the solution export judged is exactly the one bin/fastverify recorded (its sha256), copied once
        esha = (res.get("export") or {}).get("sha256")
        if not isinstance(esha, str) or not re.fullmatch(r"[0-9a-f]{64}", esha):
            v = {"tool": VERSION, "verdict": "NO_VERDICT", "exit": 2, "why": "bin/fastverify recorded no sha256 for its export",
                 "frontier": [], "frontier_size": 0, "blockers": {}, **base}
            json.dump(v, open(os.path.join(out, "verdict.json"), "w"), indent=1)
            print(summary_line(v))
            return 2
        exp = copy_pinned(exp, os.path.join(out, "pinned", "solution.export"), esha, "solution export",
                          "bin/fastverify's recorded export sha256")
        cfgp = cfg_priv
        fo = os.path.join(out, "frontier")
        pinfo = prepare(exp, ce, cfgp, fo, o["--frontier"], axioms, o["--pinned"])
        v = check(fo, int(o["--threads"]), o["--svc"], pins=(sha, csha), info=pinfo)
        v.update(base)
        v["seconds"]["fastverify"] = round(t_fv, 3)
        v["seconds"]["total"] = round(time.time() - t0, 3)
        json.dump(v, open(os.path.join(out, "verdict.json"), "w"), indent=1, ensure_ascii=False)
        print(summary_line(v))
        return v["exit"]
    sys.stderr.write(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

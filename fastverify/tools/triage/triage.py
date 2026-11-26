#!/usr/bin/python3 -I
"""triage.py — Fast sandboxed pre-proving sub-lemma triage & hygiene coach.

Before dispatching many AI prover runs (or burning hours of search compute) on a new `sorry` sub-lemma
proposed by a mathematician or Architect Agent, run a fast (~1-2 s with header snapshot) sandboxed
triage pass inside bwrap (--unshare-all, no network):
  1. Static hygiene & statement-hazard lints (instant, <5 ms):
     - Partial-operation hazards: unguarded Nat subtraction, division, Int.toNat, Real.sqrt
     - Monolithic `import Mathlib` / `maxHeartbeats` / slow tactic anti-patterns
     - Unused explicit hypothesis detection (binder name never referenced in remaining statement)
     - Suspicious `autoImplicit` free identifiers (checked cleanly with `set_option autoImplicit false`!)
  2. Sandboxed Lean elaboration & refutation probes (bwrap, official Lean 4.33.1, optional header snapshot):
     - Statement well-typedness under `set_option autoImplicit false` (catches typos like `RiemannHypotheis`!)
     - Negation / counterexample refutation probe on `¬ (<statement>)` using bounded `omega` / `norm_num` /
       `decide` / `linarith` / `simp` + concrete boundary witnesses (0, 1, 2, -1) -> catches false sub-lemmas
       such as `∀ n : ℕ, n - 5 + 5 = n` or missing `x ≠ 0` BEFORE proving!
     - Vacuity probe: checks whether hypotheses imply `False` (contradictory premises) or whether the
       conclusion holds unconditionally without using hypotheses.
  3. Duplicate-lemma lookup hook: calls the dupfind duplicate-lemma index if installed, plus fast local
     repository theorem-signature match.

Zero TCB change: pure advisory in-loop guidance. Untrusted Lean code runs strictly inside bwrap without network.
"""
import argparse
import json
import os
import stat
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.realpath(__file__))
FV_ROOT = os.path.realpath(os.path.join(HERE, "..", ".."))


def default_toolchain():
    """Default official Lean 4.33.1 toolchain: the one registered in config/components.json (tools/configure.py),
    else ${ELAN_HOME:-~/.elan}/toolchains/leanprover--lean4---v4.33.1."""
    try:
        with open(os.path.join(os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..")), "config", "components.json"), encoding="utf-8") as f:
            p = json.load(f)["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"]
        if p:
            return p
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return os.path.join(os.environ.get("ELAN_HOME") or os.path.expanduser("~/.elan"), "toolchains",
                        "leanprover--lean4---v4.33.1")


def default_packages():
    """Default trusted Lake workspace: $FV_PACKAGES, else <repository root>/verify/challenge if it exists, else None."""
    p = os.environ.get("FV_PACKAGES")
    if p:
        return p
    p = os.path.join(os.path.dirname(FV_ROOT), "verify", "challenge")
    return p if os.path.isdir(p) else None


sys.path.insert(0, os.path.join(FV_ROOT, "schemas"))
import fv_schema  # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
import leanlex  # noqa: E402   (the Lean-tokenizer mirror, shared with tools/http/fvapi.py)

BWRAP = "/usr/bin/bwrap"

# Match declaration header start: theorem/lemma NAME
DECL_HEAD_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|local|scoped)\s+)*"
    r"(?:theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)",
    re.M,
)

# Extract explicit binders `(h : P)` or `(x y : T)`
EXPLICIT_BINDER_RE = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_'\s]*?)\s*:\s*([^()]+?)\s*\)")


def strip_lean_comments(src):
    """the source with every comment blanked, read EXACTLY as Lean tokenizes it (lean_read); a regex
    stripper would ignore string literals: `def s1 := "/-"` ... `def s2 := "-/"` would hide the theorems between them, and `"--"`
    would cut a line. Raises leanlex.LeanSourceUnclear where the source cannot be read unambiguously."""
    return lean_read(src)[0]


_DECL_STOP = frozenset({"theorem", "lemma", "def", "abbrev", "structure", "inductive", "class", "instance", "axiom",
                        "end", "namespace", "section", "where"})
_BR_OPEN = {"(": ")", "[": "]", "{": "}", "\u2983": "\u2984", "\u27e8": "\u27e9"}
_NAME_OK = re.compile(r"^[^\s\x00-\x1f\x7f\u00ab\u00bb]+$")


def lean_read(src):
    """(same reading as tools/http/fvapi.py's theorem inference) -> (clean, top): clean = the source (CRLF -> LF)
    with every comment and doc comment blanked (same length, newlines kept), top = the top-level tokens
    (kind, text, start, end). A `theorem` / `lemma` inside a string interpolation, one not followed by a plain name, or
    anything leanlex cannot read exactly -> leanlex.LeanSourceUnclear (the caller fails closed)."""
    lx = leanlex._LeanLexer(src)
    try:
        _, toks = lx.code(0, 0, False)
    except RecursionError:
        raise leanlex.LeanSourceUnclear("source nested too deeply") from None
    s, out, top, cur = lx.s, [], [], 0
    for kind, text, _comps, pos in toks:
        if pos < cur:   # a token inside a string literal's interpolation
            if kind == "ident" and text in ("theorem", "lemma"):
                lx.fail("`%s` inside a string interpolation" % text, pos)
            continue
        end = pos + (1 + len(text) if kind == "namelit" else len(text))
        out.append(re.sub(r"[^\n]", " ", s[cur:pos]))   # whitespace and comments only (Parser.whitespace)
        out.append(re.sub(r"[^\n]", " ", s[pos:end]) if kind == "doc" else s[pos:end])
        top.append((kind, text, pos, end))
        cur = end
    out.append(re.sub(r"[^\n]", " ", s[cur:]))
    for k, (kind, text, pos, _end) in enumerate(top):
        if kind == "ident" and text in ("theorem", "lemma"):
            if k + 1 >= len(top) or top[k + 1][0] != "ident" or not _NAME_OK.match(top[k + 1][1]):
                lx.fail("`%s` not followed by a plain name" % text, pos)
    return "".join(out), top


def extract_decls_lex(clean, top):
    """theorem / lemma signatures from the TOKENS of lean_read (strings and character literals are atomic;
    a `theorem` inside a string is no declaration): name, binders (up to the first top-level `:`), type (up to the
    top-level `:=`, a `|` alternative at the start of a line, or the next top-level command keyword)"""
    out, closes, n = [], set(_BR_OPEN.values()), len(top)
    # the open scopes, kept exactly as
    # leanlex.lean_declared_theorems keeps them: `namespace A.B` opens one scope per component (`end B` closes one, `end A.B`
    # two), `section [X.Y]` / `mutual` open anonymous ones, `end [name]` closes as many as the name has components; a scope
    # name that cannot be read here (a «» component, an `end` without an open scope) makes every later declaration unclear
    scopes, scope_bad = [], None

    def scope_name(k):   # the optional name after section / end: an identifier (not a keyword) on the same line
        if k + 1 < n and top[k + 1][0] == "ident" and top[k + 1][1] not in leanlex._LEAN_KEYWORDS \
                and "\n" not in clean[top[k][3]:top[k + 1][2]]:
            return top[k + 1][1]
        return None
    for k, (kind, text, _pos, _end) in enumerate(top):
        if kind == "ident" and text in ("namespace", "section", "mutual", "end") and not (k > 0 and top[k - 1][1] == "."
                                                                                       and top[k - 1][3] == _pos):
            nm = scope_name(k)
            if nm is not None and ("\u00ab" in nm or "\u00bb" in nm):
                scope_bad = scope_bad or "a scope name with \u00ab\u00bb (%s)" % nm
            comps = nm.split(".") if nm else []
            if text == "namespace":
                if not comps or comps[0] == "_root_":
                    scope_bad = scope_bad or "`namespace` without a plain name"
                scopes.extend(comps)
            elif text == "section":
                scopes.extend([None] * len(comps) if comps else [None])
            elif text == "mutual":
                scopes.append(None)
            else:
                cnt = len(comps) if comps else 1
                if cnt > len(scopes):
                    scope_bad = scope_bad or "`end` without an open scope"
                    cnt = len(scopes)
                del scopes[len(scopes) - cnt:]
            continue
        if not (kind == "ident" and text in ("theorem", "lemma")):
            continue
        name, name_end = top[k + 1][1], top[k + 1][3]
        ns = ".".join(c for c in scopes if c)
        qname = name[len("_root_."):] if name.startswith("_root_.") else (ns + "." + name if ns else name)
        unclear = ("the enclosing scopes cannot be read exactly: " + scope_bad) if scope_bad else None
        depth, colon, stop, kw = 0, None, len(clean), None
        for j in range(k + 2, n):
            kd, tx, ps, _en = top[j]
            if kd == "sym":
                if tx in _BR_OPEN:
                    depth += 1
                elif tx in closes:
                    depth = max(0, depth - 1)
                elif depth == 0 and tx == ":":
                    nxt = top[j + 1] if j + 1 < n else None
                    prv = top[j - 1]
                    if nxt and nxt[0] == "sym" and nxt[1] == "=" and nxt[2] == ps + 1:
                        stop = ps
                        if kw and colon is not None:
                            # `let n := 2; ...` / `have h : p := ...` in the TYPE: this `:=` is not
                            # the proof's; the statement cannot be cut here (a cut there gives a false ELAB_ERROR)
                            unclear = unclear or "the statement contains `%s ... :=` (its `:=` is not the proof's)" % kw
                        break
                    dbl = (nxt and nxt[0] == "sym" and nxt[1] == ":" and nxt[2] == ps + 1) or \
                        (prv[0] == "sym" and prv[1] == ":" and prv[3] == ps)
                    if colon is None and not dbl:
                        colon = ps
                elif depth == 0 and tx == "|" and colon is not None and not clean[clean.rfind("\n", 0, ps) + 1:ps].strip():
                    stop = ps
                    nxt = top[j + 1] if j + 1 < n else None
                    if nxt and nxt[0] == "sym" and nxt[2] == ps + 1 and nxt[1] not in _BR_OPEN:
                        # `||`, `|>`, `|>.`, `|||` ... continuing the statement at the start of a
                        # line is no equation arm: the statement cannot be cut here (probing the prefix gives a false REFUTED)
                        unclear = "a line of the statement starts with the operator `%s%s` (not an equation arm)" % (tx, nxt[1])
                    break
            elif kd == "ident" and depth == 0 and colon is not None and tx in _DECL_STOP:
                stop = ps
                break
            elif kd == "ident" and depth == 0 and colon is not None and tx in _TYPE_BINDING_KW:
                kw = kw or tx
        if colon is not None:
            out.append({"name": name, "binders": clean[name_end:colon].strip(), "type": clean[colon + 1:stop].strip(),
                        "qname": qname, "k": k, "unclear": unclear})
    return out


_TYPE_BINDING_KW = frozenset({"let", "letI", "have", "haveI", "suffices", "let_fun", "match", "do", "show", "from"})


def _decl_start(top, k):
    """the token index where the declaration whose `theorem` / `lemma` is top[k] starts: an attribute
    block `@[...]`, modifiers (leanlex _LEAN_DECL_MODIFIERS) and a doc comment in front of the keyword belong to it"""
    j = k - 1
    while j >= 0:
        kind, text, _pos, _end = top[j]
        if kind == "ident" and text in leanlex._LEAN_DECL_MODIFIERS or kind == "doc":
            j -= 1
            continue
        if kind == "sym" and text == "]":   # an attribute block @[ ... ] (nested brackets allowed)
            depth, i = 0, j
            while i >= 0:
                if top[i][0] == "sym" and top[i][1] == "]":
                    depth += 1
                elif top[i][0] == "sym" and top[i][1] == "[":
                    depth -= 1
                    if depth == 0:
                        break
                i -= 1
            if i > 0 and top[i - 1][0] == "sym" and top[i - 1][1] == "@":
                j = i - 2
                continue
        break
    return j + 1


_PLAIN_COMP = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")


def _target_unclear(msg):
    return None, [{"kind": "target_unclear", "severity": "error",
                   "message": "%s (fail-closed: no statement extracted, no probe, no dispatch)" % msg}]


def extract_all_decls(clean):
    """Balanced-delimiter extractor for Lean 4 theorem/lemma signatures.
    Handles nested (...), [...], {...}, ⦃...⦄ in binders without splitting at binder colons."""
    out = []
    opens = {"(": ")", "[": "]", "{": "}", "\u2983": "\u2984"}
    closes = set(opens.values())
    n = len(clean)
    for m in DECL_HEAD_RE.finditer(clean):
        name = m.group("name")
        i = m.end()
        depth = 0
        in_str = False
        colon_pos = None
        end_pos = n
        while i < n:
            ch = clean[i]
            if in_str:
                if ch == "\\" and i + 1 < n:
                    i += 2
                    continue
                if ch == '"':
                    in_str = False
                i += 1
                continue
            if ch == '"':
                in_str = True
                i += 1
                continue
            if ch in opens:
                depth += 1
            elif ch in closes:
                depth = max(0, depth - 1)
            elif depth == 0:
                if ch == ":" and i + 1 < n and clean[i + 1] == "=":
                    end_pos = i
                    break
                if ch == ":" and colon_pos is None and (i == 0 or clean[i - 1] != ":") and (i + 1 >= n or clean[i + 1] != ":"):
                    colon_pos = i
                elif colon_pos is not None and clean[i:i + 6] == "\nwhere" or (colon_pos is not None and clean[i:i + 7] == " where "):
                    end_pos = i
                    break
                elif colon_pos is not None and ch == "\n":
                    # Stop if next top-level keyword starts a new declaration
                    rest = clean[i + 1:]
                    if re.match(r"^(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|end|namespace|section)\b", rest):
                        end_pos = i
                        break
            i += 1
        if colon_pos is not None:
            binders_str = clean[m.end():colon_pos].strip()
            type_str = clean[colon_pos + 1:end_pos].strip()
            out.append({"name": name, "binders": binders_str, "type": type_str})
    return out


def static_lint_statement(source, decl_name=None):
    """Instant (<5 ms) static lints on a Lean sub-lemma source snippet. The source is read with leanlex (the
    Lean-tokenizer mirror shared with fvapi); a source it cannot read exactly -> (None, [source_unclear error]): the
    caller fails closed (status UNCLEAR, no dispatch, no probe)."""
    try:
        clean, top = lean_read(source)
        if any(t[0] == "ident" and t[1] == "axiom" for t in top):
            raise leanlex.LeanSourceUnclear("the source declares an axiom (no probe answer would be evidence)")
    except leanlex.LeanSourceUnclear as e:
        return None, [{"kind": "source_unclear", "severity": "error",
                       "message": f"source cannot be read unambiguously as Lean tokenizes it: {fv_schema.sanitize_single_line(e, 200)} "
                                  "(fail-closed: no statement extracted, no dispatch)"}]
    findings = []

    # 1. Hygiene: monolithic import Mathlib
    if re.search(r"^\s*import\s+Mathlib\s*$", clean, re.M):
        findings.append({
            "kind": "hygiene_monolithic_import",
            "severity": "info",
            "message": "Uses monolithic `import Mathlib`; consider targeted imports (e.g., `import Mathlib.Tactic`) to cut build time on selective projects.",
        })
    if "maxHeartbeats 0" in clean or "maxRecDepth" in clean:
        findings.append({
            "kind": "hygiene_limit_override",
            "severity": "warning",
            "message": "Modifies `maxHeartbeats` or `maxRecDepth`; may stall builds or cause official-toolchain divergence.",
        })
    if "with_unfolding_all exact" in clean:
        findings.append({
            "kind": "hygiene_slow_tactic",
            "severity": "warning",
            "message": "Contains `with_unfolding_all exact` (known critical-path elaboration hotspot).",
        })

    # Extract target declaration statement (from the tokens; a theorem inside a string is none)
    decls = extract_decls_lex(clean, top)
    target_match = None
    if decl_name:
        # an explicitly named theorem must be found, exactly once: its namespace-qualified name,
        # else its name as written / a unique qualified suffix; never a fallback to the LAST theorem (a different statement)
        cands = [d for d in decls if d["qname"] == decl_name]
        if not cands:
            cands = [d for d in decls if d["name"] == decl_name or d["qname"].endswith("." + decl_name)]
        if len(cands) != 1:
            return _target_unclear("theorem %s: %s" % (fv_schema.sanitize_single_line(decl_name, 120),
                                                       "no theorem / lemma of that name in the source" if not cands
                                                       else "%d theorems / lemmas match that name" % len(cands)))
        target_match = cands[0]
    elif decls:
        target_match = decls[-1]
    else:   # nothing to triage is no evidence: UNCLEAR, never "OK, dispatch"
        return _target_unclear("the source declares no theorem / lemma")
    if target_match and target_match.get("unclear"):
        return _target_unclear("theorem %s: %s" % (target_match["name"], target_match["unclear"]))
    if target_match:
        st0 = _decl_start(top, target_match["k"])
        if st0 > 0 and top[st0 - 1][0] == "ident" and top[st0 - 1][1] == "in":
            # `open scoped X in` / `set_option ... in` scopes the target alone: the probe
            # cannot keep that scope (its first command would consume it: false REFUTED / VACUOUS)
            return _target_unclear("theorem %s: preceded by a command-scoped `... in` (its scope cannot be kept in the "
                                   "probe)" % target_match["name"])
        if target_match["binders"].lstrip().startswith(".{"):
            # universe parameters `t.{u}`: the probe cannot carry them into its statement
            return _target_unclear("theorem %s: declares universe parameters (.{...})" % target_match["name"])
        nmc = target_match["name"].split(".")
        if len(nmc) > 1 and (nmc[0] == "_root_" or not all(_PLAIN_COMP.match(c) for c in nmc[:-1])):
            # a dotted name opens its namespace for the statement (scoped instances included):
            # the probe reopens it for plain components; `_root_.A.b` and unusual components are not reproduced
            return _target_unclear("theorem %s: the namespace its dotted name opens cannot be reproduced exactly"
                                   % target_match["name"])

    stmt_info = None
    if target_match:
        name = target_match["name"]
        binders_str = target_match["binders"]
        type_str = target_match["type"]
        full_stmt = (f"∀ {binders_str}, {type_str}" if binders_str else type_str).strip()
        stmt_info = {"name": name, "binders": binders_str, "type": type_str, "full_type_expr": full_stmt,
                     "_decl_index": target_match["k"]}   # internal: where the target's environment ends

        # 2. Partial-operation hazards in statement
        has_nat = bool(re.search(r"\b(Nat|ℕ)\b", full_stmt))
        if has_nat and re.search(r"[^<>!=:]\s-\s", full_stmt):
            if not re.search(r"(≤|<=|≥|>=|<|>)", full_stmt):
                findings.append({
                    "kind": "hazard_nat_sub",
                    "severity": "warning",
                    "message": "Natural-number subtraction (`-` on ℕ) detected without an ordering guard (≤/≥/<); truncated subtraction (`3 - 5 = 0`) frequently makes sub-lemmas false or unintended.",
                })
        if re.search(r"\s/\s", full_stmt):
            if not re.search(r"(≠\s*0|!=\s*0|>\s*0|0\s*<|NeZero|Pos)", full_stmt):
                findings.append({
                    "kind": "hazard_div_by_zero",
                    "severity": "warning",
                    "message": "Division (`/`) detected without an apparent nonzero/positivity guard (in Lean, `x / 0 = 0`).",
                })
        if "Int.toNat" in full_stmt and not re.search(r"(0\s*≤|≥\s*0|>=\s*0|<=\s*)", full_stmt):
            findings.append({
                "kind": "hazard_int_tonat",
                "severity": "warning",
                "message": "`Int.toNat` detected without a non-negativity guard (negative integers truncate to 0).",
            })
        if "Real.sqrt" in full_stmt and not re.search(r"(0\s*≤|≥\s*0|>=\s*0|0\s*<|>\s*0)", full_stmt):
            findings.append({
                "kind": "hazard_real_sqrt",
                "severity": "warning",
                "message": "`Real.sqrt` detected without a non-negativity guard (`Real.sqrt x = 0` for `x < 0`).",
            })

        # 3. Unused explicit binders (heuristic check on non-Prop value variables)
        # Note: hypothesis binders `(h : P)` are normally unused in the *statement* (they're used in the proof!),
        # whereas value variables `(x : ℕ)` unused in BOTH remaining binders and type are genuinely unused!
        binders = list(EXPLICIT_BINDER_RE.finditer(binders_str))
        for idx, bm in enumerate(binders):
            vars_part = bm.group(1).strip().split()
            btype = bm.group(2).strip()
            # Skip likely proposition hypotheses (contain relations, logical ops, or standard Prop predicates)
            if re.search(
                r"(=|≠|!=|<|>|≤|≥|∣|→|->|∧|∨|↔|¬|∈|∉|⊆|⊂|⊇|⊃|∃|∀|⊥|⊤|"
                r"\b(?:Prop|False|True|Is\w+|Has\w+|Prime|Even|Odd|NeZero|Pos|Nonempty|"
                r"Continuous|Measurable|Integrable|Differentiable|Monotone|StrictMono|"
                r"Injective|Surjective|Bijective|Coprime|Disjoint|Irreducible|Associated|"
                r"Fintype|Finite|Infinite|Decidable\w*)\b)",
                btype,
            ):
                continue
            rest = binders_str[bm.end():] + " " + type_str
            for v in vars_part:
                if v.startswith("_"):
                    continue
                if not re.search(rf"\b{re.escape(v)}\b", rest):
                    findings.append({
                        "kind": "unused_variable",
                        "severity": "warning",
                        "message": f"Explicit variable `({v} : {btype})` does not appear in the rest of the statement (possible typo or dead variable).",
                    })

        # 4. Contradictory-looking binder patterns (quick static smell)
        # only a hypothesis whose TYPE is exactly False (`(h : False)`): `(h : False ∨ True)` is
        # satisfiable and was flagged as an error
        if re.search(r"[(\[{]\s*[^():\[\]{}]*:\s*False\s*[)\]}]", binders_str):
            findings.append({
                "kind": "vacuity_false_premise",
                "severity": "error",
                "message": "Statement hypotheses explicitly mention `False` (likely vacuous).",
            })

    return stmt_info, findings


def probe_header(source, decl_index=None):
    """the source text BEFORE the declaration of the target theorem, found on the lexer's tokens:
    an attribute (`@[simp]`), modifiers (private, protected, ...) or a doc comment in front of `theorem` belong to that
    declaration (a split on `^theorem` lines would keep `@[simp] theorem bad ... := sorry` in the header, serving simp).
    decl_index = the token index of the target's `theorem` / `lemma`: everything before it is
    kept - the target's EXACT environment (earlier theorems included: a sorry / error in one of them reaches a probe only as
    sorryAx, which voids its evidence; `end` of a section, `omit`, inner namespaces all apply). A cut before the FIRST
    theorem would keep a local instance of a closed section, an `include` later omitted, an outer definition later
    shadowed active (false REFUTED / VACUOUS). Without decl_index: before the first theorem / lemma."""
    clean, top = lean_read(source)
    if decl_index is not None and 0 <= decl_index < len(top) and top[decl_index][0] == "ident" \
            and top[decl_index][1] in ("theorem", "lemma"):
        k = decl_index
    else:
        k = next((i for i, t in enumerate(top) if t[0] == "ident" and t[1] in ("theorem", "lemma")), None)
    if k is None:
        return clean
    return clean[:top[_decl_start(top, k)][2]]


def build_probe_lean(source, stmt_info, probe_negation=True, probe_vacuity=True, tag="x"):
    """Build a self-contained Lean probe file that checks:
    1. Strict elaboration under `set_option autoImplicit false` (catches typo implicit variables)
    2. Negation refutation probe (`theorem _fv_refuted_TAG : ¬ (<stmt>)`) with bounded tactics
    3. Vacuity / trivial-conclusion probe (when statement is an implication chain)
    TAG = a random per-run nonce in every probe name and in the start / done markers, which client
    text cannot predict; the client's header is printed BEFORE the start marker (its output is ignored)
    """
    header = probe_header(source, stmt_info.get("_decl_index")).rstrip()
    if not header.strip():
        header = "import Init"

    has_mathlib = bool(re.search(r"^\s*import\s+Mathlib\b", header, re.M))
    full_type = stmt_info["full_type_expr"]
    out = [
        header,
        "",
        '#print "' + PROBE_START + tag + '"',
        "section _FVTriage",
        "set_option autoImplicit false",
        "set_option linter.all false",
        "set_option maxHeartbeats 50000",
        "",
    ]
    # a dotted target name `A.B.t` elaborates its statement inside namespace A.B
    nmc = stmt_info["name"].split(".")
    ns_open = ".".join(nmc[:-1]) if len(nmc) > 1 else None
    out += ([f"namespace {ns_open}"] if ns_open else []) + [
        f"abbrev _root_._fv_target_stmt_{tag} : Prop := {full_type}",   # never in the client's namespace
    ] + ([f"end {ns_open}"] if ns_open else []) + [
        # the statement must be CLOSED: a section variable it uses (an
        # optParam one included) would become a parameter of the abbrev, and the probes would test something else
        f"example : Prop := @_root_._fv_target_stmt_{tag}   -- fv-closed-check",
        "",
    ]

    if probe_negation:
        refute_arms = [
            "(intro h; first | (have := h 0; omega) | (have := h 1; omega) | (have := h 0 0; omega) | (have := h 0 1; omega) | (have := h 1 0; omega) | (have := h 1 1; omega) | (have := h 0 2; omega) | (have := h 2 0; omega))",
            "decide",
            "omega",
            "simp",
        ]
        if has_mathlib:
            refute_arms.insert(1, "(intro h; first | (have := h 0; norm_num at this) | (have := h 1; norm_num at this) | (have := h (-1); norm_num at this) | (have := h 0 0; norm_num at this) | (have := h 0 1; norm_num at this) | (have := h 1 0; norm_num at this))")
            refute_arms.insert(2, "(intro h; first | (have := h 0; linarith) | (have := h 1; linarith) | (have := h (-1); linarith))")
            refute_arms.append("norm_num")
        out += [
            f"theorem _root_._fv_refuted_{tag} : ¬ _fv_target_stmt_{tag} := by",
            f"  dsimp only [_fv_target_stmt_{tag}]",
            "  first",
        ] + [f"    | {arm}" for arm in refute_arms] + [
            "",
            # the refutation must be of exactly `¬ statement`: an included section hypothesis
            # (`include h`, h : n < 0) would make it `∀ n, n < 0 → ¬ statement` - provable from the hypothesis alone
            f"example : type_of% @_root_._fv_refuted_{tag} = (¬ _root_._fv_target_stmt_{tag}) := rfl   -- fv-type-check",
            f"#print axioms _fv_refuted_{tag}", ""]

    if probe_vacuity:
        vac_arms = [
            "(intros; exfalso; omega)",
            "(intros; exfalso; contradiction)",
            "(intros; exfalso; simp_all)",
        ]
        if has_mathlib:
            vac_arms.insert(1, "(intros; exfalso; linarith)")
            vac_arms.insert(2, "(intros; exfalso; norm_num at *)")
        out += [
            f"theorem _root_._fv_trivial_or_vacuous_{tag} : _fv_target_stmt_{tag} := by",
            f"  dsimp only [_fv_target_stmt_{tag}]",
            "  first | " + " | ".join(vac_arms),
            "",
            f"example : type_of% @_root_._fv_trivial_or_vacuous_{tag} = _root_._fv_target_stmt_{tag} := rfl   -- fv-type-check",
            f"#print axioms _fv_trivial_or_vacuous_{tag}",
            "",
        ]

    out.append("end _FVTriage")
    # the last command: printed only if Lean really processed the whole probe file
    out.append('#print "' + PROBE_DONE + tag + '"\n')
    return "\n".join(out)


PROBE_START = "FV_TRIAGE_PROBE_START_"
PROBE_DONE = "FV_TRIAGE_PROBE_DONE_"
S1_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})
_TC_OK = {}

def official_toolchain_error(tc):
    """None iff tc is the prefix of a toolchain registered in config/components.json whose whole tree verifies
    (lib/toolchain.py verify; once per process): only the official toolchain's answers are evidence"""
    r = os.path.realpath(tc)
    if r in _TC_OK:
        return _TC_OK[r]
    err = None
    try:
        comps = json.load(open(os.path.join(FV_ROOT, "config", "components.json"), encoding="utf-8"))
        tid = next((k for k, v in (comps.get("lean_toolchains") or {}).items()
                    if v.get("prefix") and os.path.realpath(v["prefix"]) == r), None)
        if tid is None:
            err = "toolchain %s is not a registered official toolchain (config/components.json)" % tc
        else:
            p = subprocess.run(["/usr/bin/python3", "-I", os.path.join(FV_ROOT, "lib", "toolchain.py"), "verify", r, tid],
                               capture_output=True, text=True, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}, timeout=900)
            if p.returncode != 0:
                err = "toolchain %s does not verify against its pinned manifest" % tid
    except (OSError, ValueError, subprocess.SubprocessError) as e:
        err = "toolchain check failed: %s" % e
    _TC_OK[r] = err
    return err


def probe_proved(out, name, tag):
    """positive evidence that the probe theorem `name` (already carrying the run's tag) was
    PROVED from GOAL S1(3) axioms only: considered is only Lean's output AFTER the probe's own start marker; EXACTLY one
    `#print axioms` line for exactly that name must be there, and its axioms must be a subset of {propext, Quot.sound,
    Classical.choice} (a failed tactic proof carries sorryAx; a client axiom - or any other - is no evidence)"""
    i = out.find(PROBE_START + tag)
    if i < 0:
        return False
    tail = out[i + len(PROBE_START + tag):]
    ms = re.findall(r"^'(?:_FVTriage\.)?%s' (does not depend on any axioms|depends on axioms: \[([^\]\n]*)\])\s*$"
                    % re.escape(name), tail, re.M)
    if len(ms) != 1:
        return False
    axs = {a.strip() for a in (ms[0][1] or "").split(",") if a.strip()}
    return axs <= S1_AXIOMS


def lake_packages_dir(ws):
    """the packages directory Lake uses for workspace ws: the manifest's packagesDir,
    else the lakefile.toml packagesDir, else .lake/packages (bin/fv's cli_packages checks every one of these and .lake/packages
    itself); an unusable value falls back to .lake/packages"""
    wsr = os.path.realpath(ws)
    pd = None
    try:
        with open(os.path.join(wsr, "lake-manifest.json"), encoding="utf-8") as f_:
            man = json.load(f_)
        pd = man.get("packagesDir") if isinstance(man, dict) else None
    except (OSError, ValueError):
        pd = None
    if not (isinstance(pd, str) and pd.strip()):
        try:
            with open(os.path.join(wsr, "lakefile.toml"), encoding="utf-8") as f_:
                m_ = re.search(r'(?m)^\s*packagesDir\s*=\s*"([^"\\]*)"\s*(#.*)?$', f_.read())
            pd = m_.group(1) if m_ else None
        except OSError:
            pd = None
    if not (isinstance(pd, str) and pd.strip()):
        pd = ".lake/packages"
    pd = pd[2:] if pd.startswith("./") else pd
    comps = pd.rstrip("/").split("/")
    if pd.startswith("/") or any(c in ("", ".", "..") for c in comps):
        pd = ".lake/packages"
    return os.path.join(wsr, pd)


def run_sandboxed_probe(probe_src, tc, ws, snap_dir=None, timeout=20.0):
    """Elaborate probe_src inside bwrap (--unshare-all, no network) using official lean.
    Returns (rc, wall_s, output_text)."""
    t0 = time.time()
    tmpd = tempfile.mkdtemp(prefix="fv-triage.")
    try:
        src_p = os.path.join(tmpd, "Probe.lean")
        with open(src_p, "w", encoding="utf-8") as f:
            f.write(probe_src)
        ws_pk = lake_packages_dir(ws)   # the directory Lake uses (checked by bin/fv's cli_packages)
        lp = ":".join(   # a workspace without .lake/packages has no packages (not an exception)
            os.path.join(ws_pk, d, ".lake", "build", "lib", "lean")
            for d in (sorted(os.listdir(ws_pk)) if os.path.isdir(ws_pk) else [])
            if os.path.isdir(os.path.join(ws_pk, d, ".lake", "build", "lib", "lean"))
        )
        tc_r = os.path.realpath(tc)
        ro_extra = []
        lean_args = [os.path.join(tc_r, "bin", "lean")]
        # Reuse official --incr-header-save snapshot if available and header is plain `import Mathlib`
        first_nonempty = next((ln.strip() for ln in probe_src.splitlines() if ln.strip()), "")
        snap_file = None
        if snap_dir and first_nonempty == "import Mathlib":
            for r, _, fs in os.walk(snap_dir):
                if "hdr.snap" in fs:
                    snap_file = os.path.join(r, "hdr.snap")
                    break
        if snap_file and os.path.isfile(snap_file):
            ro_extra.append(os.path.dirname(snap_file))
            lean_args += ["--incr-load", snap_file]
        lean_args.append(src_p)
        cmd = [
            BWRAP, "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root",
            "--tmpfs", "/run/user", "--tmpfs", "/tmp", "--dir", "/tmp/home",
            "--tmpfs", "/run", "--tmpfs", "/var", "--dev", "/dev", "--proc", "/proc",
            "--clearenv", "--ro-bind", tc_r, tc_r,
        ] + (["--ro-bind", ws_pk, ws_pk] if os.path.isdir(ws_pk) else []) + [   # absent -> no bind
            "--ro-bind", tmpd, tmpd,
        ]
        for p in ro_extra:
            cmd += ["--ro-bind", p, p]
        cmd += [
            "--setenv", "PATH", f"{tc_r}/bin:/usr/bin:/bin",
            "--setenv", "HOME", "/tmp/home",
            "--setenv", "LANG", "C.UTF-8",
            "--setenv", "LEAN_PATH", lp,
            "--unshare-all", "--die-with-parent", "--new-session",
            "--chdir", tmpd, "--", *lean_args,
        ]
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env={}, start_new_session=True)
        try:
            out, err = p.communicate(timeout=timeout)
            return p.returncode, round(time.time() - t0, 3), (out or "") + (err or "")
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except OSError:
                p.kill()
            try:
                p.communicate(timeout=2.0)
            except Exception:
                pass
            return 124, round(time.time() - t0, 3), f"triage probe timed out after {timeout}s"
    finally:
        shutil.rmtree(tmpd, ignore_errors=True)


def check_local_duplicates(stmt_info, repo_dir=None):
    """Fast local exact/normalized statement duplicate search in repo_dir (plus hook for the exphash index)."""
    if not stmt_info or not repo_dir or not os.path.isdir(repo_dir):
        return []
    norm_target = " ".join(stmt_info["type"].split())
    if len(norm_target) < 8:
        return []
    hits = []
    scanned = 0
    for r, ds, fs in os.walk(repo_dir):
        ds[:] = [d for d in ds if not d.startswith(".") and d != ".lake" and not os.path.islink(os.path.join(r, d))]
        for fn in fs:
            if not fn.endswith(".lean"):
                continue
            scanned += 1
            if scanned > 2000:
                break
            p = os.path.join(r, fn)
            try:   # never read through a link: single-link regular files only, O_NOFOLLOW
                fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            except OSError:
                continue
            try:
                fst = os.fstat(fd)
                if not stat.S_ISREG(fst.st_mode) or fst.st_nlink != 1:
                    continue
                with os.fdopen(os.dup(fd), "rb") as fh:
                    txt = fh.read(200000).decode("utf-8", errors="replace")
            except OSError:
                continue
            finally:
                os.close(fd)
            try:   # read exactly as Lean does; a file that cannot be is skipped (no duplicate claimed from it)
                rclean, rtop = lean_read(txt)
            except leanlex.LeanSourceUnclear:
                continue
            for d in extract_decls_lex(rclean, rtop):
                if d["name"] == stmt_info["name"]:
                    continue
                cand = " ".join(d["type"].split())
                if cand == norm_target:
                    hits.append({
                        "name": d["name"],
                        "file": os.path.relpath(p, repo_dir),
                        "match_kind": "normalized_text_exact",
                    })
                    if len(hits) >= 10:
                        return hits
    return hits


def check_dupfind_duplicates(source, stmt_info, dupfind_indexes=None, tc=None, ws=None, snap_dir=None, timeout=20.0):
    """Optional kernel-level exphash duplicate lookup via tools/dupfind/dupfind.py."""
    if not dupfind_indexes or not stmt_info or not tc or not ws:
        return []
    df_py = os.path.join(FV_ROOT, "tools", "dupfind", "dupfind.py")
    if not os.path.isfile(df_py):
        return []
    tmpd = tempfile.mkdtemp(prefix="fv-tr-dup.")
    try:
        qf = os.path.join(tmpd, "Query.lean")
        open(qf, "w", encoding="utf-8").write(source)
        cmd = [
            "/usr/bin/python3", "-I", df_py, "query", qf, "--json", "--fast-export",
            "--toolchain", tc, "--packages", ws, "--fv", FV_ROOT, "--threads", "4",
            "--targets", stmt_info["name"],
        ]
        for ix in dupfind_indexes:
            cmd += ["--index", os.path.realpath(ix)]
        if snap_dir and os.path.isdir(snap_dir):
            cmd += ["--snapshot", snap_dir]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        if p.returncode == 0 and p.stdout.strip():
            data = json.loads(p.stdout.strip().splitlines()[-1])
            hits = []
            for it in data.get("items") or []:
                for m in it.get("matches") or []:
                    hits.append({
                        "name": m.get("name"),
                        "file": m.get("module") or m.get("index"),
                        "match_kind": f"exphash_{m.get('match', 'statement')}",
                    })
            return hits[:10]
    except Exception:
        pass
    finally:
        shutil.rmtree(tmpd, ignore_errors=True)
    return []


def triage_sublemma(
    source,
    decl_name=None,
    tc=None,
    ws=None,
    snap_dir=None,
    repo_dir=None,
    dupfind_indexes=None,
    run_lean_probes=True,
    timeout=20.0,
):
    """Run full static + optional sandboxed Lean pre-proving triage on a sub-lemma snippet."""
    t0 = time.time()
    stmt_info, findings = static_lint_statement(source, decl_name=decl_name)
    dups = check_local_duplicates(stmt_info, repo_dir=repo_dir)
    if dupfind_indexes:
        dups.extend(check_dupfind_duplicates(source, stmt_info, dupfind_indexes=dupfind_indexes,
                                             tc=tc, ws=ws, snap_dir=snap_dir, timeout=timeout))
    if dups:
        findings.append({
            "kind": "duplicate_lemma",
            "severity": "warning",
            "message": f"Existing lemma(s) with identical statement found: {[d['name'] for d in dups[:5]]}",
        })

    probe_res = {
        "ran": False,
        "elaborates_strict": None,
        "refuted": False,
        "vacuous_premises": False,
        "wall_s": 0.0,
        "raw_output": "",
    }

    tc_err = official_toolchain_error(tc) if (run_lean_probes and stmt_info and tc and ws) else None
    if tc_err:   # no probe evidence from a toolchain that is not the verified official one
        findings.append({"kind": "probe_incomplete", "severity": "error",
                         "message": "Lean triage probes not run: %s (UNCLEAR)" % tc_err})
    if run_lean_probes and stmt_info and tc and ws and not tc_err:
        tag = os.urandom(8).hex()   # per-run nonce of the probe names and markers
        probe_src = build_probe_lean(source, stmt_info, probe_negation=True, probe_vacuity=True, tag=tag)
        rc, w_s, out = run_sandboxed_probe(probe_src, tc=tc, ws=ws, snap_dir=snap_dir, timeout=timeout)
        probe_res["ran"] = True
        probe_res["wall_s"] = w_s
        probe_res["raw_output"] = out[:4000]
        diags = fv_schema.parse_lean_diagnostics(out)

        # Locate line ranges of _fv_target_stmt, _fv_refuted, _fv_trivial_or_vacuous
        plines = probe_src.splitlines()
        l_stmt = next((i + 1 for i, l in enumerate(plines) if l.startswith("abbrev _root_._fv_target_stmt")), 1)
        l_ref = next((i + 1 for i, l in enumerate(plines) if l.startswith("theorem _root_._fv_refuted")), 10**6)
        l_vac = next((i + 1 for i, l in enumerate(plines) if l.startswith("theorem _root_._fv_trivial_or_vacuous")), 10**6)

        # the header now holds the earlier theorems too: an error there says nothing about the target
        # statement (no ELAB_ERROR) - but the environment is then not the source's: no claim (UNCLEAR)
        l_cl = next((i + 1 for i, l in enumerate(plines) if l.endswith("-- fv-closed-check")), -1)
        l_hdr = next((i + 1 for i, l in enumerate(plines) if l.startswith('#print "' + PROBE_START)), l_stmt)
        hdr_errs = [d for d in diags if d["severity"] == "error" and d["line"] < l_hdr]
        stmt_errs = [d for d in diags if d["severity"] == "error" and l_hdr <= d["line"] < l_ref and d["line"] != l_cl]
        # the statement is not closed (a section variable became a parameter): no claim (UNCLEAR)
        open_errs = [d for d in diags if d["severity"] == "error" and d["line"] == l_cl]
        # a probe theorem whose type is not exactly the statement (an included section
        # hypothesis became a binder): its evidence is void AND the statement Lean elaborates is not the one shown: UNCLEAR
        l_tc = {i + 1 for i, l in enumerate(plines) if l.endswith("-- fv-type-check")}
        open_errs += [d for d in diags if d["severity"] == "error" and d["line"] in l_tc]
        # an error inside a probe theorem's lines voids its evidence even when Lean still records it without
        # sorry (e.g. `dsimp` closes a closed true goal and the next tactic reports "No goals")
        ref_err = any(d["severity"] == "error" and l_ref <= d["line"] < l_vac for d in diags)
        vac_err = any(d["severity"] == "error" and d["line"] >= l_vac for d in diags)

        # no claim without positive evidence: the probe must have run to completion (its last command's
        # marker printed, Lean exit 0 / 1 = errors reported); reading "no Lean error" as REFUTED would turn an unrunnable
        # toolchain, a crash or a timeout into REFUTED
        done = rc in (0, 1) and (PROBE_DONE + tag) in out and (PROBE_START + tag) in out
        if not done:
            probe_res["incomplete"] = True
            findings.append({
                "kind": "probe_incomplete",
                "severity": "error",
                "message": ("Lean triage probe did not run to completion (%s): no claim about the statement (UNCLEAR)"
                            % ("timed out after %ss" % timeout if rc == 124 else "exit %s, completion marker %s"
                               % (rc, "present" if (PROBE_DONE + tag) in out else "missing"))),
            })
        elif hdr_errs:
            probe_res["incomplete"] = True
            findings.append({
                "kind": "probe_incomplete",
                "severity": "error",
                "message": "the source before the target theorem has Lean errors (%s): no claim about the statement (UNCLEAR)"
                           % fv_schema.sanitize_single_line(hdr_errs[0]["message"], 160),
            })
        elif stmt_errs:
            probe_res["elaborates_strict"] = False
            for e in stmt_errs[:5]:
                msg = e["message"]
                kind = "auto_implicit_or_unbound" if ("unknown identifier" in msg.lower() or "autoimplicit" in msg.lower()) else "statement_elab_error"
                findings.append({
                    "kind": kind,
                    "severity": "error",
                    "message": f"Statement fails strict elaboration (`autoImplicit false`): {fv_schema.sanitize_single_line(msg, 240)}",
                })
        elif open_errs:
            probe_res["incomplete"] = True
            findings.append({
                "kind": "probe_incomplete",
                "severity": "error",
                "message": "the target statement depends on section variables or included hypotheses (the declaration Lean "
                           "elaborates is not the statement shown): no claim about the statement (UNCLEAR)",
            })
        else:
            probe_res["elaborates_strict"] = True

            def confirmed(name, neg, vac):
                """a REFUTED / VACUOUS claim is confirmed by a probe holding ONLY that theorem: Lean exit 0, the
                completion marker and the theorem's axioms line without sorryAx"""
                src1 = build_probe_lean(source, stmt_info, probe_negation=neg, probe_vacuity=vac, tag=tag)
                rc1, w1, out1 = run_sandboxed_probe(src1, tc=tc, ws=ws, snap_dir=snap_dir, timeout=timeout)
                probe_res["wall_s"] = round(probe_res["wall_s"] + w1, 3)
                return rc1 == 0 and (PROBE_DONE + tag) in out1 and probe_proved(out1, name + "_" + tag, tag)
            # `_fv_refuted` PROVED (axioms line, no sorryAx) and confirmed alone: Lean's kernel proved `¬ _fv_target_stmt`
            if probe_proved(out, "_fv_refuted_" + tag, tag) and not ref_err:
                if confirmed("_fv_refuted", True, False):
                    probe_res["refuted"] = True
                    findings.append({
                        "kind": "refuted_false_sublemma",
                        "severity": "error",
                        "message": "REFUTED: Lean proved `¬ statement` via bounded counterexample/decision tactics — DO NOT dispatch provers on this sub-lemma!",
                    })
                else:
                    probe_res["incomplete"] = True
                    findings.append({"kind": "probe_incomplete", "severity": "error",
                                     "message": "the refutation was not confirmed by a clean probe run (UNCLEAR)"})
            # `_fv_trivial_or_vacuous` PROVED and confirmed alone: the premises imply False (vacuous)
            if not probe_res["refuted"] and not probe_res.get("incomplete") and probe_proved(out, "_fv_trivial_or_vacuous_" + tag, tag) \
                    and not vac_err:
                if confirmed("_fv_trivial_or_vacuous", False, True):
                    probe_res["vacuous_premises"] = True
                    findings.append({
                        "kind": "vacuous_contradictory_premises",
                        "severity": "error",
                        "message": "VACUOUS: Lean derived `False` directly from the sub-lemma's hypotheses (contradictory premises)!",
                    })
                else:
                    probe_res["incomplete"] = True
                    findings.append({"kind": "probe_incomplete", "severity": "error",
                                     "message": "the vacuity was not confirmed by a clean probe run (UNCLEAR)"})

    status = "OK"
    if any(f.get("kind") in ("source_unclear", "target_unclear", "probe_incomplete") for f in findings):
        status = "UNCLEAR"   # fail-closed like fvapi's theorem inference; a probe without evidence
    elif probe_res["refuted"]:
        status = "REFUTED"
    elif probe_res["vacuous_premises"]:
        status = "VACUOUS"
    elif probe_res["elaborates_strict"] is False:
        status = "ELAB_ERROR"
    elif any(f["severity"] == "error" for f in findings):
        status = "FLAGGED"
    elif any(f["severity"] == "warning" for f in findings):
        status = "WARN"

    return {
        "api_version": fv_schema.API_VERSION,
        "status": status,
        "dispatch_recommended": status in ("OK", "WARN"),
        "statement": {k: v for k, v in stmt_info.items() if not k.startswith("_")} if stmt_info else None,
        "probe": probe_res,
        "duplicates": dups,
        "findings": findings,
        "total_s": round(time.time() - t0, 3),
    }


def main():
    ap = argparse.ArgumentParser(description="Fast sandboxed pre-proving sub-lemma triage")
    ap.add_argument("file", help="Lean file containing the sorry sub-lemma (or '-' for stdin)")
    ap.add_argument("--theorem", default=None, help="target declaration name (default: last theorem/lemma in file)")
    ap.add_argument("--toolchain", default=default_toolchain(),
                    help="official Lean 4.33.1 toolchain (default: the registered one in config/components.json)")
    ap.add_argument("--packages", default=default_packages(),
                    help="trusted Lake workspace with .lake/packages (default: $FV_PACKAGES, else <repository root>/verify/challenge if present)")
    ap.add_argument("--snapshot-dir", default=None, help="optional directory containing hdr.snap for fast import Mathlib")
    ap.add_argument("--repo", default=None, help="optional repo root for local duplicate-statement scan")
    ap.add_argument("--dupfind-index", action="append", default=[], help="optional dupfind sqlite index dir (repeatable)")
    ap.add_argument("--static-only", action="store_true", help="skip sandboxed Lean probes (instant static lints only)")
    ap.add_argument("--timeout", type=float, default=20.0)
    args = ap.parse_args()
    if not args.static_only and not args.packages:
        sys.exit("triage: no trusted package workspace: pass --packages DIR or set FV_PACKAGES (or use --static-only)")

    try:   # an unreadable input is no evidence: UNCLEAR, exit 2 (was a traceback, exit 1)
        src = sys.stdin.read() if args.file == "-" else open(args.file, encoding="utf-8").read()
    except (OSError, UnicodeDecodeError) as e:
        print(json.dumps({"api_version": fv_schema.API_VERSION, "status": "UNCLEAR", "dispatch_recommended": False,
                          "statement": None, "probe": {"ran": False}, "duplicates": [],
                          "findings": [{"kind": "source_unclear", "severity": "error",
                                        "message": "the source cannot be read: %s (UNCLEAR)" % fv_schema.sanitize_single_line(e, 200)}],
                          "total_s": 0.0}, indent=2))
        sys.exit(2)
    res = triage_sublemma(
        src,
        decl_name=args.theorem,
        tc=args.toolchain,
        ws=args.packages,
        snap_dir=args.snapshot_dir,
        repo_dir=args.repo,
        dupfind_indexes=args.dupfind_index,
        run_lean_probes=(not args.static_only),
        timeout=args.timeout,
    )
    print(json.dumps(res, indent=2))
    # as bin/fv triage: 0 dispatch, 1 a finding against the statement, 2 UNCLEAR (no evidence)
    sys.exit(0 if res["dispatch_recommended"] else (2 if res["status"] == "UNCLEAR" else 1))


if __name__ == "__main__":
    main()

#!/usr/bin/python3 -I
"""fvapi.py — Hardened, Kimina-compatible HTTP/1.1 REST API fronting tools/fvserve.

Zero external dependencies (Python 3.10+ stdlib only). Additive, zero TCB change: every ACCEPTED
verdict comes exclusively from the unchanged trusted check inside fvserve (ccmp + pleanchecker +
gruszka on the pinned official challenge export).

Endpoints:
  GET  /health, /v1/health       Liveness & backend fvserve readiness
  GET  /metrics                  Prometheus text exposition metrics
  POST /verify, /api/check       Kimina-compatible AND canonical single/batch verification
  POST /v1/verify                Canonical API v1 single-attempt sound verification
  POST /v1/verify/batch          Canonical API v1 concurrent batch / best-of-N verification

Security hardening:
  * Binds 127.0.0.1 by default (loopback only unless --host is explicitly set)
  * Optional bearer-token auth (--api-key-file, constant-time hmac.compare_digest)
  * Strict Content-Length enforcement (411 if missing, 413 if > --max-body-bytes, rejects chunked)
  * Per-connection socket timeout (--socket-timeout) + total header/body deadlines (--header-timeout, --body-timeout) against slowloris
  * Concurrency admission semaphore (--max-concurrent; returns 429 + Retry-After when saturated)
  * Strict JSON validation (rejects NaN/Infinity, bad types, oversized batches, invalid names)
  * Reward-safe fail-closed semantics: ACCEPTED -> reward=1.0, is_pass=True;
    REJECTED / NO-VERDICT / DECLINED / ERROR / timeout -> reward=0.0, is_pass=False
"""
import argparse
import collections
import concurrent.futures as cf
import errno
import hmac
import http.server
import json
import os
import random
import re
import signal
import socket
import sys
import threading
import time

HERE = os.path.dirname(os.path.realpath(__file__))
FV_ROOT = os.path.realpath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(FV_ROOT, "schemas"))
sys.path.insert(0, os.path.join(FV_ROOT, "tools", "fvserve"))
import fv_schema  # noqa: E402
import fvserve    # noqa: E402


# ---------------------------------------------------------------------------------------------------------------------
# Lean source lexer: theorem inference (--experimental-theorem-inference, EXPERIMENTAL in v0.1; the former name
# --allow-theorem-inference is refused) reads the source with a lexer that mirrors the
# Lean 4 tokenizer (Lean/Parser/Basic.lean + StrInterpolation.lean; the same in 4.33.1, 4.36.0, 4.37.0-rc1 EXCEPT after a
# doc-comment opener: 4.33.1 also skips comments there, 4.36+ only spaces / newlines - that form is refused) on valid
# sources: CRLF -> LF like mkInputContext; whitespace (a tab / an isolated CR is a Lean error); `--` line comments; NESTED
# block comments (finishCommentBlock; the whitespace function skips the character right after `/-`); doc comments `/--`
# `/-!` (a token, then whitespace, then the comment body); string literals (escapes, gaps); interpolated strings; raw
# strings r#"..."#; character literals; name literals; numbers; identifiers with Lean's exact character classes, `«»`
# escapes and dotted components. A string literal is read BOTH as a plain and as an interpolated string (which one Lean
# uses depends on the syntax around it): different ends -> refused. Whatever cannot be read exactly as Lean reads it,
# and every command that can define syntax or run code that adds declarations, raises LeanSourceUnclear -> NO-VERDICT
# (fail-closed; an explicit 'theorem' is unaffected). Every `theorem` / `lemma` token is then one declaration; the token
# after it must be its name. Attributes `@[...]`, doc comments and modifiers in front of `theorem` need no special case.
# (Before: a regex comment stripper blind to string literals - `def s1 := "/-"` ... `def s2 := "-/"` hid a theorem from
# the multi-theorem guard - and a declaration regex without `@[...]`.)
# ---------------------------------------------------------------------------------------------------------------------
class LeanSourceUnclear(ValueError):
    """the source cannot be read unambiguously: theorem inference refuses (NO-VERDICT)"""


class _LeanSyntaxError(LeanSourceUnclear):
    """the text is a Lean SYNTAX error at this point (unterminated literal / comment, bad escape, tab, lone CR): Lean
    itself rejects a file that reads it this way"""


def _lean_letter_like(c):   # Init/Meta/Defs.lean isLetterLike
    v = ord(c)
    return ((0x3B1 <= v <= 0x3C9 and v != 0x3BB) or (0x391 <= v <= 0x3A9 and v != 0x3A0 and v != 0x3A3)
            or 0x3CA <= v <= 0x3FB or 0x1F00 <= v <= 0x1FFE or 0x2100 <= v <= 0x214F or 0x1D49C <= v <= 0x1D59F
            or (0xC0 <= v <= 0xFF and v != 0xD7 and v != 0xF7) or 0x100 <= v <= 0x17F)


def _lean_subscript_alnum(c):   # isSubScriptAlnum
    v = ord(c)
    return 0x2080 <= v <= 0x2089 or 0x2090 <= v <= 0x209C or 0x1D62 <= v <= 0x1D6A or v == 0x2C7C


def _lean_digit(c):
    return "0" <= c <= "9"


def _lean_hex(c):
    return "0" <= c <= "9" or "a" <= c <= "f" or "A" <= c <= "F"


def _lean_id_first(c):   # isIdFirst (Char.isAlpha is ASCII only)
    return "a" <= c <= "z" or "A" <= c <= "Z" or c == "_" or _lean_letter_like(c)


def _lean_id_rest(c):   # isIdRest
    return ("a" <= c <= "z" or "A" <= c <= "Z" or "0" <= c <= "9" or c == "_" or c == "'" or c == "!" or c == "?"
            or _lean_letter_like(c) or _lean_subscript_alnum(c))


# commands / attributes / tactics / terms that define syntax, run code at elaboration time, or generate theorems under
# names of their own (they can add a declaration without a `theorem` token, or change how the rest of the file is
# tokenized): theorem inference refuses such a source. Audit over the deployed token tables (core Lean
# 4.33.1 / 4.36.0 / 4.37.0-rc1 + `import Lean`; Mathlib 0df444a with every scoped token) and the tactic-category keywords
# (not in the token table) of core, Mathlib, Batteries, Qq, Aesop: code runners `run_cmd` `run_elab` `run_meta`
# `run_tac` `run_tacq` `by_elab` `by_elabq` `#eval`; syntax `macro*` `syntax` `elab*` `notation*` `infix*` `prefix`
# `postfix` `binder_predicate` `name_poly_vars` `name_power_vars` `declare_*` `leading_parser` `trailing_parser`; code
# registered for later runs
# `initialize` `builtin_*` `register_*` `*simproc*` `grind_propagator` + the attributes `command_elab` `term_elab`
# `tactic`; theorem generators `alias` `deprecate` `irreducible_def` `lrat_proof` `from_lrat` `gen_injective_theorems%`
# `mk_iff_of_inductive_prop` + the attributes `to_additive` `to_dual` `simps` `reassoc` `elementwise` `mk_iff` `to_app`.
_LEAN_UNCLEAR_IDENTS = frozenset({
    "macro", "macro_rules", "syntax", "elab", "elab_rules", "elab_stx_quot", "notation", "notation3", "infix", "infixl",
    "infixr", "prefix", "postfix", "binder_predicate", "name_poly_vars", "name_power_vars", "initialize", "run_cmd",
    "run_elab", "run_meta", "run_tac", "run_tacq", "by_elab", "by_elabq", "grind_propagator", "alias", "deprecate",
    "irreducible_def", "lrat_proof", "from_lrat", "gen_injective_theorems", "mk_iff_of_inductive_prop", "command_elab",
    "term_elab", "tactic", "to_additive", "to_dual", "simps", "reassoc", "elementwise", "mk_iff", "to_app",
    "leading_parser", "trailing_parser", "higher_order", "with_weak_namespace", "to_fun", "to_set_notation",
    "compile_def", "compile_inductive"})
# any identifier / name-literal COMPONENT naming the meta-programming layer (elaboration-time code that could add a
# declaration through the environment API, whatever command or attribute runs it): refused as well
_LEAN_META_COMPONENTS = frozenset({
    "Elab", "Meta", "CoreM", "MetaM", "TermElabM", "TacticM", "CommandElabM", "MacroM", "AttrM", "ImportM",
    "Environment", "addDecl", "addAndCompile", "addDeclCore", "addDeclWithoutChecking", "modifyEnv", "setEnv",
    "elabCommand", "elabCommandTopLevel", "evalConst", "evalConstCheck", "evalDecl", "evalExpr", "NormNumExt",
    "PositivityExt", "Simproc", "DSimproc"})
# a one-character symbol after which a string / character / name literal or a comment may start directly (any other
# symbol may be the start of a longer token of imported syntax, e.g. Mathlib's `⁻¹'`, so the split would be a guess).
# Derived from the deployed token tables - core 4.33.1 / 4.36.0 / 4.37.0-rc1 with `import Lean`, Mathlib
# 0df444a (4.33.1) with all scoped tokens: no token continues one of these characters with a quote, a backtick, `--` or
# `/-` (`]` and `=` are NOT safe: core `]'` as in `xs[i]'h`, Mathlib `='`; nor `#`, `/`). tests/fvapi-inference
# re-derives it from the token tables on every run.
# hash commands that are read (any other `#xyz` is refused: `#eval` runs code, `#guard_msgs` turns a failing declaration
# into an accepted file, `#exit` stops elaboration, others are unknown)
_LEAN_HASH_OK = frozenset({"check", "check_failure", "print", "reduce", "synth", "where", "version", "help", "lint", "find",
                           "simp", "norm_num", "conv", "whnf", "guard", "guard_expr", "check_simp"})
# modifiers that may precede a declaration keyword; `private` makes the kernel name `_private.<module>.0.<name>`
_LEAN_DECL_MODIFIERS = frozenset({"private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped", "local",
                                  "public", "meta"})
# classes whose derived instances are data (definitions, never theorems)
# attributes known NOT to declare theorems; any other attribute (inside `@[...]` or `attribute [...]`,
# after an optional `local` / `scoped` / `-`) makes the source UNCLEAR - an allow-list: `ext` (`<name>_iff`), `to_fun`,
# `to_set_notation`, `simps`, `to_additive`, ... and every attribute not listed here are refused
_LEAN_ATTR_OK = frozenset({"simp", "reducible", "irreducible", "semireducible", "inline", "noinline", "specialize", "instance",
                           "inherit_doc", "deprecated", "match_pattern", "norm_cast", "push_cast", "elab_as_elim", "refl",
                           "symm", "trans", "congr", "gcongr", "mono", "nolint", "induction_eliminator",
                           "cases_eliminator", "default_instance", "grind", "aesop", "fun_prop", "continuity",
                           "measurability", "bound"})
# modules after whose import `lemma` is a keyword (Mathlib.Tactic.Lemma / Batteries.Tactic.Lemma, or an import that contains it)
_LEAN_LEMMA_IMPORTS = frozenset({("Mathlib",), ("Mathlib", "Tactic"), ("Mathlib", "Tactic", "Lemma"), ("Batteries",),
                                 ("Batteries", "Tactic", "Lemma")})
# keywords that start / modify commands: preceded by `.` (Lean's rawIdent after `.`, `..`, `|>.`) or by `|` (a
# constructor name) they are NOT the keyword - the source is refused rather than guessed
_LEAN_CMD_KEYWORDS = frozenset({"theorem", "lemma", "instance", "section", "end", "namespace", "mutual", "deriving",
                                "attribute", "example", "def", "abbrev", "structure", "class", "inductive", "axiom", "opaque",
                                "with_weak_namespace"})
_LEAN_DATA_DERIVE = frozenset({"Repr", "DecidableEq", "BEq", "Hashable", "Inhabited", "Ord", "ToJson", "FromJson",
                               "ReprAtom", "TypeName", "ToExpr", "Fintype", "Encodable"})
_LEAN_SAFE_BEFORE = frozenset("()[{},;:⟨⟩!$%&*+-.<>?@^|~")
_LEAN_MAX_NEST = 64
# the identifier-shaped tokens (keywords) of the deployed token tables - core 4.33.1 / 4.36.0 /
# 4.37.0-rc1 with `import Lean`, Mathlib 0df444a with every scoped token; the standing test re-derives it. A keyword is
# never a name: `section theorem ...` is an anonymous section followed by a theorem; `theorem <keyword>` is refused.
_LEAN_KEYWORDS = frozenset({
    'AffineSpace', 'CMDiff', 'CMDiffAt', 'D', 'GL', 'I', 'L', 'MDiff', 'MDiffAt', 'PiType', 'Prop', 'Sort',
    'StateRefT', 'Type', 'V_', 'W', 'W_', 'Y', '_', '_comefrom', '_qq_match', 'abbrev', 'add_aesop_rules',
    'add_decl_doc', 'alias', 'assert!', 'assertInstancesCommute', 'assertInstancesCommuteDummy',
    'assertInstancesCommuteImpl', 'assert_no_sorry', 'assert_not_exists', 'assert_not_imported',
    'assumeInstancesCommute', "assumeInstancesCommute'", 'assumeInstancesCommuteDummy', 'at', 'attribute', 'aux_def',
    'axiom', 'bif', 'binder_predicate', 'break', 'builtin_cbv_simproc', 'builtin_cbv_simproc_decl',
    'builtin_dsimproc', 'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', 'builtin_simproc',
    'builtin_simproc_decl', 'by', 'by?', 'by_elab', 'by_elabq', 'calc', 'catch', 'cbv_eval', 'cbv_simproc',
    'cbv_simproc_decl', 'cexp', 'class', 'coinductive', 'coinductive_fixpoint', 'comefrom', 'conj', 'continue',
    'dbg_trace', 'debug_assert!', 'declare_aesop_exception', 'declare_aesop_rule_sets',
    'declare_bitwise_int_theorems', 'declare_bitwise_uint_theorems', 'declare_command_config_elab',
    'declare_command_config_elab_legacy', 'declare_config_elab', 'declare_config_elab_legacy',
    'declare_core_config_elab', 'declare_decidable_int_quantifiers', 'declare_decidable_uint_quantifiers',
    'declare_eval_bin', 'declare_eval_bin_bitwise', 'declare_eval_bin_bool_pred', 'declare_int_theorems',
    'declare_simp_like_tactic', 'declare_sint_simprocs', 'declare_syntax_cat', 'declare_term_config_elab',
    'declare_uint_simprocs', 'declare_uint_theorems', 'decreasing_by', 'def', 'def_eval_config_item', 'def_wanted',
    'deprecate', 'deprecated_module', 'deprecated_syntax', 'derive_eval_expr_instance_using_meta_eval', 'deriving',
    'distTriang', 'do', 'docs_to_verso', 'dsimproc', 'dsimproc_decl', 'elab', 'elab_rules', 'elab_stx_quot', 'else',
    'end', 'end_local_scope', 'ensure_eval_expr_instance', 'ensure_eval_term_expr_instances',
    'ensure_eval_term_instance', 'erase_aesop_rules', 'eval_prec', 'eval_prio', 'example', 'exists', 'export',
    'extend_docs', 'extends', 'f!', 'finally', 'for', 'forall', 'from', 'from_lrat', 'fun', 'fun₀', 'generalizing',
    'grind_annotated', 'grind_pattern', 'grind_propagator', 'guard_min_heartbeats', 'have', 'haveI', "haveI'",
    'hiding', 'idbg', 'if', 'import', 'in', 'include', 'include_str', 'inductive', 'inductive_fixpoint',
    'inferInstanceAs', 'infix', 'infixl', 'infixr', 'init_grind_norm', 'init_quot', 'initialize',
    'initialize_simps_projections', 'initialize_simps_projections?', 'insert_to_additive_translation', 'instance',
    'instance_wanted', 'irreducible_def', 'kerodon', 'leading_parser', 'lemma', 'let', 'letI', "letI'",
    'let_delayed', 'let_expr', 'let_fun', 'let_impl_detail', 'let_tmp', 'library_note', 'line!', 'local',
    'logNamedError', 'logNamedErrorAt', 'logNamedWarning', 'logNamedWarningAt', 'lrat_proof', 'm!', 'macro',
    'macro_rules', 'match', 'match_expr', 'matches', 'max_prec', 'meta', 'mk_iff_of_inductive_prop', 'mod_cast',
    'monotonicity_by', 'mulAuxMatBlock', 'mut', 'mutual', 'name_poly_vars', 'name_power_vars', 'namespace',
    'nat_lit', 'no_index', 'nofun', 'nomatch', 'noncomputable', 'nonrec', 'norm_cast_add_elim', 'nosimp', 'notation',
    'notation3', 'omit', 'on', 'opaque', 'open', 'over', 'panic!', 'partial', 'partial_fixpoint', 'postfix',
    'postprocess_traces', 'prefix', 'println!', 'private', 'proof_wanted', 'protected', 'public', 'recall',
    'recall?', 'recommended_spelling', 'register_builtin_option', 'register_error_explanation',
    'register_grind_attr', 'register_hint', 'register_label_attr', 'register_linter_set', 'register_option',
    'register_parser_alias', 'register_simp_attr', 'register_sym_dsimp', 'register_sym_simp',
    'register_sym_simp_attr', 'register_tactic_tag', 'register_try?_tactic', 'renaming', 'repeat', 'reportDbgIssue!',
    'reportEMatchIssue!', 'reportIssue!', 'reprove', 'return', 'rexp', 'run_cmd', 'run_elab', 'run_meta', 's!',
    'says', 'scoped', 'seal', 'section', 'set_library_suggestions', 'set_option', 'sf', 'show', 'show_panel_widgets',
    'show_term', 'show_term_elab', 'simproc', 'simproc_decl', 'single₀', 'skip', 'sorry', 'stacks',
    'store_traces_as', 'structure', 'sudo', 'suffices', 'suppress_compilation', 'syntax', 'tactic_alt',
    'tactic_extension', 'tactic_name', 'tactic_tag', 'termination_by', 'termination_by?', 'test_extern', 'then',
    'theorem', 'theorem_wanted', 'throwError', 'throwErrorAt', 'throwNamedError', 'throwNamedErrorAt', 'to',
    'to_additive_name_hint', 'to_dual_insert_cast', 'to_dual_insert_cast_fun', 'to_dual_name_hint',
    'trailing_parser', 'try', 'typeLT', 'unif_hint', 'universe', 'unless', 'unlock_limits', 'unreachable!', 'unsafe',
    'unseal', 'unset_option', 'unsuppress_compilation', 'until', 'update₀', 'using', 'using!', 'variable',
    'variable?', 'variables', 'wait_for_cancel_once_command', 'whatsnew', 'where', 'while', 'with',
    'with_annotate_term', 'with_weak_namespace', 'without_check_deprecated', 'without_expected_type', 'Γ_', 'Γ₀',
    'Δ', 'Ι', 'Λ', 'Ω', 'α_', 'αᵣ', 'αₗ', 'β_', 'γ', 'δ', 'ε', 'ε_', 'ε₀', 'ζ', 'η', 'η_', 'θ', 'ι', 'μ', 'π', "π'",
    'π_', 'πₓ', 'πₘ', 'ρ_', 'ρᵣ', 'σ', 'τ', 'φ', 'ψ', 'ω', 'ω_', 'ω₁', 'ℂ', 'ℍ', 'ℑ', 'ℕ', 'ℙ', 'ℚ', 'ℛ', 'ℜ', 'ℝ',
    'ℤ', 'ℵ_', 'ℵ₀', 'ℵ₁', 'ℶ_', '𝒟', '𝒫', '𝒮', '𝒮ℒ', '𝓒', '𝓓', '𝓕', '𝓝', '𝓞', '𝓟', '𝓡', '𝓤', '𝔠', '𝔹', '𝔻', '𝔼',
    '𝕊', '𝕋', '𝕔𝔻',
})


class _LeanLexer:
    def __init__(self, src):
        self.s = src.replace("\r\n", "\n")   # String.crlfToLf (Parser.mkInputContext normalizeLineEndings)
        self.n = len(self.s)
        self.memo = {}

    def at(self, i):
        return self.s[i] if 0 <= i < self.n else "\x00"

    def fail(self, why, i, cls=LeanSourceUnclear):
        raise cls("%s (line %d)" % (why, self.s.count("\n", 0, max(0, min(i, self.n))) + 1))

    def bad(self, why, i):   # a Lean syntax error (see _LeanSyntaxError)
        self.fail(why, i, _LeanSyntaxError)

    def check_meta(self, comps, i):   # a component naming the meta-programming layer
        for c in comps:
            if c in _LEAN_META_COMPONENTS:
                self.fail("`%s` (meta-programming: elaboration-time code)" % c[:40], i)

    def whitespace(self, i):   # Parser.whitespace
        s, n = self.s, self.n
        while i < n:
            c = s[i]
            if c == "\t":
                self.bad("tab character (a Lean error)", i)
            if c == "\r":
                self.bad("isolated carriage return (a Lean error)", i)
            if c == " " or c == "\n":
                i += 1
            elif c == "-" and self.at(i + 1) == "-":
                j = s.find("\n", i + 2)
                i = n if j < 0 else j
            elif c == "/" and self.at(i + 1) == "-":
                if self.at(i + 2) in ("-", "!"):
                    return i   # `/--`, `/-!`: doc comment tokens
                i = self.comment_body(i + 3, i)   # (the character right after `/-` is skipped, as in Lean)
            else:
                return i
        return i

    def comment_body(self, i, start):   # finishCommentBlock with nesting 1
        s, n = self.s, self.n
        nest = 1
        while True:
            if i >= n:
                self.bad("unterminated comment", start)
            c = s[i]
            i += 1
            if c == "-":
                if i >= n:
                    self.bad("unterminated comment", start)
                if s[i] == "/":
                    i += 1
                    nest -= 1
                    if nest == 0:
                        return i
            elif c == "/":
                if i >= n:
                    self.bad("unterminated comment", start)
                if s[i] == "-":
                    i += 1
                    nest += 1

    def quoted(self, i, interp, in_string, start):   # quotedCharCoreFn; i = position after the backslash
        if i >= self.n:
            self.bad("unterminated escape sequence", start)
        c = self.s[i]
        if c in "\\\"'rnt" or (interp and c == "{"):
            return i + 1
        if c == "x" or c == "u":
            k = 2 if c == "x" else 4
            for j in range(i + 1, i + 1 + k):
                if j >= self.n or not _lean_hex(self.s[j]):
                    self.bad("invalid hexadecimal escape", start)
            return i + 1 + k
        if in_string and c == "\n":   # string gap: exactly one newline, then whitespace
            j, seen = i, False
            while j < self.n:
                d = self.s[j]
                if d == "\n":
                    if seen:
                        self.bad("additional newline in string gap", start)
                    seen = True
                elif d not in " \t\r":
                    break
                j += 1
            return j
        self.bad("invalid escape sequence", start)

    def str_plain(self, i):   # strLitFnAux; i at the opening quote
        s, n = self.s, self.n
        j = i + 1
        while True:
            if j >= n:
                self.bad("unterminated string literal", i)
            c = s[j]
            j += 1
            if c == '"':
                return j
            if c == "\\":
                j = self.quoted(j, False, True, i)

    def str_interp(self, i, depth):   # interpolatedStrFn; `{ term }` = code up to the matching `}`
        s, n = self.s, self.n
        j = i + 1
        toks = []
        while True:
            if j >= n:
                self.bad("unterminated string literal", i)
            c = s[j]
            j += 1
            if c == '"':
                return j, toks
            if c == "\\":
                j = self.quoted(j, True, True, i)
            elif c == "{":
                j, t = self.code(self.whitespace(j), depth + 1, True)
                toks.extend(t)
                j += 1

    def str_lit(self, i, depth):
        if i in self.memo:
            return self.memo[i]
        perr = ierr = None
        pe = ie = None
        itoks = []
        try:
            pe = self.str_plain(i)
        except LeanSourceUnclear as e:
            perr = e
        try:
            ie, itoks = self.str_interp(i, depth)
        except LeanSourceUnclear as e:
            ierr = e
        if perr is not None and ierr is not None:
            raise perr
        if perr is None and isinstance(ierr, _LeanSyntaxError):
            # read as interpolated the text is a Lean syntax error (e.g. `"{"`): if Lean
            # reads it that way the file fails anyway; a valid file reads it as the plain string
            self.memo[i] = (pe, [])
            return pe, []
        if perr is not None or ierr is not None or pe != ie:
            self.fail("string literal reads differently as a plain and as an interpolated string", i)
        self.memo[i] = (pe, itoks)
        return pe, itoks

    def char_lit(self, i):   # charLitFnAux; i at the quote
        j = i + 1
        if j >= self.n:
            self.bad("unterminated character literal", i)
        c = self.s[j]
        j += 1
        if c == "\\":
            j = self.quoted(j, False, False, i)
        if j >= self.n or self.s[j] != "'":
            self.bad("missing end of character literal", i)
        return j + 1

    def raw_start(self, i):   # isRawStrLitStart; i = position after the `r`
        while i < self.n and self.s[i] == "#":
            i += 1
        return i < self.n and self.s[i] == '"'

    def raw_str(self, i):   # rawStrLitFnAux; i at the `r`
        s, n = self.s, self.n
        j, num = i + 1, 0
        while s[j] == "#":
            num += 1
            j += 1
        j += 1
        while True:
            if j >= n:
                self.bad("unterminated raw string literal", i)
            c = s[j]
            j += 1
            if c != '"':
                continue
            if num == 0:
                return j
            closing = 0
            while True:
                if j >= n:
                    self.bad("unterminated raw string literal", i)
                c = s[j]
                j += 1
                if c == "#":
                    if closing + 1 == num:
                        return j
                    closing += 1
                elif c == '"':
                    closing = 0
                else:
                    break

    def number(self, i):   # numberFnAux; on a Lean error: the digits only (a projection index like `h.1.le`)
        s, n = self.s, self.n

        def digits(j, isdig, need):
            while True:
                if j >= n:
                    return None if need else j
                c = s[j]
                if c == "_":
                    need = True
                elif isdig(c):
                    need = False
                elif need:
                    return None
                else:
                    return j
                j += 1

        def exact():
            d = self.at(i + 1)
            if s[i] == "0" and d in "bB":
                return digits(i + 2, lambda x: x in "01", True)
            if s[i] == "0" and d in "oO":
                return digits(i + 2, lambda x: "0" <= x <= "7", True)
            if s[i] == "0" and d in "xX":
                return digits(i + 2, _lean_hex, True)
            j = digits(i + 1, _lean_digit, False)
            if j is None or j >= n:
                return j
            cur = s[j]
            if cur == "." and self.at(j + 1) == ".":
                return j
            if cur not in ".eE":
                return j
            bare = False
            if cur == ".":
                if _lean_digit(self.at(j + 1)):
                    j = digits(j + 1, _lean_digit, False)
                else:
                    j, bare = j + 1, True
            if j is None or j >= n:
                return j
            cur = s[j]
            if cur in "eE":
                k = j + 1
                if self.at(k) in "-+":
                    k += 1
                return digits(k, _lean_digit, False) if _lean_digit(self.at(k)) else None
            if bare and (_lean_id_first(cur) or cur == "«"):
                return None
            return j
        j = exact()
        if j is None:
            j = i
            while j < n and _lean_digit(s[j]):
                j += 1
        return j

    def ident(self, i):   # identFnAux: dotted components, «» escapes
        s, n = self.s, self.n
        comps, j = [], i
        while True:
            c = self.at(j)
            if c == "«":
                k = s.find("»", j + 1)
                if k < 0:
                    self.bad("unterminated identifier escape", j)
                comps.append(s[j + 1:k])
                j = k + 1
            else:
                k = j + 1
                while k < n and _lean_id_rest(s[k]):
                    k += 1
                comps.append(s[j:k])
                j = k
            if self.at(j) == "." and j + 1 < n and (_lean_id_first(s[j + 1]) or s[j + 1] == "«"):
                j += 1
                continue
            return j, s[i:j], comps

    def code(self, i, depth, until_brace):   # a token stream; until_brace: stop at the `}` closing an interpolation
        if depth > _LEAN_MAX_NEST:
            self.fail("string interpolation nested too deeply", i)
        s, n = self.s, self.n
        toks, braces = [], 0
        i = self.whitespace(i)
        while i < n:
            c = s[i]
            if c == '"':
                j, _inner = self.str_lit(i, depth)   # the tokens of an interpolation are terms: not counted
                toks.append(("str", s[i:j], None, i))
            elif c == "'":
                if self.at(i + 1) == "'":
                    self.fail("`''` token (cannot be read without the token table)", i)
                j = self.char_lit(i)
                toks.append(("char", s[i:j], None, i))
            elif _lean_digit(c):
                j = self.number(i)
                toks.append(("num", s[i:j], None, i))
            elif c == "`":
                if not (_lean_id_first(self.at(i + 1)) or self.at(i + 1) == "«"):
                    self.fail("backtick that does not start a name literal (syntax quotation)", i)
                j, text, comps = self.ident(i + 1)
                self.check_meta(comps, i)
                toks.append(("namelit", text, comps, i))
            elif c == "r" and self.raw_start(i + 1):
                j = self.raw_str(i)
                toks.append(("str", s[i:j], None, i))
            elif s.startswith("/--", i) or s.startswith("/-!", i):
                # Lean 4.36+ (docCommentOpen) skips only whitespace characters after the opener, 4.33.1
                # skips comments too: a comment there is read differently by the deployed toolchains -> refused
                k = i + 3
                while k < n and s[k] in " \n":
                    k += 1
                if s.startswith("--", k) or (s.startswith("/-", k) and self.at(k + 2) not in ("-", "!")):
                    self.fail("comment right after a doc comment opener (read differently by Lean 4.33 and 4.36+)", i)
                j = self.comment_body(self.whitespace(i + 3), i)
                toks.append(("doc", s[i:j], None, i))
            elif c == "«" or _lean_id_first(c):
                j, text, comps = self.ident(i)
                c0 = comps[0] if len(comps) == 1 else None
                c0s = c0.rstrip("!?") if c0 is not None else None   # `simps!`, `simps?`, `to_additive?`, `reassoc!`
                if c0 is not None and (c0s in _LEAN_UNCLEAR_IDENTS or c0.startswith("builtin_") or c0.startswith("declare_")
                                       or c0.startswith("register_") or "simproc" in c0):
                    self.fail("`%s` (syntax / elaboration-time code / generated theorems)" % c0[:40], i)
                self.check_meta(comps, i)
                if comps[:2] == ["doc", "verso"]:
                    self.fail("doc.verso option (Verso doc comments)", i)
                toks.append(("ident", text, comps, i))
            else:
                if until_brace and c == "}" and braces == 0:
                    return i, toks
                if until_brace and c == "{":
                    braces += 1
                elif until_brace and c == "}":
                    braces -= 1
                j = i + 1
                if c == "#" and _lean_id_first(self.at(j)):
                    k = j
                    while k < n and _lean_id_rest(s[k]):
                        k += 1
                    if s[j:k] not in _LEAN_HASH_OK:
                        self.fail("`#%s` (only %s are read; #eval runs code, #guard_msgs hides errors, #exit stops)"
                                  % (s[j:k][:30], "/".join(sorted(_LEAN_HASH_OK))[:60]), i)
                if self.at(j) == "r" and self.raw_start(j + 1):   # Mathlib `~r`, `<r`: `~r"\"..` is `~r` + a PLAIN string
                    self.fail("symbol %r directly followed by a raw-string opener (may be one longer token, e.g. `~r`)" % c, i)
                if c not in _LEAN_SAFE_BEFORE and (self.at(j) in "\"'`" or s.startswith("--", j)
                                                   or s.startswith("/-", j)):
                    self.fail("symbol %r directly followed by a quote or comment opener (may be one longer token)" % c, i)
                toks.append(("sym", c, None, i))
            i = self.whitespace(j)
        if until_brace:
            self.bad("unterminated string interpolation", i)
        return i, toks


def _lean_plain_comp(c):   # a name component Lean prints without «» (identifier characters only)
    return bool(c) and _lean_id_first(c[0]) and all(_lean_id_rest(x) for x in c[1:])


def lean_declared_theorems(src):
    """the theorems a Lean source declares under user-chosen names, read with the Lean-tokenizer mirror above, as the
    KERNEL names Lean gives them: the active `namespace`s are prefixed, `_root_.` is interpreted, `«»`
    decoded; a name that cannot be computed here (a `private` declaration: `_private.<module>.0.<name>`; an anonymous
    instance or a derived Prop instance: generated name; a component that needs `«»`) is None. Counted declarations:
    `theorem`; `lemma` (a keyword only with Mathlib / Batteries imported: without such an import any `lemma` token is
    refused, it may be an identifier); `instance` (an instance of a Prop-valued class IS a theorem); `deriving` a class
    outside _LEAN_DATA_DERIVE. NOT counted (documented): auxiliary theorems Lean generates under DOTTED names (`t.helper` of
    `where`, `t._proof_N`, `f._proof_N`, `t._simp_N`, structure / inductive lemmas) - a dotted name is never an inference
    target (fv_schema.validate_theorem_name(allow_dotted=False)); generators with undotted names are refused by the lexer
    (`to_additive`, `irreducible_def`, `alias`, ...). LeanSourceUnclear if the source cannot be read unambiguously."""
    if src.startswith("\ufeff"):
        raise LeanSourceUnclear("byte order mark at the start (Lean rejects the file)")
    lx = _LeanLexer(src)
    try:
        _, toks = lx.code(0, 0, False)
    except RecursionError:
        raise LeanSourceUnclear("source nested too deeply") from None
    nt = len(toks)

    def tok(k):
        return toks[k] if 0 <= k < nt else (None, None, None, lx.n)

    def is_id(k, text=None):
        t = tok(k)
        return t[0] == "ident" and (text is None or t[1] == text)

    def is_sym(k, c):
        t = tok(k)
        return t[0] == "sym" and t[1] == c

    # header: `module` (default-private names) is refused; imports decide whether `lemma` is a keyword
    k = 0
    if is_id(0, "module"):
        lx.fail("`module` file (declarations are private by default)", tok(0)[3])
    if is_id(0, "prelude"):
        k = 1
    imports = []
    while is_id(k, "import") or ((is_id(k, "public") or is_id(k, "meta")) and is_id(k + 1, "import")):
        k += 1 if is_id(k, "import") else 2
        if not is_id(k):
            lx.fail("malformed import", tok(k)[3])
        imports.append(tok(k)[2])
        k += 1
    lemma_kw = any(tuple(c or ()) in _LEAN_LEMMA_IMPORTS for c in imports)   # not any Mathlib / Batteries submodule

    scopes = []   # one entry per namespace component (its name) / section component or mutual block (None)
    cur_cmd = [None]   # the declaration keyword of the command being read
    names = []

    def ns_prefix():
        return [x for x in scopes if x is not None]

    def modifiers_before(k):   # the modifier idents / attribute groups / doc comment right before position k
        mods = set()
        j = k - 1
        while j >= 0:
            t = toks[j]
            if t[0] == "ident" and t[1] in _LEAN_DECL_MODIFIERS:
                mods.add(t[1])
                j -= 1
            elif t[0] == "doc":
                j -= 1
            elif t[0] == "sym" and t[1] == "]":   # an attribute group `@[ ... ]`: skip back to its `@[`
                depth, m = 0, j
                while m >= 0:
                    if toks[m][0] == "sym" and toks[m][1] == "]":
                        depth += 1
                    elif toks[m][0] == "sym" and toks[m][1] == "[":
                        depth -= 1
                        if depth == 0:
                            break
                    m -= 1
                if m >= 1 and toks[m - 1][:2] == ("sym", "@"):
                    j = m - 2
                else:
                    break
            else:
                break
        return mods

    def kernel_name(comps, mods):
        if "private" in mods:
            return None
        comps = list(comps)
        if comps and comps[0] == "_root_":
            comps = comps[1:]
        else:
            comps = ns_prefix() + comps
        if not comps or not all(_lean_plain_comp(c) for c in comps):
            return None
        return ".".join(comps)

    def is_name(j):   # an identifier that is not a keyword (a keyword is never a name; «...» escapes are names)
        return is_id(j) and tok(j)[1] not in _LEAN_KEYWORDS

    def opt_scope_name(k, pos):
        """the optional name after `section` / `end` (Lean: `optional (checkColGt >> ident)`):
        a keyword is never that name - the scope is anonymous and the keyword starts the next command (not consumed);
        a name on the same line is the name; a non-keyword identifier on a LATER line (an indented name, or a parse
        error) is refused"""
        if not is_id(k + 1) or tok(k + 1)[1] in _LEAN_KEYWORDS:
            return None
        if lx.s.count("\n", pos, tok(k + 1)[3]) == 0:
            return tok(k + 1)[2]
        lx.fail("identifier on the line after `%s` (an indented scope name?)" % tok(k)[1], pos)

    while k < nt:
        kind, text, comps, pos = toks[k]
        if kind == "sym" and text == "@" and is_sym(k + 1, "[") or kind == "ident" and text == "attribute" and is_sym(k + 1, "["):
            # every attribute instance's name must be on _LEAN_ATTR_OK (`@[a, local b x, -c]`);
            # anything else may declare theorems (`ext`, `to_fun`, `to_set_notation`, ...) -> refused
            depth, j, start = 0, k + 1, True
            while j < nt:
                if is_sym(j, "[") or is_sym(j, "(") or is_sym(j, "{"):
                    depth += 1
                    if depth == 1:
                        start = True
                elif is_sym(j, "]") or is_sym(j, ")") or is_sym(j, "}"):
                    depth -= 1
                    if depth == 0:
                        break
                elif depth == 1 and is_sym(j, ","):
                    start = True
                elif depth == 1 and start:
                    if is_id(j, "local") or is_id(j, "scoped") or is_sym(j, "-"):
                        pass
                    elif is_id(j) and tok(j)[1] in _LEAN_ATTR_OK:
                        start = False
                    else:
                        lx.fail("attribute %r is not on the allow-list of attributes that declare no theorem"
                                % (tok(j)[1] or "?")[:40], tok(j)[3])
                j += 1
            if j >= nt:
                lx.fail("unterminated attribute list", pos)
            k = j + 1   # nothing inside an attribute list is a declaration (`[local instance]` is the attribute)
            continue
        if kind == "ident" and (text in _LEAN_CMD_KEYWORDS or text in _LEAN_DECL_MODIFIERS) and (
                (is_sym(k - 1, ".") and tok(k - 1)[3] + 1 == pos) or is_sym(k - 1, "|")):
            # `.theorem`, `..theorem`, `s |>.end`, `| section` (a constructor): Lean reads a raw
            # identifier there, not the keyword - refused (skipping only `.theorem` would let `..theorem` through)
            lx.fail("keyword `%s` in an identifier position (after `.` or `|`)" % text, pos)
        if kind != "ident":
            k += 1
            continue
        if text == "namespace":
            if not is_name(k + 1):
                lx.fail("`namespace` without a name (or with a keyword)", pos)
            c = tok(k + 1)[2]
            if c and c[0] == "_root_":
                lx.fail("`namespace _root_...`", pos)
            scopes.extend(c)
            k += 2
            continue
        if text == "section":
            c = opt_scope_name(k, pos)
            if c is not None:
                scopes.extend([None] * len(c))
                k += 2
            else:
                scopes.append(None)
                k += 1
            continue
        if text == "mutual":
            scopes.append(None)
            k += 1
            continue
        if text == "end":
            c = opt_scope_name(k, pos)
            cnt = len(c) if c is not None else 1
            if cnt > len(scopes):
                lx.fail("`end` without an open namespace / section", pos)
            del scopes[len(scopes) - cnt:]
            k += 2 if c is not None else 1
            continue
        if text == "lemma" and not lemma_kw:
            lx.fail("`lemma` without a Mathlib / Batteries import (an identifier in core Lean, a keyword with them)", pos)
        if text in ("theorem", "lemma", "def", "abbrev", "example", "opaque", "instance", "structure", "class",
                    "inductive", "axiom"):
            cur_cmd[0] = text
        if text == "where" and cur_cmd[0] in ("theorem", "lemma", "def", "abbrev", "example", "opaque") and not (
                is_sym(k - 1, "#") and tok(k - 1)[3] + 1 == pos):   # `#where` is a diagnostic command
            # `where` helpers (and `let rec`) of a theorem / definition are declarations of their own
            # (`t.step`, possibly theorems): refused (structure / class / instance / inductive `where` is plain syntax)
            lx.fail("`where` clause of a %s (declares auxiliary constants)" % cur_cmd[0], pos)
        if text == "rec" and is_id(k - 1, "let"):
            lx.fail("`let rec` (declares an auxiliary constant)", pos)
        if text in ("theorem", "lemma"):
            if not is_name(k + 1):
                lx.fail("`%s` not followed by a name (a keyword or a symbol follows)" % text, pos)
            names.append(kernel_name(tok(k + 1)[2], modifiers_before(k)))
            k += 2
            continue
        if text == "instance" and not is_id(k - 1, "deriving") and not is_sym(k - 1, "[") and not is_sym(k - 1, ","):
            # (`[instance]` / `, instance` = the attribute, not a declaration)
            mods = modifiers_before(k)
            j = k + 1
            if is_sym(j, "(") and is_id(j + 1, "priority"):
                depth = 0
                while j < nt:
                    if is_sym(j, "("):
                        depth += 1
                    elif is_sym(j, ")"):
                        depth -= 1
                        if depth == 0:
                            break
                    j += 1
                j += 1
            # counted (an instance of a Prop-valued class IS a theorem), but never an inferable name:
            # a DATA instance is a definition, and the source cannot tell which one it is
            names.append(None)
            k = j
            continue
        if text == "deriving":
            j = k + 1
            if is_id(j, "instance"):
                j += 1
            classes = []
            while is_name(j):
                classes.append(tok(j)[1])
                j += 1
                if is_sym(j, ","):
                    j += 1
                else:
                    break
            if not classes or any(c not in _LEAN_DATA_DERIVE for c in classes):
                names.append(None)   # a derived instance of a (possibly) Prop-valued class: a theorem with a generated name
            k = j
            continue
        k += 1
    return names


def strict_json_loads(raw_bytes):
    def bad_const(x):
        raise ValueError(f"non-standard JSON constant {x!r}")

    def no_dups(pairs):   # a duplicate key (e.g. two "theorem" fields) is refused, never last-key-wins
        seen = set()
        for k, _ in pairs:
            if k in seen:
                raise ValueError(f"duplicate key {k[:64]!r} in a JSON object")
            seen.add(k)
        return dict(pairs)
    return json.loads(raw_bytes.decode("utf-8", errors="strict"), parse_constant=bad_const, object_pairs_hook=no_dups)


_TARGET_NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
# fvserve's fixed refusal text for a problem set whose challenge fails a rule of its release's own comparator (the only
# two-field backend reply that is a rejection; tools/fvserve/fvserve.py bad_request)
_FVSERVE_GATE_REJECT = "REJECTED by the cross-version gate (a rule of the challenge release's own comparator fails)"


def valid_target_name(name):
    """the target names fvapi can address: an undotted ASCII identifier [A-Za-z_][A-Za-z0-9_']*, matched EXACTLY
    (fullmatch: no trailing line feed, which fv_schema's `$`-anchored match lets through), and fv_schema's own rules"""
    return (isinstance(name, str) and _TARGET_NAME_RE.fullmatch(name) is not None
            and fv_schema.validate_theorem_name(name, allow_dotted=False))


def resolve_theorem_name(source, explicit_name=None, custom_id=None, custom_id_is_theorem=False, allow_inference=False):
    """Resolve target theorem name safely (defense against cross-problem reward hacking):
      1. Explicit `theorem` always wins (strictly validated; invalid -> ('REJECTED', reason)).
      2. If `--custom-id-is-theorem` and `custom_id` given, `theorem := custom_id` (strictly validated).
      3. Only when `--experimental-theorem-inference` is explicitly set (EXPERIMENTAL in v0.1), infer from `source` — and refuse
         with ('NO-VERDICT', 'ambiguous theorem declaration') if `source` declares != 1 theorem/lemma.
      4. Otherwise fail closed: ('NO-VERDICT', 'missing required theorem name').
    every failure here is NO-VERDICT: no check ran, so there is no verdict to report (the attempt
    envelope then carries trust 'none'; never REJECTED with trust 'sound').
    Returns (theorem_name_or_None, err_verdict_or_None, err_reason_or_None)."""
    if explicit_name is not None:
        if valid_target_name(explicit_name):
            return explicit_name, None, None
        return None, "NO-VERDICT", "bad theorem name"
    if custom_id_is_theorem and custom_id is not None:
        cid_s = str(custom_id)
        if valid_target_name(cid_s):
            return cid_s, None, None
        return None, "NO-VERDICT", "bad custom_id theorem name"
    if allow_inference and isinstance(source, str):
        try:
            found = lean_declared_theorems(source)
        except LeanSourceUnclear as e:
            return None, "NO-VERDICT", f"cannot infer the theorem from this source ({e}); pass explicit 'theorem'"
        except Exception as e:   # noqa: BLE001  (a lexer fault is never a crash, never a guess)
            return None, "NO-VERDICT", f"cannot infer the theorem from this source (internal: {type(e).__name__}); pass explicit 'theorem'"
        if len(found) == 1 and found[0] is not None and valid_target_name(found[0]):
            return found[0], None, None
        if len(found) > 1:
            shown = [x if x is not None else "<generated/private name>" for x in found[:4]]
            return None, "NO-VERDICT", f"ambiguous: source declares {len(found)} theorems/lemmas/instances ({shown}); pass explicit 'theorem'"
        if len(found) == 1 and found[0] is None:
            return None, "NO-VERDICT", ("the only declaration found is an instance, a derived instance or a private / escaped "
                                        "theorem: its kind or its name cannot be determined from the source; pass explicit "
                                        "'theorem' if it is a theorem fvapi can address (an undotted ASCII name)")
        if len(found) == 1:
            return None, "NO-VERDICT", ("the only declared theorem is %s, a name fvapi cannot address (only undotted ASCII "
                                        "identifiers can be checked through fvapi; use bin/fv check / bin/fastverify)" % found[0])
        return None, "NO-VERDICT", "no theorem declaration found in source; pass explicit 'theorem'"
    return None, "NO-VERDICT", "missing required 'theorem' field (pass explicit 'theorem', or start fvapi with --custom-id-is-theorem / --experimental-theorem-inference)"


class ApiState:
    def __init__(self, args):
        self.args = args
        self.fvserve_state = os.path.realpath(args.fvserve_state)
        self.default_pset = args.default_pset
        self.max_body_bytes = args.max_body_bytes
        self.max_source_bytes = args.max_source_bytes
        self.max_batch = args.max_batch
        self.request_timeout = args.request_timeout
        self.socket_timeout = args.socket_timeout
        self.header_timeout = args.header_timeout
        self.body_timeout = args.body_timeout
        self.sem = threading.BoundedSemaphore(args.max_concurrent)
        self.max_concurrent = args.max_concurrent
        self.max_connections = max(8, args.max_connections if args.max_connections > 0 else max(2 * args.max_concurrent, 64))
        self.conn_sem = threading.BoundedSemaphore(self.max_connections)
        self.active_connections = 0
        self.custom_id_is_theorem = bool(args.custom_id_is_theorem)
        self.allow_theorem_inference = bool(args.allow_theorem_inference)
        self.backend_sem = threading.BoundedSemaphore(args.max_backend_concurrent)
        self.max_backend_concurrent = args.max_backend_concurrent
        self.backend_pool = cf.ThreadPoolExecutor(max_workers=args.max_backend_concurrent)
        self.api_key = None
        if args.api_key_file:
            self.api_key = open(args.api_key_file, "r", encoding="utf-8").read().strip()
            if not self.api_key:
                raise SystemExit("fvapi: --api-key-file is empty")
        self.lock = threading.Lock()
        self.t0 = time.time()
        self.inflight = 0
        self.req_counts = collections.Counter()
        self.verdict_counts = collections.Counter()
        self.lat_sum = 0.0
        self.lat_count = 0
        self.audit_log = open(args.audit_log, "a", encoding="utf-8") if args.audit_log else None

    @staticmethod
    def label_inferred(env, resolved=True):
        """the EXPERIMENTAL marker inside result-v1: `target` allows extra members (the top-level object
        does not), and `warnings` is a list of strings. resolved=False: inference was attempted and refused - the
        experimental-mode label stays, the success flag / wording does not"""
        tgt = env.get("target")
        if not isinstance(tgt, dict):
            tgt = env["target"] = {}
        tgt["theorem_inference"] = "experimental"
        tgt["theorem_inferred"] = bool(resolved)
        w = env.get("warnings")
        if not isinstance(w, list):
            w = env["warnings"] = []
        msg = ("target theorem inferred from the source by EXPERIMENTAL theorem inference (not reward-safe; pass 'theorem')"
               if resolved else "EXPERIMENTAL theorem inference could not determine a target (no check ran; see 'reason')")
        # the recovery advice is the reason's (it knows whether 'theorem' can address the name)
        if msg not in w:
            w.append(msg)
        env.pop("theorem_inference", None)

    def pset_theorems(self, pset):
        """the theorem names of problem set `pset` from fvserve's private copy of its comparator.json
        (<fvserve-state>/psets/<pset>/comparator.json), or None if it cannot be read (then fvserve's check decides)"""
        if not isinstance(pset, str) or not fv_schema.validate_theorem_name(pset, allow_dotted=False):
            return None
        p = os.path.join(self.fvserve_state, "psets", pset, "comparator.json")
        try:
            fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
            with os.fdopen(fd, "rb") as f:
                import stat as _stat
                if not _stat.S_ISREG(os.fstat(f.fileno()).st_mode):
                    return None
                raw = f.read(1 << 22)
            cfg = strict_json_loads(raw)
            names = cfg.get("theorem_names") if isinstance(cfg, dict) else None
            if not isinstance(names, list) or not all(isinstance(x, str) for x in names):
                return None
            return frozenset(names)
        except (OSError, ValueError):
            return None

    def record_audit(self, entry):
        if not self.audit_log:
            return
        entry["ts"] = round(time.time(), 3)
        with self.lock:
            self.audit_log.write(json.dumps(entry) + "\n")
            self.audit_log.flush()

    def backend_stats(self, timeout=5.0):
        return fvserve.request(self.fvserve_state, {"op": "stats"}, timeout=timeout)

    def verify_one(self, pset, theorem, source, timeout=None, custom_id=None):
        t0 = time.time()
        tmo = min(float(timeout or self.request_timeout), self.request_timeout)
        if not isinstance(pset, str) or not pset:
            return fv_schema.from_error("attempt", "missing pset", 0.0, target={"pset": pset, "theorem": theorem}), None
        if not isinstance(source, str) or not source.strip():
            return fv_schema.from_error("attempt", "missing or empty source", 0.0, target={"pset": pset, "theorem": theorem}), None
        if len(source.encode("utf-8", "replace")) > self.max_source_bytes:
            return fv_schema.from_error("attempt", f"source exceeds {self.max_source_bytes} bytes", 0.0,
                                        target={"pset": pset, "theorem": theorem}), None
        thm, err_verdict, err_reason = resolve_theorem_name(
            source,
            explicit_name=theorem,
            custom_id=custom_id,
            custom_id_is_theorem=self.custom_id_is_theorem,
            allow_inference=self.allow_theorem_inference,
        )
        inferred = bool(thm) and theorem is None and not (self.custom_id_is_theorem and custom_id is not None)
        if thm and valid_target_name(thm):
            names = self.pset_theorems(pset)
            if names is not None and thm not in names:
                # a target that is not a theorem of the problem set was never judged: NO-VERDICT
                # with trust 'none' (not REJECTED) - explicit, custom-id and inferred targets alike
                env = fv_schema.make_envelope(
                    mode="attempt", verdict="NO-VERDICT", trust="none",
                    verdict_basis=f"no verdict (no check ran): {thm!r} is not a theorem of problem set {pset!r}",
                    total_s=time.time() - t0, reason=f"theorem {thm!r} is not a theorem of problem set {pset!r}",
                    target={"pset": pset, "theorem": thm},
                    diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", f"{thm!r} not in problem set {pset!r}"))
                if inferred:
                    self.label_inferred(env)
                return self.finish_backend(env, None, time.time() - t0, custom_id)   # custom_id + counted
        if not thm or not valid_target_name(thm):
            # no target could be resolved, so NO check ran: this is never a verdict with the 'sound'
            # label (not REJECTED / trust sound / exit 1 for e.g. an unreadable or theorem-less source) - it is
            # NO-VERDICT with trust 'none' (reward 0, exit 2), whatever the reason (bad / missing name, inference refused)
            why = err_reason or "bad theorem name"
            env = fv_schema.make_envelope(
                mode="attempt",
                verdict="NO-VERDICT",
                trust="none",
                verdict_basis=f"no verdict (no check ran: the target theorem was not resolved): {why}",
                total_s=time.time() - t0,
                reason=why,
                target={"pset": pset, "theorem": theorem},
                diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", why),
            )
            if theorem is None and self.allow_theorem_inference and not (self.custom_id_is_theorem and custom_id is not None):
                self.label_inferred(env, resolved=False)
            return self.finish_backend(env, None, time.time() - t0, custom_id)   # custom_id + counted
        try:
            with self.backend_sem:
                deadline = t0 + tmo
                last_err = None
                raw = None
                for attempt_i in range(8):
                    rem = max(1.0, deadline - time.time())
                    try:
                        raw = fvserve.request(
                            self.fvserve_state,
                            {"op": "verify", "pset": pset, "theorem": thm, "source": source},
                            timeout=rem,
                        )
                        break
                    except OSError as oe:
                        # Retry transient AF_UNIX listen-backlog overflow (EAGAIN / EWOULDBLOCK)
                        if oe.errno in (errno.EAGAIN, errno.EWOULDBLOCK, errno.ECONNREFUSED) and attempt_i < 7 and time.time() + 0.05 < deadline:
                            last_err = oe
                            time.sleep(min(0.15, 0.015 * (1.5 ** attempt_i) + random.uniform(0.0, 0.01)))
                            continue
                        raise
                if raw is None:
                    raise last_err or RuntimeError("fvserve request failed")
        except socket.timeout:
            env = fv_schema.make_envelope(   # no check completed: trust 'none'
                mode="attempt",
                verdict="NO-VERDICT",
                trust="none",
                verdict_basis=f"fvserve request timed out after {tmo:.1f}s (fail-closed)",
                total_s=time.time() - t0,
                reason=f"timeout ({tmo:.1f}s)",
                target={"pset": pset, "theorem": thm},
                diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", f"timeout ({tmo:.1f}s)"),
            )
            if inferred:
                self.label_inferred(env)
            return self.finish_backend(env, None, time.time() - t0, custom_id)   # custom_id + counted
        except Exception as e:  # noqa: BLE001
            env = fv_schema.make_envelope(
                mode="attempt",
                verdict="NO-VERDICT",
                trust="none",
                verdict_basis=f"fvserve backend unavailable: {fv_schema.sanitize_single_line(e, 200)}",
                total_s=time.time() - t0,
                reason=f"backend error: {fv_schema.sanitize_single_line(e, 200)}",
                target={"pset": pset, "theorem": thm},
                diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", str(e)),
            )
            if inferred:
                self.label_inferred(env)
            return self.finish_backend(env, None, time.time() - t0, custom_id)   # custom_id + counted
        wall = time.time() - t0
        if (isinstance(raw, dict) and "why" in raw and set(raw) <= {"verdict", "why"}   # fvserve's refusal reply is exactly {verdict, why}
                and not (raw.get("verdict") == "REJECTED"   # only the gate's OWN reason, EXACTLY (fvserve's constant)
                         and raw.get("why") == _FVSERVE_GATE_REJECT)):
            # fvserve refused the request before any check (bad / unresolvable name, unknown problem set, full queue):
            # NO-VERDICT with trust 'none', whatever verdict word the backend used (older fvserve versions said REJECTED for a
            # bad name); only the cross-version gate's own rule ("REJECTED by the cross-version gate ...") is a rejection
            why = fv_schema.sanitize_single_line(raw.get("why"), 300)
            env = fv_schema.make_envelope(
                mode="attempt", verdict="NO-VERDICT", trust="none",
                verdict_basis=f"no verdict (fvserve refused the request before any check): {why}",
                total_s=wall, reason=why, target={"pset": pset, "theorem": thm},
                diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", why))
            if inferred:
                self.label_inferred(env)
            return self.finish_backend(env, raw, wall, custom_id)
        if isinstance(raw, dict) and raw.get("why") == "not a theorem name of the problem set" and raw.get("build_exit") is None:
            # EXACT refusal string of batchverify and no build ran: a submitter can put this text into a
            # Lean error, which batchverify copies into `why` - that judged REJECTED must stay REJECTED
            # batchverify's lookup failure is answered as REJECTED by an older backend: no check ran
            why = fv_schema.sanitize_single_line(raw.get("why"), 300)
            env = fv_schema.make_envelope(
                mode="attempt", verdict="NO-VERDICT", trust="none",
                verdict_basis=f"no verdict (no check ran: target lookup failed): {why}",
                total_s=wall, reason=f"theorem {thm!r}: {why}", target={"pset": pset, "theorem": thm},
                diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", why))
            if inferred:
                self.label_inferred(env)
            return self.finish_backend(env, raw, wall, custom_id)
        backend_s = raw.get("total_s") or 0.0
        overhead_ms = round(max(0.0, (wall - backend_s) * 1000.0), 3)
        env = fv_schema.from_fvserve_result(raw, pset=pset, theorem=thm, overhead_ms=overhead_ms, include_raw=False)
        env["timing"]["api_wall_s"] = round(wall, 4)
        if env.get("verdict") not in ("ACCEPTED", "REJECTED"):
            # a full fvserve result without a judged verdict (worker / service error before
            # the check, timeout inside the service, ...) carries no check: trust 'none', like every other non-verdict
            env["trust"] = "none"
        if inferred:   # the target was inferred from the source: EXPERIMENTAL in v0.1, said on every such answer
            self.label_inferred(env)
        return self.finish_backend(env, raw, wall, custom_id)

    def finish_backend(self, env, raw, wall, custom_id):
        """every resolved-request answer - after a backend reply, a pre-dispatch refusal, a
        timeout or a backend error: the caller's custom_id + outcome accounting"""
        env.setdefault("timing", {})["api_wall_s"] = round(wall, 4)
        if custom_id is not None:
            env.setdefault("target", {})["custom_id"] = str(custom_id)
        with self.lock:
            self.verdict_counts[env["verdict"]] += 1
            self.lat_sum += wall
            self.lat_count += 1
        return env, raw

    def to_kimina_item(self, env, custom_id):
        msgs = []
        for d in env.get("diagnostics") or []:
            msgs.append({
                "severity": d.get("severity") or "error",
                "pos": {"line": d.get("line") or 1, "column": d.get("column") or 1},
                "data": d.get("message") or "",
                "rule_id": d.get("rule_id") or "FV001",
            })
        return {
            "custom_id": custom_id,
            "theorem": (env.get("target") or {}).get("theorem"),
            "is_pass": bool(env["accepted"]),
            "verdict": env["verdict"],
            "reward": env["reward"],
            "trust": env["trust"],
            "verdict_basis": env["verdict_basis"],
            "reason": env["reason"],
            "time": env["timing"].get("api_wall_s", env["timing"]["total_s"]),
            "timing": env["timing"],
            "response": {
                "messages": msgs,
                "compiler_output": env.get("compiler_output") or "",
                "sorries": [d for d in msgs if "sorry" in (d.get("data") or "").lower()],
            },
            "envelope": env,
        }


class ApiHandler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "fastverify-api/1.0"

    def log_message(self, fmt, *args):
        if self.server.api.args.verbose:
            sys.stderr.write(f"[fvapi] {self.address_string()} - {fmt % args}\n")

    def setup(self):
        super().setup()
        self._hdr_timer = None
        self.connection.settimeout(self.server.api.socket_timeout)

    def _cancel_hdr_timer(self):
        t = getattr(self, "_hdr_timer", None)
        if t is not None:
            t.cancel()
            self._hdr_timer = None

    def _start_deadline_timer(self, timeout_s, label):
        fired = [False]
        if not timeout_s or timeout_s <= 0:
            return None, fired
        conn = self.connection
        api = self.server.api

        def _cut():
            fired[0] = True
            with api.lock:
                api.req_counts[f"dropped_{label}_timeout"] += 1
            try:
                conn.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass

        t = threading.Timer(timeout_s, _cut)
        t.daemon = True
        t.start()
        return t, fired

    def handle_one_request(self):
        # enforce a TOTAL deadline for request-line + headers (bounds trickle-byte slowloris
        # that would otherwise reset per-recv() socket_timeout and pin --max-connections slots forever).
        self._hdr_timer, _ = self._start_deadline_timer(self.server.api.header_timeout, "header")
        try:
            return super().handle_one_request()
        except OSError:
            self.close_connection = True
        finally:
            self._cancel_hdr_timer()

    def parse_request(self):
        try:
            return super().parse_request()
        finally:
            self._cancel_hdr_timer()

    def send_json(self, status, payload, extra_headers=None):
        body = (json.dumps(payload, separators=(",", ":")) + "\n").encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Cache-Control", "no-store")
        if extra_headers:
            for k, v in extra_headers.items():
                self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def send_text(self, status, text, content_type="text/plain; version=0.0.4; charset=utf-8"):
        body = text.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def check_auth(self):
        key = self.server.api.api_key
        if not key:
            return True
        auth = self.headers.get("Authorization") or ""
        if not auth.startswith("Bearer "):
            return False
        tok = auth[7:].strip()
        return hmac.compare_digest(tok.encode("utf-8"), key.encode("utf-8"))

    def read_json_body(self):
        if (self.headers.get("Transfer-Encoding") or "").lower() == "chunked":
            self.send_json(411, {"error": "chunked transfer encoding not supported; send Content-Length"})
            return None
        cl_hdr = self.headers.get("Content-Length")
        if cl_hdr is None:
            self.send_json(411, {"error": "Content-Length header required"})
            return None
        try:
            cl = int(cl_hdr)
        except ValueError:
            self.send_json(400, {"error": "invalid Content-Length"})
            return None
        if cl < 0:
            self.send_json(400, {"error": "negative Content-Length"})
            return None
        if cl > self.server.api.max_body_bytes:
            self.send_json(413, {"error": f"request body exceeds limit ({self.server.api.max_body_bytes} bytes)"})
            return None
        body_timer, body_fired = self._start_deadline_timer(self.server.api.body_timeout, "body")
        try:
            raw = self.rfile.read(cl)
        except (socket.timeout, OSError):
            self.close_connection = True
            try:
                self.send_json(408, {"error": "request body read timeout"})
            except OSError:
                pass
            return None
        finally:
            if body_timer is not None:
                body_timer.cancel()
        if len(raw) != cl:
            self.close_connection = True
            try:
                self.send_json(408 if body_fired[0] else 400, {"error": "truncated request body"})
            except OSError:
                pass
            return None
        try:
            obj = strict_json_loads(raw)
        except (ValueError, UnicodeDecodeError) as e:
            self.send_json(400, {"error": f"invalid JSON: {fv_schema.sanitize_single_line(e, 160)}"})
            return None
        if not isinstance(obj, dict):
            self.send_json(400, {"error": "JSON body must be an object"})
            return None
        return obj

    def do_GET(self):
        api = self.server.api
        path = self.path.split("?", 1)[0]
        with api.lock:
            api.req_counts[f"GET {path}"] += 1
        if path in ("/health", "/v1/health"):
            try:
                st = api.backend_stats(timeout=3.0)
                code = st.get("code")
                stale = st.get("stale")
                restart_rec = (not isinstance(code, dict)) or bool(stale)
                with api.lock:
                    api._last_backend_stale = len(stale) if isinstance(stale, list) else -1
                self.send_json(200, {
                    "status": "ok",
                    "api_version": fv_schema.API_VERSION,
                    "uptime_s": round(time.time() - api.t0, 2),
                    "inflight": api.inflight,
                    "max_concurrent": api.max_concurrent,
                    "active_connections": api.active_connections,
                    "max_connections": api.max_connections,
                    "default_pset": api.default_pset,
                    "backend": {
                        "reachable": True,
                        "psets": st.get("psets", []),
                        "pending": st.get("pending", 0),
                        "inflight_batches": st.get("inflight", 0),
                        "items_total": st.get("items", 0),
                        "code": code,
                        "stale": stale,
                        "restart_recommended": restart_rec,
                    },
                })
            except Exception as e:  # noqa: BLE001
                self.send_json(503, {
                    "status": "degraded",
                    "api_version": fv_schema.API_VERSION,
                    "backend": {"reachable": False, "error": fv_schema.sanitize_single_line(e, 160)},
                })
            return
        if path == "/metrics":
            if not self.check_auth():
                self.send_json(401, {"error": "unauthorized"})
                return
            with api.lock:
                lines = [
                    "# HELP fvapi_uptime_seconds API server uptime in seconds",
                    "# TYPE fvapi_uptime_seconds gauge",
                    f"fvapi_uptime_seconds {round(time.time() - api.t0, 3)}",
                    "# HELP fvapi_inflight Current active verification requests",
                    "# TYPE fvapi_inflight gauge",
                    f"fvapi_inflight {api.inflight}",
                    "# HELP fvapi_active_connections Current open HTTP connections (capped by --max-connections)",
                    "# TYPE fvapi_active_connections gauge",
                    f"fvapi_active_connections {api.active_connections}",
                    "# HELP fvapi_connections_rejected_total Connections dropped by max_connections cap",
                    "# TYPE fvapi_connections_rejected_total counter",
                    f"fvapi_connections_rejected_total {api.req_counts.get('rejected_conn_cap', 0)}",
                    "# HELP fvapi_backend_stale_files Stale code files reported by fvserve (stageVer; -1 if unknown/pre-76f19410)",
                    "# TYPE fvapi_backend_stale_files gauge",
                    f"fvapi_backend_stale_files {getattr(api, '_last_backend_stale', -1)}",
                    "# HELP fvapi_verdicts_total Verification verdicts by outcome",
                    "# TYPE fvapi_verdicts_total counter",
                ]
                for v, c in sorted(api.verdict_counts.items()):
                    lines.append(f'fvapi_verdicts_total{{verdict="{v}"}} {c}')
                lines.extend([
                    "# HELP fvapi_verify_duration_seconds_sum Sum of verification wall seconds",
                    "# TYPE fvapi_verify_duration_seconds_sum counter",
                    f"fvapi_verify_duration_seconds_sum {round(api.lat_sum, 4)}",
                    "# HELP fvapi_verify_duration_seconds_count Count of completed verifications",
                    "# TYPE fvapi_verify_duration_seconds_count counter",
                    f"fvapi_verify_duration_seconds_count {api.lat_count}",
                ])
            self.send_text(200, "\n".join(lines) + "\n")
            return
        self.send_json(404, {"error": "not found"})

    def do_POST(self):
        api = self.server.api
        path = self.path.split("?", 1)[0]
        with api.lock:
            api.req_counts[f"POST {path}"] += 1
        if path not in ("/verify", "/api/check", "/v1/verify", "/v1/verify/batch"):
            self.send_json(404, {"error": "not found"})
            return
        if not self.check_auth():
            self.send_json(401, {"error": "unauthorized"})
            return
        if not api.sem.acquire(blocking=False):
            with api.lock:
                api.req_counts["rejected_429"] += 1
            self.send_json(429, {"error": "too many concurrent requests"}, extra_headers={"Retry-After": "1"})
            return
        with api.lock:
            api.inflight += 1
        try:
            body = self.read_json_body()
            if body is None:
                return
            t_req = time.time()
            # Mode A: Kimina-compatible batch payload {"codes": [...]} or {"items": [...]}
            if "codes" in body or "items" in body or path == "/v1/verify/batch":
                items = body.get("codes") if "codes" in body else body.get("items")
                if not isinstance(items, list) or not items:
                    self.send_json(400, {"error": "'codes' or 'items' must be a non-empty list"})
                    return
                if len(items) > api.max_batch:
                    self.send_json(400, {"error": f"batch size {len(items)} exceeds limit ({api.max_batch})"})
                    return
                top_pset = body.get("pset") or api.default_pset
                top_tmo = body.get("timeout")
                if top_tmo is not None and (not isinstance(top_tmo, (int, float)) or isinstance(top_tmo, bool) or top_tmo <= 0):
                    self.send_json(400, {"error": "timeout must be a positive number"})
                    return
                jobs = []
                for i, it in enumerate(items):
                    if not isinstance(it, dict):
                        self.send_json(400, {"error": f"items[{i}] must be an object"})
                        return
                    cid = it.get("custom_id", f"item_{i}")
                    cid_given = "custom_id" in it   # a generated item_<i> is a display id, never a target name
                    pset = it.get("pset") or top_pset
                    src = it.get("source") if "source" in it else it.get("proof")
                    if src is None and "code" in it:
                        src = it.get("code")
                    thm = it.get("theorem")
                    it_tmo = it.get("timeout", top_tmo)
                    jobs.append((cid, pset, thm, src, it_tmo, cid if cid_given else None))
                futs = [api.backend_pool.submit(api.verify_one, pset, thm, src, it_tmo, given)
                        for cid, pset, thm, src, it_tmo, given in jobs]
                outs = [f.result() for f in futs]
                kimina_results = [api.to_kimina_item(env, cid) for (env, _), (cid, *_rest) in zip(outs, jobs)]
                wall = round(time.time() - t_req, 4)
                n_acc = sum(1 for r in kimina_results if r["is_pass"])
                api.record_audit({"path": path, "batch": len(jobs), "accepted": n_acc, "wall_s": wall})
                self.send_json(200, {
                    "api_version": fv_schema.API_VERSION,
                    # derived from the items: no item judged -> 'none' (never 'sound' for all-refusals)
                    # and only a JUDGED item (ACCEPTED / REJECTED with trust 'sound') makes the batch 'sound'
                    "trust": "sound" if any(r.get("trust") == "sound" and r.get("verdict") in ("ACCEPTED", "REJECTED")
                                            for r in kimina_results) else "none",
                    "count": len(kimina_results),
                    "accepted_count": n_acc,
                    "wall_s": wall,
                    "results": kimina_results,
                })
                return

            # Mode B: Single verification payload {"pset": ..., "theorem": ..., "source"|"proof"|"code": ...}
            pset = body.get("pset") or api.default_pset
            src = body.get("source") if "source" in body else (body.get("proof") if "proof" in body else body.get("code"))
            thm = body.get("theorem")
            tmo = body.get("timeout")
            if tmo is not None and (not isinstance(tmo, (int, float)) or isinstance(tmo, bool) or tmo <= 0):
                self.send_json(400, {"error": "timeout must be a positive number"})
                return
            cid = body.get("custom_id")
            env, _ = api.verify_one(pset, thm, src, timeout=tmo, custom_id=cid)
            api.record_audit({"path": path, "pset": pset, "theorem": env["target"].get("theorem"),
                              "verdict": env["verdict"], "wall_s": env["timing"].get("api_wall_s")})
            if path in ("/verify", "/api/check") and body.get("format") == "kimina":
                self.send_json(200, {"results": [api.to_kimina_item(env, cid or "0")]})
            else:
                self.send_json(200, env)
        finally:
            with api.lock:
                api.inflight -= 1
            api.sem.release()


class ThreadedHTTPServer(http.server.ThreadingHTTPServer):
    allow_reuse_address = True
    daemon_threads = True
    request_queue_size = 128

    def process_request(self, request, client_address):
        # cap active TCP connections BEFORE spawning a handler thread so
        # unauthenticated slow / half-open sockets cannot exhaust threads or FDs.
        api = self.api
        if not api.conn_sem.acquire(blocking=False):
            with api.lock:
                api.req_counts["rejected_conn_cap"] += 1
            try:
                request.settimeout(0.2)
                request.sendall(
                    b"HTTP/1.1 503 Service Unavailable\r\n"
                    b"Content-Type: application/json\r\n"
                    b"Content-Length: 44\r\n"
                    b"Connection: close\r\n"
                    b"Retry-After: 1\r\n\r\n"
                    b'{"error":"too many concurrent connections"}\n'
                )
            except OSError:
                pass
            finally:
                self.shutdown_request(request)
            return
        with api.lock:
            api.active_connections += 1
        try:
            super().process_request(request, client_address)
        except Exception:
            with api.lock:
                api.active_connections -= 1
            api.conn_sem.release()
            raise

    def process_request_thread(self, request, client_address):
        api = self.api
        try:
            super().process_request_thread(request, client_address)
        finally:
            with api.lock:
                api.active_connections -= 1
            api.conn_sem.release()


def main():
    ap = argparse.ArgumentParser(description="Hardened Kimina-compatible HTTP REST API fronting tools/fvserve")
    ap.add_argument("--fvserve-state", required=True, help="fvserve --state directory containing sock")
    ap.add_argument("--default-pset", default=None, help="default problem set name when omitted in requests")
    ap.add_argument("--host", default="127.0.0.1", help="bind address (default: 127.0.0.1)")
    ap.add_argument("--port", type=int, default=8080, help="bind port (default: 8080; 0 = ephemeral)")
    ap.add_argument("--api-key-file", default=None, help="optional file containing Bearer token for auth")
    ap.add_argument("--max-concurrent", type=int, default=32, help="max concurrent HTTP requests (default: 32)")
    ap.add_argument("--max-connections", type=int, default=0,
                    help="max active TCP connection threads before immediate 503 close (default: max(2*max-concurrent, 64))")
    ap.add_argument("--max-backend-concurrent", type=int, default=32, help="max concurrent calls to fvserve (default: 32)")
    ap.add_argument("--custom-id-is-theorem", action="store_true",
                    help="when 'theorem' is omitted in Kimina requests, treat custom_id as the target theorem name")
    ap.add_argument("--experimental-theorem-inference", dest="allow_theorem_inference", action="store_true",
                    help="EXPERIMENTAL, off by default (v0.1): infer the target theorem from the source when 'theorem' is "
                         "omitted, with a Lean-tokenizer mirror that refuses (NO-VERDICT) whatever it cannot read exactly. "
                         "Convenience only, NOT reward-safe against adversarial multi-theorem submissions: pass an explicit "
                         "'theorem' (or use --custom-id-is-theorem). Every inferred-target answer carries "
                         "\"theorem_inference\": \"experimental\"")
    ap.add_argument("--allow-theorem-inference", dest="old_inference_flag", action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--max-body-bytes", type=int, default=4 << 20, help="max HTTP body bytes (default: 4 MiB)")
    ap.add_argument("--max-source-bytes", type=int, default=1 << 20, help="max Lean source bytes per attempt (default: 1 MiB)")
    ap.add_argument("--max-batch", type=int, default=128, help="max attempts per batch request (default: 128)")
    ap.add_argument("--request-timeout", type=float, default=300.0, help="per-attempt backend timeout seconds")
    ap.add_argument("--socket-timeout", type=float, default=15.0, help="HTTP per-recv socket read timeout seconds")
    ap.add_argument("--header-timeout", type=float, default=10.0,
                    help="total deadline seconds for request line + headers (slowloris defense; default: 10)")
    ap.add_argument("--body-timeout", type=float, default=15.0,
                    help="total deadline seconds to finish reading request body (default: 15)")
    ap.add_argument("--audit-log", default=None, help="optional JSONL audit log path")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    if args.old_inference_flag:   # the old name is refused: inference is EXPERIMENTAL in v0.1 and must be asked for by that name
        ap.error("--allow-theorem-inference was renamed: theorem inference is EXPERIMENTAL in v0.1 (not reward-safe against "
                 "adversarial multi-theorem submissions) - use --experimental-theorem-inference, or better an explicit "
                 "'theorem' / --custom-id-is-theorem")

    api = ApiState(args)
    srv = ThreadedHTTPServer((args.host, args.port), ApiHandler)
    srv.api = api
    actual_host, actual_port = srv.server_address[:2]

    def _shutdown(*_a):
        threading.Thread(target=srv.shutdown, daemon=True).start()

    signal.signal(signal.SIGTERM, _shutdown)
    signal.signal(signal.SIGINT, _shutdown)
    print(json.dumps({
        "event": "ready",
        "host": actual_host,
        "port": actual_port,
        "url": f"http://{actual_host}:{actual_port}",
        "fvserve_state": api.fvserve_state,
        "default_pset": api.default_pset,
        "auth": bool(api.api_key),
        "theorem_inference": "experimental" if api.allow_theorem_inference else "off",
    }), flush=True)
    if args.allow_theorem_inference:   # after the `ready` line (clients read that line first)
        print("fvapi: WARNING: --experimental-theorem-inference is on: inferred targets are EXPERIMENTAL (a source-level "
              "Lean-tokenizer mirror, not Lean's own list of declared theorems); pass an explicit 'theorem' for "
              "reward-critical use", file=sys.stderr, flush=True)
    try:
        srv.serve_forever(poll_interval=0.2)
    finally:
        srv.server_close()
        if api.audit_log:
            api.audit_log.close()


if __name__ == "__main__":
    main()

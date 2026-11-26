"""leanlex.py -- a mirror of the Lean 4 tokenizer for reading CLIENT Lean sources on the host without guessing.

VERBATIM COPY of the lexer section of tools/http/fvapi.py (from the section marker comment to
`def strict_json_loads`), so that tools/triage/triage.py reads sources exactly as fvapi's theorem inference does and fails
closed the same way (LeanSourceUnclear). When the package's own tools/http/fvapi.py carries the
lexer section, THAT section is loaded at import and replaces the bundled copy (LEXER_ORIGIN says which one is active), so triage
and fvapi read sources identically whatever fvapi.py revision is installed. Pure stdlib, no side effects on import beyond that.
"""
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

# ---- end of the lexer copy --------------------------------------------------------------------------------------------


def _load_installed_lexer():
    """the lexer section of this package's tools/http/fvapi.py (package code, as trusted as this
    file), compiled into a fresh namespace; None if fvapi.py is absent, has no lexer section, or it lacks a name triage uses"""
    import os as _os
    fvapi = _os.path.join(_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))), "http", "fvapi.py")
    try:
        with open(fvapi, encoding="utf-8") as _f:
            txt = _f.read()
        a0, a1 = txt.index("# Lean source lexer:"), txt.index("def strict_json_loads")
        ns = {"__name__": __name__}
        exec(compile(txt[a0:a1], fvapi + " (lexer section)", "exec"), ns)  # noqa: S102
    except Exception:  # noqa: BLE001
        return None
    need = ("_LeanLexer", "LeanSourceUnclear", "_LEAN_KEYWORDS", "_LEAN_DECL_MODIFIERS", "lean_declared_theorems")
    return (ns, fvapi) if all(n in ns for n in need) else None


LEXER_ORIGIN = "bundled copy"
_inst = _load_installed_lexer()
if _inst is not None:
    globals().update({k: v for k, v in _inst[0].items() if not k.startswith("__")})
    LEXER_ORIGIN = _inst[1]
del _inst

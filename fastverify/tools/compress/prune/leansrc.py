"""leansrc.py - split a Lean 4 source file into top-level commands.

Heuristic but conservative: a command starts at a column-0 line whose first word is a command keyword (or a modifier /
attribute that precedes one); every other line (indented lines, `|` match arms, `where`, `deriving`, `termination_by`,
...) continues the previous command. Block comments are tracked (nesting). A command that ends in the token `in`
(`set_option ... in`, `open ... in`, `omit ... in`, `attribute [...] ... in`) and a command that consists only of
attributes / modifiers are merged with the following command, so a deletion never leaves a dangling prefix.
Contiguous `--` comment lines directly above a command (no blank line in between) belong to that command.
"""
import re

START_WORDS = {
    'theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class', 'inductive', 'coinductive', 'example', 'axiom',
    'opaque', 'noncomputable', 'private', 'protected', 'namespace', 'section', 'end', 'open', 'variable', 'universe',
    'set_option', 'attribute', 'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'macro', 'macro_rules',
    'syntax', 'elab', 'elab_rules', 'declare_syntax_cat', 'initialize', 'builtin_initialize', 'run_cmd', 'run_elab',
    'run_meta', 'import', 'mutual', 'export', 'local', 'scoped', 'unsafe', 'partial', 'nonrec', 'omit', 'include', 'alias',
    'unseal', 'seal', 'irreducible_def', 'add_decl_doc', 'library_note', 'assert_not_exists', 'suppress_compilation',
    'cpt_copy_thms', 'module', 'public', 'meta', 'prelude', 'register_simp_attr', 'compile_inductive', 'recall',
}
MODIFIERS = {'private', 'protected', 'noncomputable', 'partial', 'unsafe', 'nonrec', 'scoped', 'local', 'public', 'meta'}
DECL_WORDS = {'theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class', 'inductive', 'coinductive',
              'example', 'axiom', 'opaque', 'irreducible_def'}
# identifier components, exactly Lean 4's isIdRest (Lean/Syntax / Init/Meta): ASCII alnum, _ ' ! ?, isLetterLike
# (Greek except λ Π Σ, Coptic, polytonic Greek, letter-like symbols U+2100-214F, math alphanumerics U+1D49C-1D59F) and
# isSubScriptAlnum (₀-₉ ₐ-ₜ ᵢ-ᵪ ⱼ). Superscripts such as ⁻¹ are NOT identifier characters (postfix notation).
_LL = ("A-Za-z0-9_'!?"
       "\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1\u03a2\u03a4-\u03a9\u03ca-\u03fb\u1f00-\u1ffe"
       "\u2100-\u214f\U0001d49c-\U0001d59f\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c")
TOKEN_RE = re.compile("[" + _LL + "]+")
_word_re = re.compile(r"[A-Za-z_#][A-Za-z_0-9]*")


class Cmd:
    __slots__ = ('start', 'end', 'kind', 'name', 'attrs', 'mods', 'text_start')

    def __init__(self, start, end):
        self.start = start          # first line index (0-based, inclusive), incl. leading comments
        self.end = end              # last line index + 1 (exclusive), excl. trailing blank lines
        self.text_start = start     # first non-comment line
        self.kind = None; self.name = None; self.attrs = []; self.mods = []

    def __repr__(self):
        return f'Cmd({self.start}-{self.end} {self.kind} {self.name} attrs={self.attrs} mods={self.mods})'


def _first_word(line):
    if line.startswith('@['):
        return '@['
    if line.startswith('#'):
        return '#'
    if line.startswith('/-') or line.startswith('--'):
        return line[:2]
    m = _word_re.match(line)
    return m.group(0) if m else None


def _strip_comments_line(line, depth):
    """Return (code part of line, new block-comment depth). Line comments `--` removed; strings are not special-cased
    beyond a simple skip (RH sources have almost no string literals)."""
    out = []; i = 0; n = len(line)
    while i < n:
        if depth > 0:
            if line.startswith('/-', i):
                depth += 1; i += 2
            elif line.startswith('-/', i):
                depth -= 1; i += 2
            else:
                i += 1
            continue
        c = line[i]
        if c == '"':
            j = i + 1
            while j < n and line[j] != '"':
                j += 2 if line[j] == '\\' else 1
            out.append(line[i:j + 1]); i = j + 1; continue
        if line.startswith('--', i):
            break
        if line.startswith('/-', i):
            depth += 1; i += 2; continue
        out.append(c); i += 1
    return ''.join(out), depth


def split_commands(lines):
    """lines: list of str (no newlines). Returns (cmds, code) where code[i] is line i without comments."""
    code = []; depth = 0; starts_in_comment = []
    for l in lines:
        starts_in_comment.append(depth > 0)
        c, depth = _strip_comments_line(l, depth)
        code.append(c)
    n = len(lines)
    starts = []
    for i, l in enumerate(lines):
        if starts_in_comment[i] or not l or l[0].isspace():
            continue
        w = _first_word(l)
        if l.startswith('/--'):          # doc comment: belongs to (starts) the following declaration
            starts.append(i); continue
        if w in ('--', '/-'):
            continue
        if w in START_WORDS or w in ('@[', '#'):
            if w == 'deriving' and not l.startswith('deriving instance'):
                continue
            starts.append(i)
        elif l.startswith('deriving instance'):
            starts.append(i)
    cmds = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else n
        cmds.append([s, e])
    # header before first command (comments/blank) is not a command; merge rules
    merged = []
    i = 0
    while i < len(cmds):
        s, e = cmds[i]
        while i + 1 < len(cmds):
            text = ' '.join(code[j] for j in range(s, e)).strip()
            if not text:
                if lines[s].startswith('/--'):     # a doc comment alone: merge with the declaration it documents
                    i += 1; e = cmds[i][1]; continue
                break
            attrs, mods, rest = strip_prefix(text)
            if not rest.strip() or text.split()[-1] == 'in':
                i += 1; e = cmds[i][1]
            else:
                break
        merged.append([s, e]); i += 1
    out = []
    for s, e in merged:
        # trailing blank / comment-only lines go to the next command's leading-comment search; trim blanks
        ee = e
        while ee > s + 1 and (not lines[ee - 1].strip() or (lines[ee - 1].startswith('--') and not code[ee - 1].strip())):
            ee -= 1
        c = Cmd(s, ee)
        # attach directly preceding `--` comment lines (contiguous, column 0) to this command
        ss = s
        while ss > 0 and lines[ss - 1].startswith('--') and (not out or ss - 1 >= out[-1].end):
            ss -= 1
        c.start = ss; c.text_start = s
        _classify(c, code)
        out.append(c)
    return out, code


def strip_prefix(text):
    """Split leading attribute groups `@[...]` (balanced brackets), modifiers and `set_option/open/omit/include/
    attribute ... in` prefixes off a command text. Returns (attrs, mods, rest)."""
    attrs = []; mods = []; t = text.lstrip()
    while t:
        if t.startswith('@['):
            d = 0; j = 0
            for j, ch in enumerate(t):
                if ch == '[': d += 1
                elif ch == ']':
                    d -= 1
                    if d == 0: break
            attrs.append(t[:j + 1]); t = t[j + 1:].lstrip(); continue
        w = t.split(None, 1)
        if w[0] in MODIFIERS:
            mods.append(w[0]); t = w[1] if len(w) > 1 else ''; continue
        if w[0] in ('set_option', 'open', 'omit', 'include', 'attribute', 'variable', 'universe'):   # D17: + universe .. in
            m = re.search(r'\sin(\s|$)', t)
            if m:
                mods.append(t[:m.start()] + ' in'); t = t[m.end():].lstrip(); continue
        break
    return attrs, mods, t


def _classify(c, code):
    text = ' '.join(code[j] for j in range(c.text_start, min(c.end, c.text_start + 30)))
    attrs, mods, rest = strip_prefix(text)
    c.attrs = attrs; c.mods = mods
    toks = rest.split()
    if toks:
        c.kind = toks[0]
        if c.kind in DECL_WORDS and len(toks) > 1:
            m = re.match(r"[^\s(\[{:⦃]+", toks[1])
            c.name = m.group(0) if m else None
    return c


def tokens(text):
    return TOKEN_RE.findall(text)


def namespaces(cmds, code):
    """current namespace (dotted string) at the start of every command"""
    stack = []   # entries: ('ns', [components]) or ('sec', name)
    out = []
    for c in cmds:
        out.append('.'.join(x for kind, comps in stack if kind == 'ns' for x in comps))
        toks = code[c.text_start].split()
        if c.kind == 'namespace' and len(toks) > 1:
            stack.append(('ns', toks[1].split('.')))
        elif c.kind == 'section' and not c.mods or (c.kind == 'section'):
            stack.append(('sec', toks[-1] if len(toks) > 1 and toks[-1] != 'section' else ''))
        elif c.kind == 'end':
            if stack: stack.pop()
    return out

#!/usr/bin/env python3
"""edits_v2.py - name-anchored edit lists (format v2 of NEXT_PLAN 4.3 P2) resolved to the team's line-anchored v1 TSV.

UNTRUSTED producer-side tool (like every tool under tools/compress): whatever it emits is only a proposal; a candidate
counts only with the unchanged judge's ACCEPTED and `expdiff` (NEXT_PLAN 4.0). Its job is to let text work (docstrings,
module docs, statement layout, renames) be written ONCE against declaration names and survive line shifts - a rebase
onto a newer main, other owners' edits, a move from base A to base B - and to REFUSE (never guess) when the declaration
it was written for is no longer the same text.

  edits_v2.py index   PROJECT [--srcdir src] [--modules FILE]            > INDEX.tsv
      module  decl  start  end  sha256  dstart  dsha256
          start..end = 1-based inclusive lines of the declaration's command span (merged `set_option ... in` prefixes,
          docstring, attributes, modifiers, the declaration); sha256 = of exactly those lines, LF-joined; dstart/dsha256 =
          the same for the declaration PROPER (from its docstring / attributes / keyword line; = D18's docs_v2.py hash).
          A v2 line may carry either hash; `replace` then covers exactly the span its hash names, `delete` always the
          whole command (never a dangling `set_option ... in`), and a docstring always goes at dstart.
  edits_v2.py resolve PROJECT V2.tsv [V2.tsv ...] --out V1.tsv [--refused R.tsv] [--srcdir src] [--relocate]

V2 line (tab-separated; payload '\\n'-escaped exactly like v1):
  module  decl  decl_sha256  action  owner  payload
  action  doc          payload = docstring body (or a full `/-- ... -/`): replaces the declaration's docstring, or
                       inserts one before it; a body containing `-/` is refused
          replace      payload = the new text of the span its hash names (statement layout, STMTFMT); a payload that
                       adds a docstring to a declaration without one is refused (docstrings are `doc` lines, so a doc
                       insert and a statement replace of one declaration compose without a double docstring)
          delete       payload ignored; deletes the command span and the `--` comment lines directly above it
          insert_after payload = text inserted after the command span
          rename       payload = 'OLD NEW'; OLD must be the declaration's own name (as written or fully qualified);
                       emitted as a v1 `subst` for THIS module only (other modules: their own v2 lines; cross-module
                       checks stay with rename_scan.py / compose_check.py)
          moddoc       decl = '-', decl_sha256 = sha256 of the existing `/-! -/` module doc or '-' if none;
                       payload = module doc body: replaces that block or inserts one after the header (module/imports)
A line resolves only when the module exists, the declaration name is found exactly once in it, and the sha256 of its
current command span equals decl_sha256. With --relocate a declaration that is not in the named module is searched in
every module of the tree and used only if exactly one declaration with that full name AND that sha256 exists.
Refusals (R.tsv: the v2 line + reason): MODULE_MISSING, DECL_MISSING, DECL_AMBIGUOUS, HASH_MISMATCH, BAD_ACTION,
BAD_PAYLOAD, RENAME_MISMATCH, DUPLICATE_ANCHOR (two lines of one owner on one declaration and action).
Declaration spans come from tools/compress/prune/leansrc.py (the splitter the pruning rounds use at RH scale), with
`mutual ... end` handled for namespace tracking. Anonymous instances have no name and cannot be anchored.
"""
import sys, os, re, json, hashlib, argparse, collections

HERE = os.path.dirname(os.path.abspath(__file__))
for cand in (os.environ.get('FV_LEANSRC_DIR', ''),
             os.path.join(HERE, '..', '..', '..', '..', '..', 'fastverify', 'tools', 'compress', 'prune'),
             os.path.join(HERE, '..', 'prune')):
    if cand and os.path.isfile(os.path.join(cand, 'leansrc.py')):
        sys.path.insert(0, os.path.abspath(cand)); break
import leansrc  # noqa: E402

ACTIONS = {'doc', 'replace', 'delete', 'insert_after', 'rename', 'moddoc'}
ALIASES = {'docstring': 'doc'}
PREFIX_WORDS = {'set_option', 'open', 'omit', 'include', 'attribute', 'variable', 'universe'}   # D18's stage3/docs_v2.py writes `docstring`


def unesc(s):
    out = []; i = 0
    while i < len(s):
        if s[i] == '\\' and i + 1 < len(s):
            out.append('\n' if s[i + 1] == 'n' else s[i + 1]); i += 2
        else:
            out.append(s[i]); i += 1
    return ''.join(out)


def esc(s):
    return s.replace('\\', '\\\\').replace('\n', '\\n')


def sha(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def modpath(root, srcdir, mod):
    return os.path.join(root, srcdir, mod.replace('.', '/') + '.lean')


def namespaces(cmds, code):
    """namespace at the start of every command; like leansrc.namespaces but `mutual` opens a scope its `end` closes."""
    stack = []; out = []
    for c in cmds:
        out.append('.'.join(x for kind, comps in stack if kind == 'ns' for x in comps))
        toks = code[c.text_start].split()
        if c.kind == 'namespace' and len(toks) > 1:
            stack.append(('ns', toks[1].split('.')))
        elif c.kind == 'section':
            stack.append(('sec', []))
        elif c.kind == 'mutual':
            stack.append(('mut', []))
        elif c.kind == 'end':
            if stack:
                stack.pop()
    return out


class Module:
    def __init__(self, path):
        self.text = open(path, encoding='utf-8').read()
        self.lines = self.text.split('\n')
        self.cmds, self.code = leansrc.split_commands(self.lines)
        ns = namespaces(self.cmds, self.code)
        self.decls = collections.defaultdict(list)     # name (full and as written) -> [cmd]
        for c, n in zip(self.cmds, ns):
            if c.kind in leansrc.DECL_WORDS and c.name and c.kind != 'example':
                written = c.name
                full = written[len('_root_.'):] if written.startswith('_root_.') else (n + '.' + written if n else written)
                self.decls[full].append(c)
                if written != full:
                    self.decls.setdefault('\0w:' + written, []).append(c)

    def span_text(self, c):
        return '\n'.join(self.lines[c.text_start:c.end])

    def dstart(self, c):
        """first line of the declaration proper (its docstring, attributes or keyword): the command span minus the
        `set_option ... in` / `open ... in` (etc.) prefix lines and blank lines that leansrc merges into the command.
        A docstring must be inserted HERE - `/-- d -/ set_option x y in theorem ...` does not parse."""
        i = c.text_start
        while i < c.end - 1:
            code = self.code[i].strip()
            if self.lines[i].lstrip().startswith('/--'):
                break
            if not code or (code.split()[0] in PREFIX_WORDS and code.split()[-1] == 'in'):
                i += 1; continue
            break
        return i

    def proper_text(self, c):
        return '\n'.join(self.lines[self.dstart(c):c.end])

    def anchor(self, c, h):
        """0-based start line of the span whose sha256 is h: the command span, else the declaration proper; None."""
        if sha(self.span_text(c)) == h:
            return c.text_start
        d = self.dstart(c)
        if d != c.text_start and sha('\n'.join(self.lines[d:c.end])) == h:
            return d
        return None

    def full_names(self):
        return [k for k in self.decls if not k.startswith('\0w:')]

    def lookup(self, name):
        hits = self.decls.get(name)
        if hits is None:
            hits = self.decls.get('\0w:' + name, [])
        return hits

    def moddoc(self):
        """(start, end) 0-based [start, end) of the first column-0 `/-!` block before the first declaration, or None;
        plus the insertion line after the header (module / imports / blank / comments)."""
        first_decl = min((c.text_start for c in self.cmds if c.kind not in ('import', 'module', 'prelude', 'public')),
                         default=len(self.lines))
        i = 0
        while i < first_decl:
            if self.lines[i].startswith('/-!'):
                j = i
                while j < len(self.lines) and '-/' not in self.lines[j][(3 if j == i else 0):]:
                    j += 1
                return (i, min(j + 1, len(self.lines))), None    # clamp: an unclosed comment
            i += 1
        ins = 0
        for c in self.cmds:
            toks = self.code[c.text_start].split()
            if c.kind in ('import', 'module', 'prelude') or (toks[:1] == ['public'] and toks[1:2] == ['import']):
                ins = c.end
            else:
                break
        return None, ins

    def docspan(self, c):
        """0-based [start, end) of the docstring that opens the command span, or None."""
        i = self.dstart(c)
        if not self.lines[i].lstrip().startswith('/--'):
            return None
        j = i
        while j < c.end and '-/' not in self.lines[j][(self.lines[j].index('/--') + 3 if j == i else 0):]:
            j += 1
        return (i, min(j + 1, c.end))    # clamp: an unclosed docstring never reaches past the command


def iter_modules(root, srcdir):
    base = os.path.join(root, srcdir)
    for dp, dn, fn in os.walk(base):
        dn[:] = sorted(d for d in dn if not d.startswith('.'))
        for f in sorted(fn):
            if f.endswith('.lean'):
                rel = os.path.relpath(os.path.join(dp, f), base)[:-5]
                yield rel.replace(os.sep, '.')


def cmd_index(a):
    mods = [l.strip() for l in open(a.modules)] if a.modules else iter_modules(a.project, a.srcdir)
    w = sys.stdout
    for m in mods:
        if not m:
            continue
        p = modpath(a.project, a.srcdir, m)
        if not os.path.isfile(p):
            continue
        M = Module(p)
        for full in sorted(M.full_names()):
            for c in M.decls[full]:
                d = M.dstart(c)
                w.write(f'{m}\t{full}\t{c.text_start + 1}\t{c.end}\t{sha(M.span_text(c))}\t{d + 1}\t{sha(M.proper_text(c))}\n')


def docblock(payload, indent=''):
    body = payload.strip('\n')
    if body.lstrip().startswith('/--'):
        return body
    if '\n' in body:
        return f'{indent}/-- {body}\n{indent}-/'
    return f'{indent}/-- {body} -/'


def cmd_resolve(a):
    cache = {}
    def mod(m):
        if m not in cache:
            p = modpath(a.project, a.srcdir, m)
            cache[m] = Module(p) if os.path.isfile(p) else None
        return cache[m]
    gidx = None
    def global_index():
        nonlocal gidx
        if gidx is None:
            gidx = collections.defaultdict(list)
            for m in iter_modules(a.project, a.srcdir):
                M = mod(m)
                for full in M.full_names():
                    for c in M.decls[full]:
                        gidx[full].append((m, c))
        return gidx

    out = open(a.out, 'w', encoding='utf-8')
    ref = open(a.refused, 'w', encoding='utf-8') if a.refused else None
    S = collections.Counter(); seen = set()
    def refuse(raw, why):
        S['refused_' + why] += 1
        if ref:
            ref.write(raw.rstrip('\n') + '\t' + why + '\n')
    for f in a.v2:
        for raw in open(f, encoding='utf-8'):
            if not raw.strip() or raw.startswith('#'):
                continue
            p = raw.rstrip('\n').split('\t', 5)
            if len(p) < 5:
                refuse(raw, 'BAD_ACTION'); continue
            m, decl, dsha, act, owner = p[:5]
            payload = unesc(p[5]) if len(p) > 5 else ''
            act = ALIASES.get(act, act)
            if act not in ACTIONS:
                refuse(raw, 'BAD_ACTION'); continue
            key = (owner, m, decl, act)
            if key in seen:
                refuse(raw, 'DUPLICATE_ANCHOR'); continue
            seen.add(key)
            M = mod(m)
            if act == 'moddoc':
                if M is None:
                    refuse(raw, 'MODULE_MISSING'); continue
                blk, ins = M.moddoc()
                cur = '-' if blk is None else sha('\n'.join(M.lines[blk[0]:blk[1]]))
                if cur != dsha:
                    refuse(raw, 'HASH_MISMATCH'); continue
                body = payload.strip('\n')
                bs = body.strip()
                inner = bs[3:-2] if bs.startswith('/-!') and bs.endswith('-/') else body
                if '-/' in inner or '/-' in inner:
                    refuse(raw, 'BAD_PAYLOAD'); continue
                text = body if body.startswith('/-!') else f'/-!\n{body}\n-/'
                if blk is None:
                    out.write(f'{m}\t{ins + 1}\t{ins}\tinsert_before\t{owner}\t{esc(text + chr(10))}\n')
                else:
                    out.write(f'{m}\t{blk[0] + 1}\t{blk[1]}\treplace\t{owner}\t{esc(text)}\n')
                S['resolved_moddoc'] += 1; continue
            hits = M.lookup(decl) if M is not None else []
            where = m
            if not hits and a.relocate:
                cands = [(mm, c) for (mm, c) in global_index().get(decl, []) if mod(mm).anchor(c, dsha) is not None]
                if len(cands) == 1:
                    where, c0 = cands[0]; M = mod(where); hits = [c0]; S['relocated'] += 1
            if M is None:
                refuse(raw, 'MODULE_MISSING'); continue
            if not hits:
                refuse(raw, 'DECL_MISSING'); continue
            if len(hits) > 1:
                refuse(raw, 'DECL_AMBIGUOUS'); continue
            c = hits[0]
            a0 = M.anchor(c, dsha)
            if a0 is None:
                refuse(raw, 'HASH_MISMATCH'); continue
            s1, e1 = a0 + 1, c.end          # 1-based inclusive: the span the hash was computed on
            if act == 'replace':
                if '/--' in payload and M.docspan(c) is None:
                    refuse(raw, 'BAD_PAYLOAD'); continue    # docstrings belong to `doc` lines (else: two docstrings)
                out.write(f'{where}\t{s1}\t{e1}\treplace\t{owner}\t{esc(payload.rstrip(chr(10)))}\n')
            elif act == 'delete':
                out.write(f'{where}\t{c.start + 1}\t{e1}\tdelete\t{owner}\t\n')
            elif act == 'insert_after':
                out.write(f'{where}\t{e1 + 1}\t{e1}\tinsert_before\t{owner}\t{esc(payload.rstrip(chr(10)))}\n')
            elif act == 'doc':
                body = payload.strip('\n')
                bs = body.strip()    # an indented full `/-- ... -/` payload is valid
                inner = bs[3:-2] if bs.startswith('/--') and bs.endswith('-/') else body
                if '-/' in inner or '/-' in inner:
                    refuse(raw, 'BAD_PAYLOAD'); continue
                ds = M.dstart(c)
                ind = re.match(r'\s*', M.lines[ds]).group(0)
                d = M.docspan(c)
                if d is None:
                    # insert_before (as D18's v1 lists do), so a docstring composes with another owner's `replace` of
                    # the same statement (STMTFMT); the two-docstring hazard is closed on the replace side below
                    out.write(f'{where}\t{ds + 1}\t{ds}\tinsert_before\t{owner}\t{esc(docblock(body, ind))}\n')
                else:
                    out.write(f'{where}\t{d[0] + 1}\t{d[1]}\treplace\t{owner}\t{esc(docblock(body, ind))}\n')
            elif act == 'rename':
                pp = payload.split()
                if len(pp) != 2:
                    refuse(raw, 'BAD_PAYLOAD'); continue
                old, new = pp
                written = c.name[len('_root_.'):] if c.name.startswith('_root_.') else c.name
                if old not in (decl, c.name, written):
                    refuse(raw, 'RENAME_MISMATCH'); continue
                out.write(f'{where}\t{s1}\t{e1}\tsubst\t{owner}\t{esc(old + " " + new)}\n')
            S['resolved_' + act] += 1
    out.close()
    if ref:
        ref.close()
    json.dump(dict(sorted(S.items())), sys.stderr, indent=1); sys.stderr.write('\n')
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sp = ap.add_subparsers(dest='cmd', required=True)
    i = sp.add_parser('index'); i.add_argument('project'); i.add_argument('--srcdir', default='src')
    i.add_argument('--modules')
    r = sp.add_parser('resolve'); r.add_argument('project'); r.add_argument('v2', nargs='+')
    r.add_argument('--out', required=True); r.add_argument('--refused'); r.add_argument('--srcdir', default='src')
    r.add_argument('--relocate', action='store_true')
    a = ap.parse_args()
    return cmd_index(a) if a.cmd == 'index' else cmd_resolve(a)


if __name__ == '__main__':
    sys.exit(main() or 0)

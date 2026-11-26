#!/usr/bin/env python3
"""dedup_edits.py PLAN_TSV SRC_DIR OUT_EDITS [--actions ALIAS,IMPORT] [--mode proof|alias] [--modules FILE]

Turns a dupplan.py plan into an EDIT LIST (shared composition format, one TSV line per edit, against the ORIGINAL
sources):  module  start_line  end_line  action  owner  replacement
  action = replace (lines start..end, 1-based inclusive, replaced by `replacement`, '\\n'-escaped)
         | insert_before (replacement inserted before line start; end = start - 1)
Edits per member (actions ALIAS/IMPORT of the plan; its target is a KEPT copy with the identical kernel statement):
  --mode proof (default): the member keeps its statement text; its proof (from the first ':=' at bracket depth 0 that
      does not belong to a let/have of the statement, to the end of the declaration) becomes
      `:= by first | exact T | [exact T <explicit binder names> |] (intros; apply T <;> assumption)` (T = `_root_.<target>`).
  --mode auto: alias mode when the member and its target have the same binder infos (plan column binfo_eq), else
      proof mode (where `exact T <explicit binder names>` is tried first when the binders parse).
  --mode alias: the whole declaration becomes `<modifiers> alias <declared name> := T` (statement text deleted; the
      alias gets T's kernel type, alpha-equal to the member's).
  IMPORT members additionally give their module `import <target module>` (after the last import line); with
  --cp-guard only when that import cannot delay the module's start in the build (critical path cannot grow).
Members whose declaration text cannot be parsed safely (no top-level ':=', `where`/`|` bodies, `termination_by`,
`decreasing_by`, a `#` command, nested declarations) are skipped and counted.
"""
import sys, os, re, collections, json, argparse

ap = argparse.ArgumentParser()
ap.add_argument('plan'); ap.add_argument('src'); ap.add_argument('out')
ap.add_argument('--actions', default='ALIAS,IMPORT')
ap.add_argument('--mode', default='proof', choices=['proof', 'alias', 'auto'])
ap.add_argument('--modules', default=None, help='only members of these modules (one per line)')
ap.add_argument('--owner', default='P03-dedup')
ap.add_argument('--redirect', default=None, help='redirect_check.py output: members with verdict OK/OK-unused are '
                'DELETED (instead of aliased) and every module that references them gets a module-wide subst edit')
ap.add_argument('--alias-form', default='alias', choices=['alias', 'typeof'],
                help="alias: `alias x := T` (Batteries/Mathlib command); typeof: `theorem x : type_of% @T := @T` (core Lean)")
ap.add_argument('--protect-from', default=None, metavar='COMPARATOR_JSON',
                help="never edit or delete the challenge's theorem_names/definition_names (REQUIRED unless --protect)")
ap.add_argument('--protect', default='', help='comma-separated extra names that are never edited or deleted')
ap.add_argument('--scan', default=None, help='dupscan scan output dir: binder signatures for the proof-mode refine form')
ap.add_argument('--cp-guard', nargs=2, metavar=('IMPORTS_JSON', 'COSTS_JSON_GZ'), default=None,
                help='accept an IMPORT member only if the added import cannot delay its module in the build '
                     '(finish(target module) <= start(module) under the given per-module costs)')
ap.add_argument('--keep-zero', action='store_true', help='also edit members whose proof is already one line')
a = ap.parse_args()
ACTS = set(a.actions.split(','))
only = set(open(a.modules).read().split()) if a.modules else None

IDRE = re.compile(r"^[A-Za-z_α-κμ-ϻἀ-῾℀-⅏\U0001d49c-\U0001d59f][A-Za-z0-9_'!?α-κμ-ϻἀ-῾℀-⅏₀-ₜᵢ-ᵪ\U0001d49c-\U0001d59f]*$")
KEYWORDS = {'fun', 'by', 'have', 'show', 'from', 'at', 'with', 'then', 'else', 'if', 'do', 'match', 'let', 'in',
            'where', 'end', 'open', 'theorem', 'lemma', 'def', 'instance', 'example', 'calc', 'local', 'section',
            'namespace', 'variable', 'universe', 'import', 'private', 'protected', 'noncomputable', 'set_option'}
def user_name(full):
    """kernel name -> source-level full name (strips the private prefix _private.<Mod>.0.)"""
    if full.startswith('_private.'):
        i = full.find('.0.')
        if i > 0:
            return full[i + 3:]
    return full
def esc(name):
    parts = name.split('.')
    out = []
    for p in parts:
        if IDRE.match(p) and p not in KEYWORDS:
            out.append(p)
        else:
            out.append('«' + p + '»')
    return '.'.join(out)

OPEN = {'(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄'}
CLOSE = set(OPEN.values())
def scan_tokens(L):
    """yield (line_idx, col, kind) for depth-0 ':=' and ':' (outside comments/strings), in order"""
    depth = 0; incom = 0
    for i, line in enumerate(L):
        j = 0; n = len(line); instr = False
        while j < n:
            ch = line[j]
            if incom:
                if line.startswith('-/', j): incom -= 1; j += 2; continue
                if line.startswith('/-', j): incom += 1; j += 2; continue
                j += 1; continue
            if instr:
                if ch == '\\': j += 2; continue
                if ch == '"': instr = False
                j += 1; continue
            if ch == '"': instr = True; j += 1; continue
            if line.startswith('/-', j): incom += 1; j += 2; continue
            if line.startswith('--', j): break
            if ch in OPEN: depth += 1
            elif ch in CLOSE: depth = max(0, depth - 1)
            elif depth == 0 and line.startswith(':=', j):
                yield (i, j, ':='); j += 2; continue
            elif depth == 0 and ch == ':':
                yield (i, j, ':')
            elif depth == 0 and (ch.isalpha() or ch == '_') and (j == 0 or not (line[j-1].isalnum() or line[j-1] in "_.'")):
                k = j
                while k < n and (line[k].isalnum() or line[k] in "_'!?."):
                    k += 1
                w = line[j:k]
                if w in LETS:
                    yield (i, j, 'let')
                j = k; continue
            j += 1

LETS = {'let', 'letI', 'have', 'haveI', 'set', 'let_fun'}
def explicit_binder_names(txt):
    """names of the explicit binders of a pre-colon binder text, or None if unparseable"""
    names = []; depth = 0; i = 0; n = len(txt); start = None; opener = None
    while i < n:
        ch = txt[i]
        if depth == 0:
            if ch in OPEN:
                depth = 1; start = i + 1; opener = ch
            elif not ch.isspace():
                return None  # something that is not a bracketed binder group
        else:
            if ch in OPEN: depth += 1
            elif ch in CLOSE:
                depth -= 1
                if depth == 0:
                    grp = txt[start:i]
                    if opener == '(':
                        k = grp.find(':')
                        if k < 0:
                            return None
                        ns = grp[:k].split()
                        if not ns or any(x == '_' or not IDRE.match(x) for x in ns):
                            return None
                        names.extend(ns)
        i += 1
    return names if depth == 0 else None

DECL = re.compile(r'(^|\s)(theorem|lemma)\s+(\S+)')
srccache = {}
def lines_of(mod):
    if mod not in srccache:
        p = os.path.join(a.src, mod.replace('.', '/') + '.lean')
        srccache[mod] = open(p, encoding='utf-8').read().split('\n')
    return srccache[mod]

S = collections.Counter()
edits = []
protect = set(x for x in a.protect.split(',') if x)
if a.protect_from:
    cj = json.load(open(a.protect_from))
    protect |= set(cj.get('theorem_names', [])) | set(cj.get('definition_names', []))
if not protect:
    sys.exit('dedup_edits: give --protect-from COMPARATOR_JSON (or --protect NAMES): the challenge targets must never be edited')
redir = {}
if a.redirect:
    for l in open(a.redirect, encoding='utf-8'):
        x = l.rstrip('\n').split('\t')
        if len(x) >= 5 and x[4] in ('OK', 'OK-unused'):
            redir[x[0]] = [u.split(':')[0] for u in x[3].split(';') if u]
nbind = {}
if a.scan:
    import glob
    want = set()
    for l in open(a.plan):
        x = l.rstrip('\n').split('\t')
        if len(x) > 15 and x[1] in ACTS and x[15] != '1':
            want.add(x[2])
    for f in sorted(glob.glob(a.scan + '/c*.tsv')):
        for l in open(f, encoding='utf-8', errors='replace'):
            x = l.rstrip('\n').split('\t')
            if x[0] == 'K' and x[3] in want and len(x) > 12:
                nbind[x[3]] = len(x[12])
mfinish = mstart = None
if a.cp_guard:
    import gzip
    impg = json.load(open(a.cp_guard[0])); cost = json.load(gzip.open(a.cp_guard[1]))
    deps = {m: [d for d in v['imports'] if d in impg] for m, v in impg.items()}
    mfinish = {}; mstart = {}
    order = []; state = {}
    for m0 in deps:
        if m0 in state: continue
        st = [(m0, iter(deps[m0]))]; state[m0] = 1
        while st:
            m, it = st[-1]; nxt = None
            for d in it:
                if d not in state: nxt = d; break
            if nxt is None: st.pop(); order.append(m)
            else: state[nxt] = 1; st.append((nxt, iter(deps[nxt])))
    for m in order:
        mstart[m] = max((mfinish[d] for d in deps[m]), default=0.0)
        mfinish[m] = mstart[m] + cost.get(m, 1.0)
imports = collections.defaultdict(set)
rows = [l.rstrip('\n').split('\t') for l in open(a.plan)][1:]
hdr = None
for r in rows:
    (gi, act, name, mod, tgt, tmod, sl, pl, incl, indeg, priv, l1, l2) = r[:13]
    if act not in ACTS:
        continue
    if only is not None and mod not in only:
        continue
    S['members'] += 1
    if name in protect or user_name(name) in protect:
        S['skip_protected'] += 1; continue
    if act == "IMPORT" and mfinish is not None and mfinish.get(tmod, 0) > mstart.get(mod, 0) + 1e-9:
        S['skip_cp_guard'] += 1; continue
    l1, l2 = int(l1), int(l2)
    L = lines_of(mod)[l1 - 1:l2]
    text = '\n'.join(L)
    if re.search(r'\b(termination_by|decreasing_by|where)\b', text) or '#' in ''.join(x.split('--')[0] for x in L if x.lstrip().startswith('#')):
        S['skip_special'] += 1; continue
    m = DECL.search(L[0]) if L else None
    if not m:
        # modifiers / attributes / docstring on earlier lines: find the keyword line
        km = None
        for k, x in enumerate(L):
            mm = DECL.search(x)
            if mm:
                km = (k, mm); break
        if km is None:
            S['skip_nokeyword'] += 1; continue
        kline, m = km
    else:
        kline = 0
    # declared name must match the kernel name's tail
    declared = re.sub(r'\.\{[^}]*\}$', '', m.group(3)).rstrip(':')
    un = user_name(name)
    if not (un == declared or un.endswith('.' + declared) or declared.startswith('_root_.') and declared[7:] == un):
        S['skip_name_mismatch'] += 1; continue
    toks = [t for t in scan_tokens(L) if (t[0], t[1]) > (kline, m.end(3) - (0 if kline else 0) - 1)]
    colon = next((t for t in toks if t[2] == ':'), None)
    assign = None
    if colon is not None:
        pending = 0
        for t in toks:
            if (t[0], t[1]) <= (colon[0], colon[1]):
                continue
            if t[2] == 'let':
                pending += 1
            elif t[2] == ':=':
                if pending:
                    pending -= 1
                else:
                    assign = t; break
    if assign is None or colon is None or (colon[0], colon[1]) > (assign[0], assign[1]):
        S['skip_noassign'] += 1; continue
    # a second top-level ':=' after the proof start would mean nested commands / `where`: be conservative
    # (tactic proofs contain ':=' only inside have/let/set which are at depth 0 too, so we cannot use that test; rely on
    # the declaration range from declRangeExt instead)
    T = '_root_.' + esc(user_name(tgt))
    pre = L[kline][m.end(3):] if colon[0] == kline else None
    binders = True
    if colon[0] == kline:
        between = L[kline][m.end(3):colon[1]]
        binders = between.strip() != ''
    else:
        between = '\n'.join([L[kline][m.end(3):]] + L[kline + 1:colon[0]] + [L[colon[0]][:colon[1]]])
        binders = between.strip() != ''
    mode = a.mode
    if mode == 'auto':
        mode = 'alias' if (len(r) > 15 and r[15] == '1') else 'proof'
    S['mode_' + mode] += 1
    if mode == 'proof':
        # never a bare `:= T`: section `variable`s can add leading binders that the source does not show
        bn = explicit_binder_names(between) if binders else None
        alts = [f'exact {T}']
        if bn:
            alts.append(f'exact {T} {" ".join(bn)}')
        k = nbind.get(name)
        if k:
            # all k binders of the (identical) telescope are in context after `intros`: full explicit application
            # with every argument a new goal; unification assigns the determined ones, `assumption` the rest
            alts.append(f'(intros; refine @{T}{" ?_" * k} <;> assumption)')
        alts.append(f'(intros; apply {T} <;> assumption)')
        proof = ':= by first | ' + ' | '.join(alts)
        ai, aj = assign[0], assign[1]
        newline = L[ai][:aj] + proof
        start = l1 + ai; end = l2
        if end - start + 1 <= 1 and not a.keep_zero:
            S['skip_zero_gain'] += 1; continue
        edits.append((mod, start, end, 'replace', newline))
        S['edited'] += 1; S['edited_' + act] += 1
        S['lines_removed'] += (end - start + 1) - 1
    else:
        # modifiers: everything on the keyword line before the keyword, plus attribute/doc lines before it
        prefix = L[kline][:m.start(2)]
        head = '\n'.join(L[:kline] + [prefix]) if kline else prefix
        dn = re.sub(r'\.\{[^}]*\}$', '', declared).rstrip(':')
        if name in redir and '.' in un and not (tgt.startswith('_private.') and any(um != tmod for um in redir[name])):
            # dotted full names only (a bare name could also be a local variable); a PRIVATE target can only replace
            # references inside its own module
            # REDIRECT: delete the declaration; every module that references it by full name gets a subst edit.
            # Command modifiers directly above it (`set_option ... in`, `open ... in`, `omit/include ... in`) go too.
            ML = lines_of(mod); d1 = l1
            MOD_KW = r'^\s*(?:set_option|open|omit|include|variable|attribute)\b'
            STOP_KW = r'^\s*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|namespace|section|end|import|alias)\b'
            while d1 > 1:
                k = d1 - 1
                while k > 1 and ML[k - 1].strip() == '':
                    k -= 1
                if k >= 1 and re.search(r'(?:^|\s)in\s*(?:--.*)?$', ML[k - 1]):
                    # Walk back over multi-line continuation to the modifier keyword
                    m0 = k
                    while m0 > 1 and not re.match(MOD_KW, ML[m0 - 1]):
                        if ML[m0 - 1].strip() == '' or re.match(STOP_KW, ML[m0 - 1]):
                            m0 = 0; break
                        m0 -= 1
                    if m0 >= 1 and re.match(MOD_KW, ML[m0 - 1]):
                        d1 = m0
                        continue
                break
            S['modifier_lines_deleted'] += l1 - d1
            edits.append((mod, d1, l2, 'delete', ''))
            newn = user_name(tgt)
            for um in set(redir[name]) | {mod}:
                edits.append((um, l1 if um == mod else 0, l2 if um == mod else 0, 'subst', f'{un} {newn}'))
            S['edited'] += 1; S['edited_' + act] += 1; S['redirected'] += 1
            S['lines_removed'] += l2 - l1 + 1
            if act == 'IMPORT':
                imports[mod].add(tmod)
                for um in redir[name]:
                    if um != tmod:
                        imports[um].add(tmod)
            continue
        if a.alias_form == 'alias':
            newtxt = f'{head}alias {dn} := {T}'
        else:
            newtxt = f'{head}theorem {dn} : type_of% @{T} := @{T}'
        if l2 - l1 + 1 <= 1 + newtxt.count('\n') and not a.keep_zero:
            S['skip_zero_gain'] += 1; continue
        edits.append((mod, l1, l2, 'replace', newtxt))
        S['edited'] += 1; S['edited_' + act] += 1
        S['lines_removed'] += (l2 - l1 + 1) - newtxt.count('\n') - 1
    if act == 'IMPORT':
        imports[mod].add(tmod)

for mod, ms in imports.items():
    L = lines_of(mod)
    last = 0
    for i, x in enumerate(L):
        s = x.strip()
        if s.startswith('import '):
            last = i + 1
        elif s == '' or s.startswith('--'):
            continue
        else:
            break
    existing = set()
    for x in L[:last]:
        if x.strip().startswith('import '):
            existing.update(x.strip()[7:].split())
    new = sorted(ms - existing)
    if new:
        edits.append((mod, last + 1, last, 'insert_before', '\n'.join('import ' + n for n in new)))
        S['import_lines_added'] += len(new); S['modules_with_new_imports'] += 1

S['modules_edited'] = len(set(e[0] for e in edits))
with open(a.out, 'w') as fh:
    for mod, s, e, act, txt in sorted(edits, key=lambda e: (e[0], e[1])):
        fh.write(f"{mod}\t{s}\t{e}\t{act}\t{a.owner}\t{txt.replace(chr(92), chr(92)*2).replace(chr(10), chr(92)+'n')}\n")
print(json.dumps(S, indent=1, sort_keys=True))

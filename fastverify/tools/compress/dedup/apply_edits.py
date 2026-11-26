#!/usr/bin/env python3
"""apply_edits.py PROJECT_DIR OUT_DIR EDITS.tsv [EDITS2.tsv ...] [--srcdir src] [--priority OWNER1,OWNER2] [--copy]

Shared composition applier. Copies the Lean project PROJECT_DIR to OUT_DIR (hard links for unchanged files unless
--copy; edited files are always written as new files, so the original tree is never modified) and applies edit lists
in the team format (one TSV line per edit, line numbers against the ORIGINAL files, 1-based inclusive):
  module  start  end  action  owner  replacement('\\n'-escaped)
  action: replace (lines start..end -> replacement) | delete (lines start..end removed) |
          insert_before (replacement inserted before line start; end = start-1) |
          newfile (start = end = 0; the module's file is created with `replacement` as content) |
          deletefile (start = end = 0; the module's file is removed; other edits of that module become conflicts) |
          subst (replacement = 'OLD NEW': every identifier token OLD of the module is replaced by NEW, AFTER all
                 structural edits of the module; never conflicts; start/end are informational)
Overlapping edits of one module: the edit of the owner earlier in --priority wins (default: the first edit list wins);
the losers are reported in OUT_DIR/.apply-conflicts.tsv. A module whose edits leave it empty is kept (an empty module
is valid Lean). Summary (files/lines before and after) is printed as JSON and written to OUT_DIR/.apply-summary.json.
"""
import sys, os, re, shutil, json, argparse, collections

ap = argparse.ArgumentParser()
ap.add_argument('project'); ap.add_argument('out'); ap.add_argument('edits', nargs='+')
ap.add_argument('--srcdir', default='src')
ap.add_argument('--priority', default='')
ap.add_argument('--copy', action='store_true')
a = ap.parse_args()
prio = {o: i for i, o in enumerate(a.priority.split(',')) if o}

def unesc(s):
    out = []; i = 0
    while i < len(s):
        if s[i] == '\\' and i + 1 < len(s):
            out.append('\n' if s[i + 1] == 'n' else s[i + 1]); i += 2
        else:
            out.append(s[i]); i += 1
    return ''.join(out)

E = collections.defaultdict(list)
for k, f in enumerate(a.edits):
    for ln in open(f, encoding='utf-8'):
        p = ln.rstrip('\n').split('\t', 5)
        if len(p) < 5:
            continue
        mod, s, e, act, owner = p[:5]
        txt = unesc(p[5]) if len(p) > 5 else ''
        E[mod].append((int(s), int(e), act, owner, txt, prio.get(owner, 1000 + k)))

if os.path.exists(a.out):
    sys.exit(f'apply_edits: {a.out} exists')
t = shutil.copytree(a.project, a.out, symlinks=True, copy_function=(shutil.copy2 if a.copy else os.link),
                    ignore=shutil.ignore_patterns('.lake', '.git'))
S = collections.Counter(); conflicts = []
for mod, es in E.items():
    path = os.path.join(a.out, a.srcdir, mod.replace('.', '/') + '.lean')
    if any(x[2] == 'deletefile' for x in es):
        if os.path.exists(path):
            os.unlink(path)
        S['files_deleted'] += 1
        S['lines_deleted_files'] += len(open(os.path.join(a.project, a.srcdir, mod.replace('.', '/') + '.lean'), encoding='utf-8').read().split('\n'))
        others = [x for x in es if x[2] != 'deletefile']
        for x in others:
            conflicts.append((mod, x[0], x[1], x[2], x[3]))
        continue
    if any(x[2] == 'newfile' for x in es):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        if os.path.exists(path):
            os.unlink(path)
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(next(x for x in es if x[2] == 'newfile')[4])
        S['new_files'] += 1
        continue
    orig = open(path, encoding='utf-8').read().split('\n')
    # conflict resolution: keep non-overlapping edits by priority
    es.sort(key=lambda x: (x[5], x[0]))
    taken = []
    for x in es:
        if x[2] == 'subst':
            taken.append((-1, -1, x)); continue
        s, e = x[0], x[1]
        lo, hi = (s, e) if x[2] != 'insert_before' else (s - 0.5, s - 0.5)
        clash = any(not (hi < tl or lo > th) for (tl, th, y) in taken if y[2] != 'subst')
        if clash:
            conflicts.append((mod, x[0], x[1], x[2], x[3])); continue
        taken.append((lo, hi, x))
    substs = [x for x in es if x[2] == 'subst']
    taken = [t for t in taken if t[2][2] != 'subst']
    new = list(orig)
    # apply from the bottom up so line numbers stay valid
    for lo, hi, x in sorted(taken, key=lambda t: (-t[0], -t[1])):
        s, e, act, owner, txt = x[:5]
        if act == 'replace':
            new[s - 1:e] = txt.split('\n')
        elif act == 'delete':
            new[s - 1:e] = []
        elif act == 'insert_before':
            new[s - 1:s - 1] = txt.split('\n')
        S['edits_' + act] += 1; S['edits_by_' + owner] += 1
    if substs:
        # module-wide identifier substitution OLD -> NEW, applied after every structural edit of the module (so it
        # also reaches text that other owners rewrote); OLD must be a full declaration name that no longer exists
        # scope commands (namespace/section/end/open) are never rewritten: a deleted theorem's name can be a namespace prefix
        keep = {i: ln for i, ln in enumerate(new) if re.match(r'\s*(namespace|section|end|open|export)\b', ln)}
        txt = '\n'.join('' if i in keep else ln for i, ln in enumerate(new))
        # one pass for all substitutions of the module (targets are never themselves substituted, so no chaining)
        mp = {}
        for x in substs:
            oldn, newn = x[4].split(' ', 1)
            mp[oldn] = newn; S['edits_by_' + x[3]] += 1
        alt = '|'.join(re.escape(o) for o in sorted(mp, key=len, reverse=True))
        # an occurrence may be written `_root_.OLD`; NEW may itself be `_root_.T` (unambiguous: a bare `T` written inside
        # `namespace N` resolves to `N.T` first - RH: a root-level target `main` captured by a local `main`; D17)
        pat = re.compile(r"(?<![^\s()\[\]{}⟨⟩,;@←·$`|:=<>+*/\\^&!~-])(_root_\.)?(" + alt + r")(?![A-Za-z0-9_'!?\u0370-\u03ff\u1f00-\u1ffe\u2100-\u214f\u2080-\u209c\u1d62-\u1d6a\u2c7c])")
        def _rep(mo):
            nw = mp[mo.group(2)]
            return nw if nw.startswith('_root_.') else (mo.group(1) or '') + nw
        txt, k = pat.subn(_rep, txt)
        S['subst_hits'] += k
        new = txt.split('\n')
        for i, ln in keep.items():
            new[i] = ln
    os.unlink(path)  # break the hard link before writing
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(new))
    S['files_edited'] += 1
    S['lines_before_edited_files'] += len(orig); S['lines_after_edited_files'] += len(new)
with open(os.path.join(a.out, '.apply-conflicts.tsv'), 'w') as fh:
    for c in conflicts:
        fh.write('\t'.join(map(str, c)) + '\n')
S['conflicts'] = len(conflicts)
S['lines_removed'] = S['lines_before_edited_files'] - S['lines_after_edited_files'] + S['lines_deleted_files']
json.dump(S, open(os.path.join(a.out, '.apply-summary.json'), 'w'), indent=1, sort_keys=True)
print(json.dumps(S, indent=1, sort_keys=True))

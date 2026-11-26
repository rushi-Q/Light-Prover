#!/usr/bin/env python3
"""newlist_guard.py DECLS_TSV NEW.tsv OUT.tsv --deleted LIST... [--report R.tsv] [--src ORIG_SRC_DIR]

Name safety for an edit list that joins a train AFTER the pruning lists were computed (stage 3).
The pruning rounds (P01, P01r2) protect the names mentioned by the lists they were run with (--other-edits, inside the
fixpoint); a list that arrives later can mention a declaration that P01 / P01r2 / P03-dedup delete (a closer
`simp [foo]` written against the original tree, an `import M` of a deleted file). Such an edit would fail to build.

Rule (conservative, untrusted, only drops edits): code text of `replace` / `insert_before` rows (comments and strings
removed; docstrings / module docs are not code) is tokenized; a token, or any dotted prefix of it, that equals a
deleted declaration's full name or a dot-suffix of one (`foo`, `Ns.foo` for `A.Ns.foo`) flags the row; `import M` of a
module deleted as a whole flags the row. With --src, tokens that the ORIGINAL declaration already contains are not
checked (the declaration is kept, so the pruning closure kept what they name), and Lean keywords / tactic names are skipped. A flagged row drops every row of the same list in the same declaration
(DECLS ranges, original coordinates) - rows inside one declaration are coupled (e.g. several closer positions).
`subst` rows (renames, redirects) and `delete` rows pass unchanged (a rename of a deleted name is a no-op).

DECLS_TSV: prune.py's R.json.decls.tsv (#module start end kind live deleted names) of the ORIGINAL tree.
Deleted declarations: a declaration whose first line lies inside a `delete` row of a --deleted list, or every
declaration of a module with a `deletefile` row.
"""
import bisect, collections, re, sys

def unesc(t):
    return t.replace('\\n', '\n').replace('\\t', '\t')

COMMENT = re.compile(r'/-.*?-/', re.S)
LINEC = re.compile(r'--[^\n]*')
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')
IDENT = re.compile(r"«[^»]*»|[A-Za-z_À-῿℀-⅏\U0001d400-\U0001d7ff][\w'!?À-῿℀-⅏\U0001d400-\U0001d7ff₀-₉ᵢ-ᵪ]*(?:\.[A-Za-z_À-῿℀-⅏«][\w'!?À-῿℀-⅏₀-₉ᵢ-ᵪ»]*)*")
KEYWORDS = set('''by fun at with only using this exact apply refine intro intros rfl simp simp_all dsimp simpa norm_num ring
ring_nf field_simp linarith nlinarith positivity omega decide aesop gcongr constructor use exists left right cases rcases obtain
induction rw rwa erw show have let calc conv congr ext funext trivial assumption contradiction exfalso push_neg by_contra
by_cases split_ifs unfold change convert exact_mod_cast push_cast norm_cast tauto infer_instance first try repeat all_goals
any_goals case next fin_cases interval_cases subst symm trans refl from in if then else match do return true false Type Prop
Sort sorry abel group noncomm_ring module polyrith bound continuity measurability fun_prop filter_upwards nth_rw nth_rewrite
specialize generalize clear set suffices lift zify qify rify mod_cast exists_prop and or not iff'''.split())
IMPORT = re.compile(r'^\s*import\s+(\S+)', re.M)

def code_of(text):
    t = COMMENT.sub(' ', text)       # also removes /-- docstrings -/ and /-! module docs -/
    t = LINEC.sub(' ', t)
    return STRING.sub(' ', t)

def main(argv):
    if len(argv) < 5 or '--deleted' not in argv:
        sys.exit(__doc__)
    decls, new, out = argv[1:4]
    i = argv.index('--deleted'); rest = argv[i + 1:]
    report = None
    if '--report' in rest:
        j = rest.index('--report'); report = rest[j + 1]; rest = rest[:j] + rest[j + 2:]
    if '--src' in rest:
        j = rest.index('--src'); rest = rest[:j] + rest[j + 2:]
    dels = rest
    # declarations (original coordinates)
    D = collections.defaultdict(list)   # module -> [(start, end, names)]
    for ln in open(decls, encoding='utf-8'):
        if ln.startswith('#'): continue
        p = ln.rstrip('\n').split('\t')
        if len(p) < 7: continue
        D[p[0]].append((int(p[1]), int(p[2]), p[6].split()))
    for m in D: D[m].sort()
    starts = {m: [d[0] for d in L] for m, L in D.items()}
    # deletions
    iv = collections.defaultdict(list); gone_mod = set()
    for f in dels:
        for ln in open(f, encoding='utf-8'):
            p = ln.rstrip('\n').split('\t')
            if len(p) < 4: continue
            if p[3] == 'deletefile': gone_mod.add(p[0])
            elif p[3] == 'delete': iv[p[0]].append((int(p[1]), int(p[2])))
    deleted = set()
    for m, L in D.items():
        if m in gone_mod:
            for s, e, ns in L: deleted.update(ns)
            continue
        I = sorted(iv.get(m, ()))
        if not I: continue
        ss = [a for a, b in I]
        for s, e, ns in L:
            k = bisect.bisect_right(ss, s) - 1
            if k >= 0 and I[k][0] <= s <= I[k][1]: deleted.update(ns)
    kept_full = set()
    for m, L in D.items():
        for s, e, ns in L:
            for n in ns:
                if n not in deleted: kept_full.add(n)
    gone_full = deleted - kept_full
    suf = set()
    for n in deleted:
        if n in kept_full: continue      # the same full name survives elsewhere (private / duplicated names)
        parts = n.split('.')
        for k in range(len(parts)):
            suf.add('.'.join(parts[k:]))
    def decl_of(m, s):
        L = D.get(m);
        if not L: return None
        k = bisect.bisect_right(starts[m], s) - 1
        return (m, L[k][0]) if k >= 0 and L[k][0] <= s <= L[k][1] else None
    src = None
    if '--src' in argv:
        src = argv[argv.index('--src') + 1]
    cache = {}
    def orig_tokens(m, key):
        # tokens of the ORIGINAL declaration text: a token the declaration already used still resolves in the train
        # (the declaration is kept, so its original references are kept by the pruning closure)
        if src is None or key is None or key[1] == 'line': return set()
        if m not in cache:
            try: cache[m] = open(f"{src}/{m.replace('.', '/')}.lean", encoding='utf-8').read().split('\n')
            except OSError: cache[m] = []
        L = D.get(m, []); k = bisect.bisect_right(starts[m], key[1]) - 1
        s, e = L[k][0], L[k][1]
        return set(IDENT.findall(code_of('\n'.join(cache[m][s - 1:e]))))
    rows = [ln for ln in open(new, encoding='utf-8') if ln.strip()]
    flagged = {}; bad_keys = set()
    for idx, ln in enumerate(rows):
        p = ln.rstrip('\n').split('\t')
        if len(p) < 6 or p[3] not in ('replace', 'insert_before'): continue
        text = unesc(p[5]); why = None
        for mm in IMPORT.findall(text):
            if mm in gone_mod: why = f'import of deleted module {mm}'; break
        if why is None:
            known = orig_tokens(p[0], decl_of(p[0], int(p[1])))
            for tok in IDENT.findall(code_of(text)):
                if tok in known or tok in KEYWORDS: continue
                rooted = tok.startswith("_root_.")
                t = tok[7:] if rooted else tok
                parts = t.split('.')
                for k in range(len(parts), 0, -1):
                    c = '.'.join(parts[:k])
                    if (c in gone_full) if rooted else (c in suf):   # a `_root_.` name is the full name
                        why = f'mentions deleted {c}'; break
                if why: break
        if why:
            flagged[idx] = why
            key = decl_of(p[0], int(p[1])) or (p[0], 'line', int(p[1]))
            bad_keys.add(key)
    kept = dropped = 0
    rep = []
    with open(out, 'w', encoding='utf-8') as fo:
        for idx, ln in enumerate(rows):
            p = ln.rstrip('\n').split('\t')
            key = None
            if p[3] in ('replace', 'insert_before', 'delete'):
                key = decl_of(p[0], int(p[1])) or (p[0], 'line', int(p[1]))
            if key is not None and key in bad_keys:
                dropped += 1; rep.append(f'{p[0]}\t{p[1]}\t{p[3]}\t{flagged.get(idx, "same declaration as a flagged row")}')
                continue
            fo.write(ln); kept += 1
    if report:
        with open(report, 'w', encoding='utf-8') as fr: fr.write('\n'.join(rep) + ('\n' if rep else ''))
    print(f'newlist_guard: {len(deleted)} deleted declarations ({len(gone_mod)} deleted modules); '
          f'rows kept {kept}, dropped {dropped} ({len(flagged)} flagged, {len(bad_keys)} declarations)')

if __name__ == '__main__':
    main(sys.argv)

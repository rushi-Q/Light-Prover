#!/usr/bin/env python3
"""Dead-have elimination (DHE): map kernel-detected dead `let`s (expdiff dead --tsv, kind=let, origin=project) to
`have NAME ...` blocks in the RH sources and emit an edit list in the team format
(module<TAB>start<TAB>end<TAB>delete<TAB>P05-dhe<TAB>) against the ORIGINAL sources.

usage: dhe.py DEAD_TSV DECLS_TSV SRC_ROOT OUT_EDITS [--stats OUT_JSON] [--lets LETS_TSV]
LETS_TSV (expdiff lets --tsv): kernel let order; with it, a binder name that occurs several times in a declaration is
matched to its `have NAME` lines by position (same count required, one kernel constant per name).
DECLS_TSV = a declaration table (module, name, kw, line, lines, ...).
Only theorem/lemma commands are edited (proof irrelevance: importers cannot observe a changed proof).
Conservative rules (skip when unsure): exactly one dead let with that binder name in the declaration AND exactly one
`have NAME` line (anonymous `have :` for `this`) in the declaration's line range; the line starts with `have` after
indentation (no bullet, no `;`); the block = that line + following lines indented deeper; it must contain `:=`;
hygienic (compiler) binder names are skipped."""
import csv, json, re, sys, collections

csv.field_size_limit(10**9)

def parent(n):
    m = re.sub(r'\._proof_\d+(_\d+)*$', '', n)
    m = re.sub(r'\.match_\d+$', '', m)
    if m.startswith('_private.'):
        parts = m.split('.0.', 1)
        if len(parts) == 2:
            m = parts[1]
    return m

def main():
    dead_tsv, decls_tsv, src, out = sys.argv[1:5]
    stats_out = sys.argv[sys.argv.index('--stats') + 1] if '--stats' in sys.argv else None
    lets_tsv = sys.argv[sys.argv.index('--lets') + 1] if '--lets' in sys.argv else None
    decls = {}
    with open(decls_tsv) as f:
        r = csv.reader(f, delimiter='\t'); next(r)
        for row in r:
            decls[row[1]] = (row[0], int(row[3]), int(row[4]), row[2])
    # dead lets per source decl and binder name
    per = collections.defaultdict(collections.Counter)
    kdec = collections.defaultdict(set)   # (source decl, binder) -> kernel decls with a dead let of that name
    st = collections.Counter()
    with open(dead_tsv) as f:
        r = csv.reader(f, delimiter='\t'); next(r)
        for row in r:
            if row[1] != 'project' or row[3] != 'let':
                continue
            st['dead_lets'] += 1
            n = row[0]
            key = n if n in decls else parent(n)
            if key not in decls:
                st['unmapped_decl'] += 1
                continue
            if decls[key][3] not in ('theorem', 'lemma'):
                # only proofs: a theorem's value is never unfolded by its users (proof irrelevance), so importers
                # cannot observe the edit; definition bodies are left alone
                st['skip_not_theorem'] += 1
                continue
            b = row[4]
            if '._@.' in b or b == '?' or b.startswith('_'):
                st['hygienic_or_anonymous_binder'] += 1
                continue
            per[key][b] += 1
            kdec[(key, b)].add(n)
    # v6: kernel let order (expdiff lets --tsv): (kernel decl, binder) -> [dead flags in preorder]; and which kernel
    # decls of a source decl carry a let with a given name at all
    order = {}
    owners = collections.defaultdict(set)
    if lets_tsv:
        want = set()
        for (key, b), ks in kdec.items():
            want.add(b)
        with open(lets_tsv) as f:
            r = csv.reader(f, delimiter='\t'); next(r)
            for row in r:
                if row[2] not in want:
                    continue
                n = row[0]
                key = n if n in decls else parent(n)
                if (key, row[2]) not in kdec:
                    continue
                order.setdefault((n, row[2]), []).append(row[3] == '1')
                owners[(key, row[2])].add(n)
    files = {}
    def lines_of(mod):
        if mod not in files:
            p = f"{src}/{mod.replace('.', '/')}.lean"
            try:
                files[mod] = open(p, encoding='utf-8').read().split('\n')
            except OSError:
                files[mod] = None
        return files[mod]
    edits = []
    removed_lines = 0
    by_mod = collections.Counter()

    def block_end(L, i, hi, ind):
        j = i + 1
        while j < hi:
            s = L[j]
            if s.strip() == '':
                k = j + 1
                while k < hi and L[k].strip() == '':
                    k += 1
                if k < hi and len(L[k]) - len(L[k].lstrip()) > ind:
                    j = k; continue
                break
            if len(s) - len(s.lstrip()) > ind:
                j += 1; continue
            break
        return j
    for dname, names in per.items():
        mod, l0, nl, _kw = decls[dname]
        L = lines_of(mod)
        if L is None:
            st['no_source'] += sum(names.values()); continue
        lo, hi = l0 - 1, min(len(L), l0 - 1 + nl)   # 0-based [lo, hi)
        for b, cnt in names.items():
            if b == 'this':
                pat = re.compile(r'^(\s*)have(\s+this\b|\s*:)')
            else:
                pat = re.compile(r'^(\s*)have\s+' + re.escape(b) + r'(\s|:|$)')
            cands = [i for i in range(lo, hi) if pat.match(L[i])]
            if lets_tsv and (cnt != 1 or len(cands) > 1) and len(owners.get((dname, b), ())) == 1:
                kd = next(iter(owners[(dname, b)]))
                seq = order.get((kd, b), [])
                if len(seq) == len(cands) and len(cands) >= 2 and any(seq):
                    tok = re.compile(r'(?<![\w.\'])' + re.escape(b) + r'(?![\w\'])')
                    nb = 0
                    for k, i in enumerate(cands):
                        if not seq[k]:
                            continue
                        if ';' in L[i]:
                            st['order_skip'] += 1; continue
                        ind = len(pat.match(L[i]).group(1))
                        j = block_end(L, i, hi, ind)
                        if ':=' not in '\n'.join(L[i:j]):
                            st['order_skip'] += 1; continue
                        nxt = cands[k + 1] if k + 1 < len(cands) else hi
                        # no reference to this (dead) binder before the next `have NAME` shadows it
                        if any(tok.search(x) for x in L[j:nxt]):
                            st['order_skip'] += 1; continue
                        edits.append((mod, i + 1, j, dname, b, 'delete', ''))
                        removed_lines += j - i
                        nb += 1
                        st['edits_order'] += 1
                    if nb:
                        by_mod[mod] += 1
                        continue
            if cnt != 1:
                # v4: several dead lets with this name - delete them all iff there are exactly as many `have NAME`
                # lines, every block is well-formed, and NAME occurs nowhere else in the declaration
                if len(cands) != cnt:
                    st['ambiguous_multiple_dead_same_name'] += cnt; continue
                tok = re.compile(r'(?<![\w.\'])' + re.escape(b) + r'(?![\w\'])')
                blocks = []
                okm = True
                for i in cands:
                    if ';' in L[i]:
                        okm = False; break
                    ind = len(pat.match(L[i]).group(1))
                    j = block_end(L, i, hi, ind)
                    if ':=' not in '\n'.join(L[i:j]):
                        okm = False; break
                    blocks.append((i, j))
                if okm:
                    starts = set(cands)
                    for k in range(lo, hi):
                        x = L[k][len(pat.match(L[k]).group(0)):] if k in starts else L[k]
                        if tok.search(x):
                            okm = False; break
                if not okm or (len(blocks) == 1 and blocks[0] == (lo, hi)):
                    st['ambiguous_multiple_dead_same_name'] += cnt; continue
                for i, j in blocks:
                    edits.append((mod, i + 1, j, dname, b, 'delete', ''))
                    removed_lines += j - i
                    st['edits_multi'] += 1
                by_mod[mod] += 1
                continue
            if len(cands) == 0:
                # `set x := e with h` / `with ← h` where only the equation h is dead: drop the with-clause
                wpat = re.compile(r'^(\s*)set\s.*?(\s+with\s+(?:←\s*)?' + re.escape(b) + r')\s*$')
                wc = [i for i in range(lo, hi) if wpat.match(L[i])]
                tok = re.compile(r'(?<![\w.\'])' + re.escape(b) + r'(?![\w\'])')
                if len(wc) == 1 and sum(1 for x in L[lo:hi] if tok.search(x)) == 1:
                    i = wc[0]
                    m = wpat.match(L[i])
                    newline = L[i][:m.start(2)]
                    edits.append((mod, i + 1, i + 1, dname, b, 'replace', newline))
                    st['set_with_edits'] += 1
                    by_mod[mod] += 1
                    continue
                st['no_have_line'] += 1; continue
            if len(cands) > 1:
                st['ambiguous_multiple_have_lines'] += 1; continue
            i = cands[0]
            ind = len(pat.match(L[i]).group(1))
            if ';' in L[i]:
                st['skip_semicolon'] += 1; continue
            j = i + 1
            while j < hi:
                s = L[j]
                if s.strip() == '':
                    # blank line inside a block only if the next non-blank line is deeper
                    k = j + 1
                    while k < hi and L[k].strip() == '':
                        k += 1
                    if k < hi and len(L[k]) - len(L[k].lstrip()) > ind:
                        j = k; continue
                    break
                if len(s) - len(s.lstrip()) > ind:
                    j += 1; continue
                break
            block = L[i:j]
            if ':=' not in '\n'.join(block):
                st['skip_no_assign'] += 1; continue
            # the name must not be mentioned anywhere else in the declaration (e.g. an unused `simp only [h]`
            # argument: dead in the kernel term, but a syntactic reference)
            tok = re.compile(r'(?<![\w.\'])' + re.escape(b) + r'(?![\w\'])')
            rest = L[lo:i] + [L[i][len(pat.match(L[i]).group(0)):]] + L[i + 1:hi]
            if b != 'this' and any(tok.search(x) for x in rest):
                st['skip_mentioned_elsewhere'] += 1; continue
            if b == 'this' and any(tok.search(x) for x in L[i + 1:hi]):
                st['skip_mentioned_elsewhere'] += 1; continue
            if j >= hi and i == lo:
                st['skip_whole_decl'] += 1; continue
            edits.append((mod, i + 1, j, dname, b, 'delete', ''))
            removed_lines += j - i
            by_mod[mod] += 1
            st['edits'] += 1
    # overlapping edits (nested haves) -> keep the outer one
    edits.sort(key=lambda e: (e[0], e[1], -e[2]))
    final = []
    for e in edits:
        if final and final[-1][0] == e[0] and e[1] <= final[-1][2]:
            st['dropped_nested'] += 1
            continue
        final.append(e)
    esc = lambda t: t.replace('\\', '\\\\').replace('\n', '\\n')
    with open(out, 'w') as f:
        for mod, a, b, dname, bn, act, txt in final:
            f.write(f"{mod}\t{a}\t{b}\t{act}\tP05-dhe\t{esc(txt)}\n")
    st['final_edits'] = len(final)
    st['final_lines'] = sum(b - a + 1 for _, a, b, _, _, act, _ in final if act == 'delete')
    st['final_replace_edits'] = sum(1 for e in final if e[5] == 'replace')
    st['modules'] = len(set(e[0] for e in final))
    st['decls'] = len(set(e[3] for e in final))
    print(json.dumps(st, indent=1))
    if stats_out:
        json.dump(st, open(stats_out, 'w'), indent=1)
    with open(out + '.detail.tsv', 'w') as f:
        for mod, a, b, dname, bn, act, txt in final:
            f.write(f"{mod}\t{a}\t{b}\t{dname}\t{bn}\t{act}\n")

main()

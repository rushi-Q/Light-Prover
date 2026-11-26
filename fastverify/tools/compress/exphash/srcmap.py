#!/usr/bin/env python3
"""srcmap.py SRC_ROOT OUT_TSV [--modules LIST] [--jobs N]

Lightweight outline of Lean 4 source files (no elaboration): every top-level declaration command with its full name
(namespaces resolved, `private` names mangled as `_private.<Module>.0.<name>`, `_root_.` honoured), keyword, and line
range [start, end] (start = first doc-comment / attribute line, end = last non-blank line before the next column-0
command).  Output TSV: name, module, keyword, start, end, nlines, proof_start (line of the first ':=' / 'by' / '|' after
the statement, heuristic).  Anonymous instances and `example`s get the name '-' (they are still counted).
Used to map export-level findings (duplicate classes, dead haves) back to source text.  Untrusted analysis only."""
import os, re, sys, argparse
from multiprocessing import Pool

KW = r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|example|irreducible_def|alias|noncomputable def|class inductive)'
MODS = r'((?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
DECL = re.compile(r'^' + MODS + KW + r'\b\s*(\S*)')
NS = re.compile(r'^namespace\s+(\S+)')
SEC = re.compile(r'^(?:noncomputable\s+)?section\b\s*(\S*)')
END = re.compile(r'^end\b\s*(\S*)')

def outline(path, module):
    try:
        lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
    except OSError:
        return []
    stack = []   # entries: ('ns', [parts]) or ('sec', name)
    out = []
    pending = None  # start line of doc/attribute block preceding a declaration
    cur = None
    in_block_comment = 0
    def ns_prefix():
        p = []
        for k, v in stack:
            if k == 'ns':
                p.extend(v)
        return p
    def close(endline):
        nonlocal cur
        if cur is not None:
            # trim trailing blank lines
            e = endline
            while e > cur['start'] and not lines[e - 1].strip():
                e -= 1
            cur['end'] = e
            out.append(cur)
            cur = None
    for i, raw in enumerate(lines, 1):
        line = raw
        s = line.strip()
        if in_block_comment:
            in_block_comment += line.count('/-') - line.count('-/')
            if in_block_comment < 0:
                in_block_comment = 0
            continue
        if not line or line[0] in ' \t':
            continue
        # column-0 command
        if line.startswith('/-'):
            depth = line.count('/-') - line.count('-/')
            close(i - 1)
            if pending is None:
                pending = i
            if depth > 0:
                in_block_comment = depth
            continue
        if line.startswith('--'):
            continue
        if line.startswith('@['):
            close(i - 1)
            if pending is None:
                pending = i
            # attribute may be followed by the declaration on the same line
            rest = re.sub(r'^@\[[^\]]*\]\s*', '', line)
            if not DECL.match(rest):
                continue
            line = rest
        m = DECL.match(line)
        if m:
            close(i - 1)
            kw = m.group(2)
            nm = m.group(3)
            start = pending if pending is not None else i
            pending = None
            mods = m.group(0)
            if kw in ('instance', 'example') or not nm or nm.startswith((':', '(', '[', '{', '⦃')):
                full = '-'
            else:
                nm = nm.rstrip(':')
                if nm.startswith('_root_.'):
                    parts = nm[len('_root_.'):].split('.')
                else:
                    parts = ns_prefix() + nm.split('.')
                full = '.'.join(parts)
                if re.search(r'\bprivate\b', mods):
                    full = '_private.%s.0.%s' % (module, full)
            cur = {'name': full, 'kw': kw, 'start': start, 'decl': i}
            continue
        pending = None
        close(i - 1)
        m = NS.match(line)
        if m:
            stack.append(('ns', m.group(1).split('.')))
            continue
        m = SEC.match(line)
        if m and not line.startswith('section_'):
            stack.append(('sec', m.group(1)))
            continue
        m = END.match(line)
        if m:
            nm = m.group(1)
            if stack:
                if nm and stack[-1][0] == 'ns':
                    # `end A.B` closes namespace A.B (possibly opened as one entry)
                    stack.pop()
                else:
                    stack.pop()
            continue
    close(len(lines))
    res = []
    for d in out:
        # proof start: first line from decl line on containing ':=' or ending in ' by' / starting with '|'
        ps = d['decl']
        for j in range(d['decl'], d['end'] + 1):
            t = lines[j - 1]
            if ':=' in t or re.search(r'\bby\s*$', t) or t.lstrip().startswith('| '):
                ps = j
                break
        res.append((d['name'], module, d['kw'], d['start'], d['end'], d['end'] - d['start'] + 1, ps))
    return res

def work(arg):
    root, rel = arg
    module = rel[:-5].replace('/', '.')
    return outline(os.path.join(root, rel), module)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('root')
    ap.add_argument('out')
    ap.add_argument('--modules', help='file with module names (one per line) to restrict to')
    ap.add_argument('--jobs', type=int, default=16)
    a = ap.parse_args()
    rels = []
    if a.modules:
        for m in open(a.modules):
            m = m.strip().split('\t')[0]
            if m:
                rels.append(m.replace('.', '/') + '.lean')
    else:
        for dp, dn, fn in os.walk(a.root):
            dn[:] = [d for d in dn if not d.startswith('.')]
            for f in fn:
                if f.endswith('.lean'):
                    rels.append(os.path.relpath(os.path.join(dp, f), a.root))
    rels.sort()
    n = 0
    with Pool(a.jobs) as p, open(a.out, 'w') as o:
        o.write('name\tmodule\tkw\tstart\tend\tnlines\tproof_start\n')
        for res in p.imap(work, [(a.root, r) for r in rels], chunksize=64):
            for r in res:
                o.write('\t'.join(map(str, r)) + '\n')
                n += 1
    print('files %d decls %d' % (len(rels), n), file=sys.stderr)

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""mk_index.py : regenerate fastverify/tests/INDEX.md, the regression test index.

Generated rows, one per finding test directory NNN-* (reported defect NNN): kind, heavy tag and finding title from the
test.sh header, case counts from EXPECT / CASES / ECASES, the per-test result summary of the most recent full (or heavy)
run in tests/results/, and of the latest run against the original deployed fast flow (*-deployed.tsv).
Carried over from the existing INDEX.md: the severity column, every other row (gNN / cNN / bNN tests and the suites, whose
descriptions and results are maintained by hand) verbatim and in place, and a result cell when tests/results/ has no run
that contains that test. A test directory NNN-* / gNN-* / cNN-* / bNN-* without a row gets a new row from its header."""
import collections, glob, os, re

T = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
INDEX = os.path.join(T, 'INDEX.md')
GEN_ID = re.compile(r'^[0-9]{3}$')
TEAM_RE = re.compile(r',?\s*TEAM [A-Z]\b(\s+[A-Z][0-9]{2}\b)?')
HEADER = ('| id | kind | severity | finding | cases | package (latest full run) | deployed fast flow |\n'
          '|---|---|---|---|---|---|---|\n')


def cells(line):   # generated rows never contain a literal '|' (it is written as '/')
    return [c.strip() for c in line.strip()[1:-1].split('|')]


# existing index: row order, raw lines, cells
old_order, old_line, old_cells = [], {}, {}
if os.path.exists(INDEX):
    in_table = False
    for ln in open(INDEX, encoding='utf-8'):
        if ln.startswith('| id |'):
            in_table = True; continue
        if in_table and ln.startswith('|---'):
            continue
        if in_table and ln.startswith('| '):
            c = cells(ln)
            if c[0] not in old_line:
                old_order.append(c[0]); old_line[c[0]] = ln if ln.endswith('\n') else ln + '\n'; old_cells[c[0]] = c
        elif in_table:
            in_table = False

# latest results per id: for each test, the most recent 'full' or 'heavy' run that contains it
res = collections.defaultdict(collections.Counter); rsrc = {}
rs = sorted(glob.glob(os.path.join(T, 'results', '*.tsv')), key=os.path.getmtime)
for rf in [r for r in rs if 'full' in os.path.basename(r) or 'heavy' in os.path.basename(r)]:   # oldest first
    per = collections.defaultdict(collections.Counter)
    for ln in open(rf):
        f = ln.rstrip('\n').split('\t')
        if len(f) >= 7 and f[0] != 'id':
            per[f[0]][f[6]] += 1
    for k, v in per.items():
        res[k] = v; rsrc[k] = os.path.basename(rf)[:-4]
fulls = [r for r in rs if 'full' in os.path.basename(r)]
rfile = fulls[-1] if fulls else None
dep = collections.defaultdict(collections.Counter); dfile = None
deps = [r for r in rs if r.endswith('-deployed.tsv')]
if deps:
    dfile = deps[-1]
    for ln in open(dfile):
        f = ln.rstrip('\n').split('\t')
        if len(f) >= 7 and f[0] != 'id':
            dep[f[0]][f[6]] += 1


def old(i, k):
    c = old_cells.get(i)
    return c[k] if c and len(c) > k else ''


gen = {}
dirs = [d for pat in ('[0-9][0-9][0-9]-*', 'g[0-9][0-9]-*', 'c[0-9][0-9]-*', 'b[0-9][0-9]-*')
        for d in sorted(glob.glob(os.path.join(T, pat))) if os.path.isdir(d)]
for d in dirs:
    i = os.path.basename(d)[:3]; ts = os.path.join(d, 'test.sh')
    if not os.path.exists(ts):
        gen[i] = (i, '-', '-', 'NO TEST', '', '', ''); continue
    head = open(ts).read()
    kind = re.search(r'\(kind ([^:)]+)', head); kind = TEAM_RE.sub('', kind.group(1)).strip() if kind else '?'
    heavy = '# heavy' in head
    title = re.search(r'^# finding: \w{3} (.*)$', head, re.M)
    if title:
        title = title.group(1)[:95]
    else:   # gNN / cNN / bNN: the description after "(kind ...): " in the header comment, continuation lines joined
        m = re.search(r'^# test [^\n]*?\(kind [^)]*\):\s*(.*(?:\n#   .*)*)', head, re.M)
        title = ' '.join(l.lstrip('#').strip() for l in m.group(1).splitlines())[:95] if m else ''
    n = []
    if os.path.exists(os.path.join(d, 'EXPECT')):
        n.append(f"{sum(1 for l in open(os.path.join(d, 'EXPECT')) if l.strip() and not l.startswith('#'))} e2e")
    for f, k in (('CASES', 'export-level'), ('ECASES', 'exporter')):
        p = os.path.join(d, f)
        if os.path.exists(p):
            n.append(f"{sum(1 for l in open(p) if l.strip() and not l.lstrip().startswith('#'))} {k}")
    r = res.get(i)
    rr = (' '.join(f'{v} {k}' for k, v in sorted(r.items())) + (f' ({rsrc[i]})' if 'heavy' in rsrc.get(i, '') else '')) \
        if r else old(i, 5)
    dd = dep.get(i); dr = ' '.join(f'{v} {k}' for k, v in sorted(dd.items())) if dd else old(i, 6)
    gen[i] = (i, kind + (' (heavy)' if heavy else ''), old(i, 2), title, ', '.join(n), rr, dr)


def row(r):
    line = '| ' + ' | '.join(x.replace('|', '/').strip() for x in r) + ' |'
    while '|  |' in line:   # empty cell -> '| |'
        line = line.replace('|  |', '| |')
    return line + '\n'


# keep the existing order: finding rows are recomputed in place (dropped if the test directory is gone), every other row is
# kept verbatim; a new finding test goes after the last finding row, a new gNN / cNN / bNN test after the last such row
GCB_ID = re.compile(r'^[gcb][0-9]{2}$')
out = []; last = {'nnn': -1, 'gcb': -1}
for i in old_order:
    if GEN_ID.match(i):
        if i in gen:
            out.append(row(gen[i])); last['nnn'] = len(out) - 1
        continue
    out.append(old_line[i])
    if GCB_ID.match(i):
        last['gcb'] = len(out) - 1
new_gcb = [row(gen[i]) for i in gen if i not in old_line and GCB_ID.match(i)]
new_nnn = [row(gen[i]) for i in gen if i not in old_line and GEN_ID.match(i)]
g = last['gcb'] if last['gcb'] >= 0 else len(out) - 1
out[g + 1:g + 1] = new_gcb
if last['gcb'] > last['nnn'] or last['gcb'] < 0:
    out[last['nnn'] + 1:last['nnn'] + 1] = new_nnn
else:
    out[last['nnn'] + 1 + len(new_gcb):last['nnn'] + 1 + len(new_gcb)] = new_nnn

with open(INDEX, 'w', encoding='utf-8') as o:
    o.write('# Regression test index\n\n'
            'One test per reported defect plus generality, component, soundness and daily-use suites (base table generated by\n'
            '`tests/tools/mk_index.py`). See [README.md](README.md).\n\n')
    o.write(f'Latest full run summarised: `{os.path.relpath(rfile, T) if rfile else "none yet"}` (heavy tests: their latest heavy '
            'run, named in the cell); last column = the same e2e tests run against the ORIGINAL (deployed) fast flow that the '
            f'defects were found in: `{os.path.relpath(dfile, T) if dfile else "none"}` (sensitivity: the test fails on that '
            'flow). Kinds: e2e = the defect\'s reproduction with bin/fastverify as the fast flow vs the official flow; '
            'export-level = every fast checker + bin/fastverify --export vs the live official lake comparator; exporter = '
            'export/export.sh vs official lean4export on the same .olean files; component = a component test script '
            '(PASS/FAIL lines). See README.md.\n\n')
    o.write(HEADER)
    o.writelines(out)
nnew = len(new_gcb) + len(new_nnn); ngen = sum(1 for i in gen if GEN_ID.match(i) and i in old_line)
print(f'INDEX.md: {len(out)} rows ({ngen} finding rows regenerated, {nnew} new, {len(out) - ngen - nnew} carried over)')

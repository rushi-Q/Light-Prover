#!/usr/bin/env python3
"""dupplan.py SCAN_DIR CMP_DIR SRC_DIR IMPORTS_JSON OUTDIR

Duplicate-THEOREM consolidation plan for a Lean project.

Inputs: dupscan scan output (K lines: module, kind, name, nlev, normalized type hash, value hash, depth,
declRange lines, used constants, type-used constants), dupscan cmp output (Q lines: structural confirmation of
type equality inside each hash group), the source tree, the module import graph (tools/imports.py).

For every verified statement group it decides, member by member in a global topological order (module import
order, then source line):
  KEEP      the member stays as is (the first visible copy = the canonical one for later members);
  ALIAS     the member's proof is replaced by a reference to a KEPT member with the identical statement that is
            VISIBLE at the member's position (its module is imported, transitively, by the member's module, or it is
            earlier in the same module). Visibility implies acyclicity: every redirected edge still points to an
            earlier declaration of the same topological order. No import changes.
  SHARED    no kept member is visible, but the group's best proof uses only non-project constants (Mathlib/core):
            one copy goes into a new shared module (imports Mathlib only => no import cycle is possible) and every
            member becomes an alias of it (the member's module gains one import of the shared module).
  NONE      neither (statement or proof needs project constants and no visible copy exists).
Statement/proof split: first ':=' at bracket depth 0 of the declaration text (heuristic; `|`-style and `where`
bodies count as proof). Writes OUTDIR/plan.tsv and OUTDIR/plan-summary.json.
"""
import sys, os, glob, json, collections, re

SCAN, CMP, SRC, IMPJ, OUT = sys.argv[1:6]
IMPORT_MAX = int(sys.argv[6]) if len(sys.argv) > 6 else -1   # max new modules an IMPORT alias may add (-1: off)
COSTS = sys.argv[7] if len(sys.argv) > 7 else None          # per-module build costs {module: s} (.json.gz): cp-aware IMPORT targets
newmods = {}
wrapper = {}
os.makedirs(OUT, exist_ok=True)
TARGETS = ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
           "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]

# ---------------- load scan ----------------
ids = {}; names = []
def iid(s):
    i = ids.get(s)
    if i is None:
        i = len(names); ids[s] = i; names.append(s)
    return i
bsig = {}; owner = {}; kind = {}; nlev = {}; tyh = {}; vh = {}; rng = {}; uses = {}; tyuses = {}
for f in sorted(glob.glob(SCAN + '/c*.tsv')):
    for ln in open(f, encoding='utf-8', errors='replace'):
        p = ln.rstrip('\n').split('\t')
        if p[0] != 'K':
            continue
        c = iid(p[3])
        if c in owner and int(p[8]) == 0:
            continue  # realized duplicate (eq_N ...) declared in several modules: keep the first/user one
        owner[c] = p[1]; kind[c] = p[2]; nlev[c] = int(p[4]); tyh[c] = p[5]; vh[c] = p[6]
        rng[c] = (int(p[8]), int(p[9]))
        uses[c] = [iid(u) for u in p[10].split(' ')] if len(p) > 10 and p[10] else []
        tyuses[c] = [iid(u) for u in p[11].split(' ')] if len(p) > 11 and p[11] else []
        bsig[c] = p[12] if len(p) > 12 else ''
print('consts', len(owner), flush=True)

# closure of the targets (project constants)
closure = set(); st = [ids[t] for t in TARGETS if t in ids]
while st:
    c = st.pop()
    if c in closure or c not in owner:
        continue
    closure.add(c); st.extend(uses[c])
indeg = collections.Counter()
users = collections.defaultdict(list)
for c, us in uses.items():
    for u in us:
        indeg[u] += 1
        users[u].append(c)

# ---------------- verified groups ----------------
bad = set()
for f in glob.glob(CMP + '/out/c*.tsv'):
    for ln in open(f, encoding='utf-8', errors='replace'):
        p = ln.rstrip('\n').split('\t')
        if p[3] != '1':
            bad.add(p[2])
g = collections.defaultdict(list)
for c in owner:
    if kind[c] == 't' and rng[c][0] > 0 and names[c] not in bad:
        g[(nlev[c], tyh[c])].append(c)
groups = [v for v in g.values() if len(v) > 1]
print('groups', len(groups), 'members', sum(map(len, groups)), flush=True)

# ---------------- import graph: topological index + closure bitsets ----------------
imp = json.load(open(IMPJ))
mods = list(imp.keys())
order = []; state = {}
for m0 in mods:
    if m0 in state:
        continue
    stack = [(m0, iter(imp[m0]['imports']))]; state[m0] = 1
    while stack:
        m, it = stack[-1]
        nxt = None
        for d in it:
            if d in imp and d not in state:
                nxt = d; break
        if nxt is None:
            stack.pop(); state[m] = 2; order.append(m)
        else:
            state[nxt] = 1; stack.append((nxt, iter(imp[nxt]['imports'])))
topo = {m: i for i, m in enumerate(order)}
need = set(owner[c] for v in groups for c in v)
# closure bitsets only for modules on paths we query: compute for all (cheap enough)
bits = {}
for m in order:
    b = 1 << topo[m]
    for d in imp[m]['imports']:
        if d in bits:
            b |= bits[d]
    bits[m] = b
print('import closures computed', flush=True)
mfinish = mstart = None
if COSTS:
    import gzip
    cost = json.load(gzip.open(COSTS)); mfinish = {}; mstart = {}
    for m in order:
        mstart[m] = max((mfinish[d] for d in imp[m]['imports'] if d in mfinish), default=0.0)
        mfinish[m] = mstart[m] + cost.get(m, 1.0)
def visible(c, at):
    """is constant c visible at the position of constant `at`?"""
    mc, ma = owner[c], owner[at]
    if mc == ma:
        return rng[c][0] < rng[at][0]
    return (bits[ma] >> topo[mc]) & 1 == 1

# ---------------- source statement/proof split ----------------
srccache = {}
def srclines(mod):
    if mod not in srccache:
        if len(srccache) > 20000:
            srccache.clear()
        p = os.path.join(SRC, mod.replace('.', '/') + '.lean')
        try:
            srccache[mod] = open(p, encoding='utf-8', errors='replace').read().split('\n')
        except OSError:
            srccache[mod] = []
    return srccache[mod]
OPEN = {'(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄'}
CLOSE = set(OPEN.values())
def split(c):
    """returns (stmt_lines, proof_lines, assign_line_index_in_file or -1)"""
    l1, l2 = rng[c]
    L = srclines(owner[c])[l1 - 1:l2]
    depth = 0; incom = 0
    for i, line in enumerate(L):
        j = 0; n = len(line)
        while j < n:
            ch = line[j]
            if incom:
                if line.startswith('-/', j): incom -= 1; j += 2; continue
                if line.startswith('/-', j): incom += 1; j += 2; continue
                j += 1; continue
            if line.startswith('/-', j): incom += 1; j += 2; continue
            if line.startswith('--', j): break
            if ch in OPEN: depth += 1
            elif ch in CLOSE: depth = max(0, depth - 1)
            elif depth == 0 and line.startswith(':=', j):
                return i + 1, len(L) - i - 1, l1 - 1 + i
            elif depth == 0 and i > 0 and j == len(line) - len(line.lstrip()) and (line.lstrip().startswith('| ') or line.lstrip().startswith('where')):
                return i, len(L) - i, l1 - 1 + i
            j += 1
    return len(L), 0, -1

def project_only_mathlib(c):
    """True if neither statement nor proof uses a project constant (other than itself)."""
    return all((u not in owner) for u in uses[c])

def is_private(c):
    return names[c].startswith('_private.')

# ---------------- plan ----------------
S = collections.Counter()
rows = []
for gi, v in enumerate(groups):
    v.sort(key=lambda c: (topo[owner[c]], rng[c][0]))
    info = {c: split(c) for c in v}
    vset = set(v)
    kept = []
    # best proof for a shared copy: a member using only non-project constants, fewest proof lines
    shareable = [c for c in v if project_only_mathlib(c)]
    shared = min(shareable, key=lambda c: (info[c][1], info[c][0], names[c])) if shareable else None
    for c in v:
        vis = [k for k in kept if visible(k, c) and (not is_private(k) or owner[k] == owner[c])]
        sl, pl, _ = info[c]
        pubkept = [k for k in kept if not is_private(k)]
        if vis:
            tgt = min(vis, key=lambda k: (bsig[k] != bsig[c], info[k][1], names[k]))
            act = 'ALIAS'
        elif IMPORT_MAX >= 0 and pubkept and topo[owner[pubkept[0]]] < topo[owner[c]] \
                and (bits[owner[pubkept[0]]] & ~bits[owner[c]]).bit_count() <= IMPORT_MAX:
            # IMPORT: alias of a public kept copy of a topologically earlier module; the member's module gains
            # `import <its module>`; acyclic because every new edge goes down the original topological order.
            # With costs: prefer a copy whose module is finished before the member's module can start (no build delay),
            # then the same binder infos, then the fewest new modules; else the first (lowest) public copy.
            cands = [k for k in pubkept if topo[owner[k]] < topo[owner[c]]]
            tgt = cands[0]
            if mfinish is not None:
                ok = [k for k in cands if mfinish.get(owner[k], 0) <= mstart.get(owner[c], 0) + 1e-9]
                if ok:
                    tgt = min(ok, key=lambda k: (bsig[k] != bsig[c], (bits[owner[k]] & ~bits[owner[c]]).bit_count()))
            act = 'IMPORT'
            newmods[c] = (bits[owner[tgt]] & ~bits[owner[c]]).bit_count()
        elif shared is not None:
            tgt = shared; act = 'SHARED'
            kept.append(c)  # it stays a valid visible copy for later members too (as an alias of the shared one)
        else:
            tgt = None; act = 'KEEP'
            kept.append(c)
        rows.append((gi, act, c, tgt, sl, pl))
        wrapper[c] = int(any(u in vset for u in uses[c]))
    # if only one member would be SHARED and nobody else uses the shared copy, turning it into an alias saves nothing:
# second pass: groups where SHARED was chosen for exactly one member and all others ALIAS to it -> KEEP instead
byg = collections.defaultdict(list)
for r in rows:
    byg[r[0]].append(r)
final = []
for gi, rs in byg.items():
    nsh = sum(1 for r in rs if r[1] == 'SHARED')
    if nsh == 1:
        rs = [(r[0], 'KEEP', r[2], None, r[4], r[5]) if r[1] == 'SHARED' else r for r in rs]
    final.extend(rs)

with open(OUT + '/plan.tsv', 'w') as fh:
    fh.write('group\taction\tname\tmodule\ttarget\ttarget_module\tstmt_lines\tproof_lines\tin_closure\tindegree\tprivate\tline1\tline2\twrapper\tnewmods\tbinfo_eq\n')
    for gi, act, c, tgt, sl, pl in final:
        fh.write(f"{gi}\t{act}\t{names[c]}\t{owner[c]}\t{names[tgt] if tgt is not None else ''}\t"
                 f"{owner[tgt] if tgt is not None else ''}\t{sl}\t{pl}\t{int(c in closure)}\t{indeg[c]}\t{int(is_private(c))}\t{rng[c][0]}\t{rng[c][1]}\t{wrapper[c]}\t{newmods.get(c, -1)}\t{int(tgt is not None and bsig[c] == bsig[tgt])}\n")
        S['members'] += 1
        S['wrapper_' + act] += wrapper[c]
        if tgt is not None:
            S['binfo_eq_' + act] += int(bsig[c] == bsig[tgt])
        S['wrapper_lines_' + act] += (sl + pl) * wrapper[c]
        if act == 'IMPORT':
            nm = newmods[c]
            S['import_newmods_le1' if nm <= 1 else 'import_newmods_le10' if nm <= 10 else 'import_newmods_le100' if nm <= 100 else 'import_newmods_le1000' if nm <= 1000 else 'import_newmods_gt1000'] += 1
            S['import_newmods_lines_' + ('le10' if nm <= 10 else 'le100' if nm <= 100 else 'le1000' if nm <= 1000 else 'gt1000')] += pl
        S['act_' + act] += 1
        S['lines_' + act] += sl + pl
        S['proof_lines_' + act] += pl
        if c in closure:
            S['inclosure_act_' + act] += 1
        if act in ('ALIAS', 'SHARED'):
            S['indeg_' + act] += indeg[c]
            S['zero_indeg_' + act] += (indeg[c] == 0)
            S['private_' + act] += is_private(c)
            # alias saving: proof lines replaced by one reference line (proof on the ':=' line)
            S['save_alias_lines_' + act] += pl
            # delete+redirect saving: all lines (statement + proof)
            S['save_delete_lines_' + act] += sl + pl
nsharedgroups = len(set(r[0] for r in final if r[1] == 'SHARED'))
S['shared_groups'] = nsharedgroups
S['groups'] = len(groups)
json.dump(S, open(OUT + '/plan-summary.json', 'w'), indent=1, sort_keys=True)
print(json.dumps(S, indent=1, sort_keys=True))

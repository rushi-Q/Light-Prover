#!/usr/bin/env python3
"""topic_coalesce.py — Intra-directory sibling leaf coalescing for Lean 4 repositories
(Stage-3 LAYOUT.topic).

Mathematical cycle- & DFS-safety invariant:
  Modules M_1, ..., M_r are eligible to coalesce into M_r ONLY when they:
    1. Live in the exact same directory (`dir_prefix(M_i) == dir_prefix(M_j)`), preserving 100% topic purity;
    2. Have identical library options (`lib_base`) and are plain non-root, non-denied, non-`module`-system files;
    3. Have the EXACT SAME ordered import list `tuple(imports(M_i)) == S` (so no M_i can reach another M_j in the DAG,
       coalescing into M_r cannot introduce any cycle, and every importer U keeps the exact same transitive import set
       and first-discovery DFS post-order when replacing the first occurrence in {M_1..M_r} by M_r and dropping duplicates);
    4. Have balanced scopes, disjoint `private` declaration identifiers (preventing private-clash build failures at L0),
       per-file lines <= `--max-lines` (default 40), group lines <= `--max-group-lines` (default 240), and summed
       build cost <= `--max-cost` (default 30.0s from `--costs`, e.g. `rh-build-costs.json.gz`).
"""
from __future__ import annotations
import argparse, collections, gzip, json, os, re, shutil, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import normalize as NZ
import chainmerge as CM

DECL_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?((?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*)'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|alias|irreducible_def)\s+([^\s:({\[⦃]+)',
    re.M,
)
SIDE_EFFECT_RE = re.compile(
    r'(?:@\[[^\]]*\bsimp\b|\battribute\s*\[|^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*instance\b'
    r'|^\s*(?:scoped\s+|local\s+)?(?:notation|infix[lr]?|prefix|postfix|macro|macro_rules|elab|elab_rules|syntax)\b)',
    re.M,
)
IMP_LINE_RE = re.compile(r'^(\s*import\s+)([^\s]+)(.*)$')


def decl_short_names(lines: list[str]) -> tuple[set[str], set[str], bool]:
    """Return (all_short_names, private_short_names, has_global_side_effect)."""
    txt = '\n'.join(lines)
    all_n: set[str] = set()
    priv_n: set[str] = set()
    for m in DECL_RE.finditer(txt):
        sn = m.group(2).split('.')[-1]
        all_n.add(sn)
        if 'private' in m.group(1):
            priv_n.add(sn)
    has_se = bool(SIDE_EFFECT_RE.search(txt))
    return all_n, priv_n, has_se


def rewrite_importer_header(lines: list[str], hdr_items: list[tuple[int, str, str]], redirect: dict[str, str]) -> tuple[list[str], int]:
    """Rewrite `import X` -> `import redirect[X]` in header lines, deduplicating while keeping first-seen order."""
    if not hdr_items:
        return lines, 0
    idx_set = {idx for idx, _, _ in hdr_items}
    seen: set[tuple[str, str]] = set()
    changed = 0
    out: list[str] = []
    for idx, ln in enumerate(lines):
        if idx not in idx_set:
            out.append(ln)
            continue
        m = IMP_LINE_RE.match(ln)
        if not m:
            out.append(ln)
            continue
        prefix, target, suffix = m.group(1), m.group(2), m.group(3)
        new_target = redirect.get(target, target)
        if new_target != target:
            changed += 1
        key = (prefix.strip(), new_target)
        if key in seen:
            changed += 1
            continue
        seen.add(key)
        out.append(f'{prefix}{new_target}{suffix}')
    return out, changed


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('project')
    ap.add_argument('out')
    ap.add_argument('--srcdir', default='src')
    ap.add_argument('--packages', default=None)
    ap.add_argument('--toolchain-src', default=None)
    ap.add_argument('--deny', default=None)
    ap.add_argument('--costs', default=None, help='JSON or .json.gz {module: seconds} build-cost hints')
    ap.add_argument('--max-cost', type=float, default=30.0, help='Max summed build cost (s) per coalesced module')
    ap.add_argument('--default-cost', type=float, default=2.5)
    ap.add_argument('--max-lines', type=int, default=40, help='Max lines of each candidate leaf file')
    ap.add_argument('--max-group-lines', type=int, default=240, help='Max combined lines per coalesced output file')
    ap.add_argument('--max-group', type=int, default=8, help='Max files coalesced into one output file')
    ap.add_argument('--same-importers', action='store_true',
                    help='G1* mode: only coalesce siblings imported by the exact same non-empty set of modules')
    ap.add_argument('--allow-side-effects', action='store_true',
                    help='Allow instance/@[simp]/notation files in non---same-importers mode')
    ap.add_argument('--plan-only', action='store_true')
    a = ap.parse_args()

    costs = CM.load_costs(a.costs)
    src = NZ.resolve_srcdir(a.project, a.srcdir)
    files: dict[str, str] = {}
    for root, dirs, fs in os.walk(src):
        dirs[:] = [d for d in dirs if d not in ('.lake', '.git')]
        for fn in fs:
            if fn.endswith('.lean'):
                p = os.path.join(root, fn)
                files[os.path.relpath(p, src)[:-5].replace('/', '.')] = p

    texts = {m: open(p, encoding='utf-8').read().split('\n') for m, p in files.items()}
    hdr = {}
    unsupported: set[str] = set()
    importers_of: dict[str, list[str]] = collections.defaultdict(list)
    for m, lines in texts.items():
        h = NZ.parse_header_ext(lines)
        if h is None:
            unsupported.add(m)
        else:
            hdr[m] = h
            for _, _, c in h[1]:
                if c in files:
                    importers_of[c].append(m)

    base, libs = NZ.lake_options(a.project)
    lakeroots: set[str] = set()
    lf = os.path.join(a.project, 'lakefile.toml')
    if os.path.exists(lf):
        t = open(lf, encoding='utf-8').read()
        for blk in re.split(r'(?m)^(?=\[\[)', t):
            if blk.startswith('[[lean_lib]]') or blk.startswith('[[lean_exe]]'):
                nm = re.search(r'^name\s*=\s*"([^"]*)"', blk, re.M)
                rts = re.search(r'^roots\s*=\s*\[(.*?)\]', blk, re.M | re.S)
                if rts:
                    lakeroots |= set(NZ._toml_list(rts.group(1)))
                elif nm:
                    lakeroots.add(nm.group(1))

    deny = (set(open(a.deny, encoding='utf-8').read().split()) if a.deny else set()) | unsupported
    why = collections.Counter()
    buckets: dict[tuple, list[str]] = collections.defaultdict(list)
    parsed_body: dict[str, tuple[int, list[str], list[str], set[str], set[str]]] = {}

    for m in sorted(hdr):
        if m in lakeroots or m in deny:
            why['root/deny'] += 1
            continue
        is_m, items = hdr[m]
        if is_m:
            why['module-system file'] += 1
            continue
        if any(vis != 'plain' for _, vis, _ in items):
            why['special import'] += 1
            continue
        lines = texts[m]
        if len(lines) > a.max_lines:
            why['>max_lines'] += 1
            continue
        mc = costs.get(m, a.default_cost)
        if a.max_cost is not None and mc > a.max_cost:
            why['>max_cost_single'] += 1
            continue
        imps_in = tuple(sorted(set(importers_of.get(m, ()))))
        if a.same_importers and not imps_in:
            why['no_importers'] += 1
            continue
        hl = CM.hdr_last_idx(lines, is_m, items)
        body, stack = CM.body_and_scopes(lines, hl)
        cl = CM.closing(stack) if stack is not None else None
        if cl is None:
            why['unbalanced scopes'] += 1
            continue
        all_names, pnames, has_se = decl_short_names(body)
        if not a.same_importers and not a.allow_side_effects and has_se:
            why['side_effect_decl (instance/simp/notation)'] += 1
            continue
        parsed_body[m] = (hl, body, cl, all_names, pnames)
        dir_prefix = m.rsplit('.', 1)[0] if '.' in m else ''
        imp_tuple = tuple(c for _, _, c in items)
        lib_key = tuple(sorted(NZ.lib_base(m, base, libs).items()))
        bkey = (dir_prefix, lib_key, imp_tuple, imps_in) if a.same_importers else (dir_prefix, lib_key, imp_tuple)
        buckets[bkey].append(m)

    coalesced: dict[str, tuple[list[str], list[str]]] = {}
    redirect: dict[str, str] = {}
    priv_skips = 0

    for _, members in sorted(buckets.items()):
        if len(members) < 2:
            continue
        batches: list[list[str]] = []
        cur: list[str] = []
        cur_lines = 0
        cur_cost = 0.0
        cur_all: set[str] = set()
        cur_privs: set[str] = set()
        for m in members:
            mlines = len(texts[m])
            mcost = costs.get(m, a.default_cost)
            mall, mprivs = parsed_body[m][3], parsed_body[m][4]
            if a.same_importers:
                clash = bool((cur_privs & mall) or (cur_all & mprivs))
            else:
                clash = bool(cur_all & mall)
            if clash:
                priv_skips += 1
            over_group = len(cur) >= a.max_group
            over_lines = cur and (cur_lines + mlines > a.max_group_lines)
            over_cost = cur and (a.max_cost is not None and cur_cost + mcost > a.max_cost)
            if cur and (clash or over_group or over_lines or over_cost):
                if len(cur) >= 2:
                    batches.append(cur)
                cur = [m]
                cur_lines = mlines
                cur_cost = mcost
                cur_all = set(mall)
                cur_privs = set(mprivs)
            else:
                cur.append(m)
                cur_lines += mlines
                cur_cost += mcost
                cur_all |= mall
                cur_privs |= mprivs
        if len(cur) >= 2:
            batches.append(cur)

        for grp in batches:
            keeper = grp[-1]
            hl0 = parsed_body[grp[0]][0]
            out_lines = list(texts[grp[0]][:hl0 + 1]) if hl0 >= 0 else []
            for x in grp[:-1]:
                _, body_x, cl_x, _, _ = parsed_body[x]
                bx = list(body_x)
                while bx and bx[-1] == '':
                    bx.pop()
                out_lines.append(f'-- (coalesced) module {x}')
                out_lines.append('section')
                out_lines.extend(bx)
                out_lines.extend(cl_x)
                out_lines.append('end')
                redirect[x] = keeper
            hlk = parsed_body[keeper][0]
            out_lines.extend(texts[keeper][hlk + 1:])
            coalesced[keeper] = (grp, out_lines)

    importers_rewritten = 0
    import_edits = 0
    rewritten_texts: dict[str, list[str]] = {}
    if redirect:
        for m, lines in texts.items():
            if m in redirect or m not in hdr:
                continue
            base_lines = coalesced[m][1] if m in coalesced else lines
            h = NZ.parse_header_ext(base_lines)
            if h is None:
                continue
            new_lines, nchg = rewrite_importer_header(base_lines, h[1], redirect)
            if nchg > 0:
                importers_rewritten += 1
                import_edits += nchg
                if m in coalesced:
                    coalesced[m] = (coalesced[m][0], new_lines)
                else:
                    rewritten_texts[m] = new_lines

    summary = {
        'modules_before': len(texts),
        'groups_coalesced': len(coalesced),
        'members_removed': len(redirect),
        'modules_after': len(texts) - len(redirect),
        'importers_rewritten': importers_rewritten,
        'import_header_edits': import_edits,
        'private_clash_splits': priv_skips,
        'skipped_reasons': dict(why),
    }

    if not a.plan_only:
        if os.path.exists(a.out):
            sys.exit(f'topic_coalesce: {a.out} exists')
        shutil.copytree(a.project, a.out, symlinks=True, ignore=shutil.ignore_patterns('.lake', '.git'))
        osrc = NZ.resolve_srcdir(a.out, a.srcdir)
        for x in redirect:
            os.unlink(os.path.join(osrc, x.replace('.', '/') + '.lean'))
        for keeper, (_, out_lines) in coalesced.items():
            with open(os.path.join(osrc, keeper.replace('.', '/') + '.lean'), 'w', encoding='utf-8') as f:
                f.write('\n'.join(out_lines))
        for m, new_lines in rewritten_texts.items():
            with open(os.path.join(osrc, m.replace('.', '/') + '.lean'), 'w', encoding='utf-8') as f:
                f.write('\n'.join(new_lines))
        with open(os.path.join(a.out, '.topic_coalesce.tsv'), 'w', encoding='utf-8') as f:
            for x, k in sorted(redirect.items()):
                f.write(f'{x}\t{k}\n')
        for root_d, _, _ in os.walk(osrc, topdown=False):
            if not os.listdir(root_d) and root_d != osrc:
                os.rmdir(root_d)

    print(json.dumps(summary))


if __name__ == '__main__':
    main()

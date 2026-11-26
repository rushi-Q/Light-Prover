#!/usr/bin/env python3
"""defdedup_edits.py DEFPLAN_TSV SRC OUT_EDITS_TSV [options]

Emits team-format edit lists (apply_edits.py) from defdedup_plan.py in three measurable G2 modes:
  * abbrev   : replace duplicate def/abbrev with `[noncomputable] abbrev <short> := @_root_.<target>`
  * def      : replace duplicate def/abbrev with `[noncomputable] def <short> := @_root_.<target>`
  * matchkw  : match the original keyword (`abbrev` for abbrev, `def` for def)
  * redirect : delete the duplicate declaration (including contiguous preceding `... in` modifier lines)
               and emit `subst` (full name -> _root_.<target>, plus same-module short-name rewrite when
               unambiguous); skips declarations used via dot notation or without safe textual rewriting.
"""
import argparse, collections, json, os, re, sys

MODIFIER_IN_RE = re.compile(r'^\s*(?:set_option|attribute|variable|open|omit|include)\b.*\bin\s*(?:--.*)?$')
CONT_LINE_RE = re.compile(r'^\s+(?:\[|\{|\(|_)')


def strip_priv(name):
    if name.startswith('_private.'):
        i = name.find('.0.')
        if i > 0:
            return name[i + 3:]
    return name


def decl_head_name(lines, s, e):
    """Extract the exact identifier token written after def/abbrev in the source declaration."""
    head = '\n'.join(lines[max(0, s - 1):min(len(lines), e)])
    m = re.search(r'\b(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*(?:def|abbrev)\s+([^\s:({\[⦃]+)', head)
    return m.group(1) if m else None


def find_modifier_start(lines, s):
    """Walk backwards from 1-based start line s to include all contiguous `... in` modifier lines
    (fixes the dangling multi-line `attribute/variable ... in` bug found in P03's edits-c1r!)."""
    i = s - 1  # 0-based index of decl line
    while i > 0:
        j = i - 1
        while j >= 0 and lines[j].strip() == '':
            j -= 1
        if j < 0:
            break
        # Check if line j ends with `in` (or `in -- ...`)
        if re.search(r'(?:^|\s)in\s*(?:--.*)?$', lines[j]):
            # Walk back over multi-line continuation of this modifier command
            k = j
            while k > 0 and not re.match(r'^\s*(?:set_option|attribute|variable|open|omit|include)\b', lines[k]):
                if lines[k].strip() == '' or re.match(r'^\s*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|namespace|section|end|import)\b', lines[k]):
                    k = j + 1  # abort: wasn't a modifier command
                    break
                k -= 1
            if k <= j and re.match(r'^\s*(?:set_option|attribute|variable|open|omit|include)\b', lines[k]):
                i = k
                continue
        break
    return i + 1  # 1-based


def first_non_import_line(lines):
    last_imp = 0
    for i, l in enumerate(lines, 1):
        s = l.strip()
        if s.startswith('import '):
            last_imp = i
        elif s == '' or s.startswith('--'):
            continue
        else:
            break
    return last_imp + 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('plan', help='defplan.tsv from defdedup_plan.py')
    ap.add_argument('src', help='project source directory')
    ap.add_argument('out', help='output edits TSV (team format)')
    ap.add_argument('--mode', choices=('abbrev', 'def', 'matchkw', 'redirect', 'hybrid'), default='hybrid')
    ap.add_argument('--actions', default='VISIBLE,IMPORT_CP', help='comma-separated actions to include')
    ap.add_argument('--owner', default='D19-defdedup')
    ap.add_argument('--only-kw', default='', help='optional filter: def or abbrev')
    ap.add_argument('--protect-from', required=True, help='comparator.json (REQUIRED)')
    ap.add_argument('--stats', default=None)
    a = ap.parse_args()

    cfg = json.load(open(a.protect_from))
    prot = set(cfg.get('theorem_names', [])) | set(cfg.get('definition_names', []))
    acts = set(x for x in a.actions.split(',') if x)

    # Load plan
    rows = []
    with open(a.plan, encoding='utf-8') as f:
        hdr = f.readline().rstrip('\n').split('\t')
        ix = {k: i for i, k in enumerate(hdr)}
        for l in f:
            p = l.rstrip('\n').split('\t')
            if p[ix['action']] not in acts:
                continue
            if a.only_kw and p[ix['kw']] != a.only_kw:
                continue
            if p[ix['name']] in prot:
                continue
            rows.append({k: p[i] for k, i in ix.items()})

    file_cache = {}
    def get_lines(mod):
        if mod not in file_cache:
            if len(file_cache) > 4000:
                file_cache.clear()
            fp = os.path.join(a.src, mod.replace('.', '/') + '.lean')
            file_cache[mod] = open(fp, encoding='utf-8', errors='replace').read().split('\n') if os.path.exists(fp) else []
        return file_cache[mod]

    edits = []
    added_imports = collections.defaultdict(set)
    stats = collections.Counter()
    by_mod = collections.defaultdict(list)
    for r in rows:
        by_mod[r['module']].append(r)

    for mod, mrows in sorted(by_mod.items()):
        lines = get_lines(mod)
        if not lines:
            stats['missing_file'] += len(mrows); continue
        existing_imps = set(l.split()[1] for l in lines if l.startswith('import ') and len(l.split()) >= 2)
        ins_line = first_non_import_line(lines)
        full_text = '\n'.join(lines)
        used_ranges = []

        for r in sorted(mrows, key=lambda x: int(x['start'])):
            s, e = int(r['start']), int(r['end'])
            if any(not (e < x or y < s) for x, y in used_ranges):
                stats['overlap_skip'] += 1; continue
            head_tok = decl_head_name(lines, s, e)
            if not head_tok:
                stats['no_head_name'] += 1; continue
            # Detect private/protected/noncomputable prefixes on the decl line itself
            decl_hdr = '\n'.join(lines[s - 1:e]).split(':=')[0]
            if 'where' in decl_hdr or 'match ' in decl_hdr:
                stats['skip_pattern_def'] += 1; continue
            priv_pfx = 'private ' if r['is_priv'] == '1' or re.search(r'\bprivate\s+', decl_hdr) else ''
            prot_pfx = 'protected ' if re.search(r'\bprotected\s+', decl_hdr) else ''
            nc_pfx = 'noncomputable ' if re.search(r'\bnoncomputable\s+', decl_hdr) else ''
            tgt = r['target']
            tmod = r['target_mod']
            orig_kw = r['kw']

            use_alias = (a.mode in ('abbrev', 'def', 'matchkw')) or (a.mode == 'hybrid' and orig_kw == 'abbrev')
            if use_alias:
                kw = orig_kw if a.mode in ('matchkw', 'hybrid') else a.mode
                new_line = f'{priv_pfx}{prot_pfx}{nc_pfx}{kw} {head_tok} := @_root_.{tgt}'
                edits.append((mod, s, e, 'replace', a.owner, new_line))
                used_ranges.append((s, e))
                stats['emitted'] += 1
                stats['lines_saved'] += (e - s + 1) - 1
            else:
                # redirect mode (delete decl + rewrite full name and unqualified short name in this module)
                un = strip_priv(r['name'])
                short = un.rsplit('.', 1)[-1]
                # Check for dot notation `.short` in this module (high-risk G2!)
                if re.search(r'(?<!_root_)\.' + re.escape(short) + r'\b', full_text):
                    stats['redirect_skip_dot'] += 1; continue
                s_mod = find_modifier_start(lines, s)
                edits.append((mod, s_mod, e, 'delete', a.owner, ''))
                used_ranges.append((s_mod, e))
                # Rewrite full name and unqualified short name in this module (apply_edits subst format: "OLD NEW")
                edits.append((mod, 0, 0, 'subst', a.owner, f'{un} _root_.{tgt}'))
                if short != un:
                    edits.append((mod, 0, 0, 'subst', a.owner, f'{short} _root_.{tgt}'))
                stats['emitted'] += 1
                stats['lines_saved'] += (e - s_mod + 1)

            if r['action'].startswith('IMPORT') and tmod and tmod != mod and tmod not in existing_imps:
                added_imports[mod].add(tmod)

        if added_imports[mod]:
            imp_block = '\\n'.join(f'import {tmod}' for tmod in sorted(added_imports[mod]))
            edits.append((mod, ins_line, ins_line - 1, 'insert_before', a.owner, imp_block))
            stats['imports_added'] += len(added_imports[mod])

    with open(a.out, 'w', encoding='utf-8') as f:
        for mod, s, e, op, own, txt in edits:
            f.write(f'{mod}\t{s}\t{e}\t{op}\t{own}\t{txt}\n')
    stats['modules_touched'] = len(set(x[0] for x in edits))
    stats['mode'] = a.mode
    if a.stats:
        json.dump(dict(stats), open(a.stats, 'w'), indent=1, sort_keys=True)
    print(json.dumps(dict(stats), indent=1, sort_keys=True))


if __name__ == '__main__':
    main()

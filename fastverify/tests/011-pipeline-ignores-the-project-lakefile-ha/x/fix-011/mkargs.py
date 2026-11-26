#!/usr/bin/env python3
"""fix-011 PROTOTYPE: mkargs.py PROJ LOGDIR -> derive what `lake build` would do from the project's lakefile.toml (minimal
TOML subset parser; a real fix should use the Lake API in the sandbox and support lakefile.lean via `lake translate-config`):
 * per-module lean args = moreLeanArgs + -D<package leanOptions> + -D<lean_lib leanOptions> (+ weakLeanArgs) -> LOGDIR/args.json
 * module set = modules of the default-target libs (globs, or roots if no globs) + their local import closure restricted to
   modules that belong to SOME lean_lib (lake cannot resolve others) -> rewrites LOGDIR/deps.json
 * LOGDIR/requires.txt = number of [[require]] entries (pipeline drops the package cache from LEAN_PATH when 0)"""
import json, re, sys
PROJ, LOGD = sys.argv[1], sys.argv[2]

def parse_value(v):
    v = v.strip()
    if v.startswith('"'): return json.loads(v)
    if v in ('true', 'false'): return v == 'true'
    if v.startswith('['): return [parse_value(x) for x in re.findall(r'"(?:[^"\\]|\\.)*"|[^,\[\]\s]+', v[1:-1])]
    if v.startswith('{'):
        return {k.strip().strip('"'): parse_value(x) for k, x in re.findall(r'([\w."]+)\s*=\s*("(?:[^"\\]|\\.)*"|[^,}]+)', v[1:-1])}
    try: return int(v)
    except ValueError: return v

def parse_toml(text):
    root, cur = {}, None; cur = root
    for raw in text.splitlines():
        line = re.sub(r'\s+#.*$', '', raw).strip() if not raw.strip().startswith('#') else ''
        if not line: continue
        m = re.match(r'^\[\[([\w.]+)\]\]$', line)
        if m: cur = {}; root.setdefault(m.group(1), []).append(cur); continue
        m = re.match(r'^\[([\w.]+)\]$', line)
        if m:
            parts = m.group(1).split('.')
            base = root[parts[0]][-1] if isinstance(root.get(parts[0]), list) and len(parts) > 1 else root
            key = parts[-1] if base is not root else m.group(1)
            cur = base.setdefault(key, {}); continue
        k, _, v = line.partition('=')
        cur[k.strip().strip('"')] = parse_value(v)
    return root

def dflag(k, v): return f'-D{k}={str(v).lower() if isinstance(v, bool) else v}'

cfg = parse_toml(open(f'{PROJ}/lakefile.toml').read())
pkg_args = list(cfg.get('moreLeanArgs', [])) + [dflag(k, v) for k, v in cfg.get('leanOptions', {}).items()]
weak = list(cfg.get('weakLeanArgs', []))
libs = cfg.get('lean_lib', [])
def pats(lib): return lib.get('globs') or lib.get('roots') or [lib['name']]
def lib_of(m):
    for lib in libs:
        for p in pats(lib):
            if (p.endswith('.+') and m.startswith(p[:-2] + '.')) or (p.endswith('.*') and (m == p[:-2] or m.startswith(p[:-2] + '.'))) or m == p:
                return lib
    return None
deps = json.load(open(f'{LOGD}/deps.json'))
targets = set(cfg.get('defaultTargets') or [l['name'] for l in libs])
todo = [m for m in deps if lib_of(m) and lib_of(m)['name'] in targets]; keep = set(todo)
while todo:
    m = todo.pop()
    for d in deps[m][1]:
        if d not in keep and lib_of(d): keep.add(d); todo.append(d)
args = {m: pkg_args + [dflag(k, v) for k, v in lib_of(m).get('leanOptions', {}).items()] + weak for m in keep}
json.dump({m: [deps[m][0], [d for d in deps[m][1] if d in keep]] for m in keep}, open(f'{LOGD}/deps.json', 'w'))
json.dump(args, open(f'{LOGD}/args.json', 'w'), indent=0)
open(f'{LOGD}/requires.txt', 'w').write(f"{len(cfg.get('require', []))}\n")
print(f'mkargs: {len(keep)} of {len(deps)} modules in the lake target set; args e.g. {next(iter(args.values()), None)}; requires={len(cfg.get("require", []))}')

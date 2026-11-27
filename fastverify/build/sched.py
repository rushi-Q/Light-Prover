#!/usr/bin/env python3
"""fastverify direct build scheduler.

usage: python3 -I sched.py JOBS [--memfloor GB] [--cgroup DIR]... [--early-release] [--extra-arg ARG]... [--retry-exact] < PLAN.jsonl
       (stdout = log records; exit status = verdict). Without options = preset B1 (exact).
  --early-release  (B2, exact) a module's dependents start as soon as ALL its olean-family outputs exist (lean writes each
                   part atomically: tmp + rename); the build still needs every lean to exit 0, outputs are fingerprinted at
                   release, so a later change is detected (finding 041 = releasing on .olean alone, fixed by waiting for all
                   parts).
  --extra-arg ARG  (B3, UNSAFE opt-in) prepend ARG to every lean argv (e.g. -Ddebug.skipKernelTC=true: findings 007 017
                   030 038; -Dlinter.all=false: 022) - the result is no longer the official build's.
  --setup-import-append MOD  (B3 'premise-off', untrusted, sound preset; S07) every eligible module's setup.json gets
                   `imports` = its plain header imports + MOD (ModuleSetup.imports? supersedes the header); eligible =
                   plain header whose closure already contains Lean.LibrarySuggestions.Basic (see build/README.md)
  --lean-path-append DIR  append DIR to LEAN_PATH;  --lean-path-order project-first  (B3 'lean-path-order', S07) the
                   same LEAN_PATH entries with the root lib dir first, then by descending .olean count
  --retry-exact    (B3, UNSAFE opt-in, only with --extra-arg) a module that fails WITH the extra args is rebuilt once with
                   the exact Lake invocation (finding 062 class: changes which failures are visible).
  --ktc-exempt-translate  (B3 'skip-kernel-tc=except-translate', untrusted, sound preset; D04) modules whose source
                   mentions `to_additive` / `to_dual` (Mathlib's translation attributes use the kernel's error as control
                   flow: G1-ML-1/G1-ML-2) are started WITHOUT the extra argument -Ddebug.skipKernelTC=true and without the
                   zygote (plain lean, the other transforms unchanged); every other module keeps it. Order/options only.
  --split-fallback FILE  (B3 'merge', untrusted, sound preset only; S02) the plan contains MERGED records (key "merged" =
                   member list in emission order, sink last, written by build/mergeplan.py); FILE holds the members'
                   original plan records. A merged module that fails in any way (error, exit != 0, missing output) is
                   replaced by its members' original records, built as a sub-DAG; its dependents keep waiting for the sink.
                   A running merged module is killed at its first error message (its members then build separately).
  --merge-late DIR  (B3 'merge=late', untrusted, sound preset only; S02) the plan on stdin is Lake's ORIGINAL plan; the
                   merge planner runs concurrently and writes DIR/plan.jsonl, then DIR/READY. From then on every merged
                   group none of whose members has been launched is swapped in (members -> the merged record, deps,
                   dependents and priority rewired; the members' current records become its split fallback); groups
                   with a launched member stay unmerged (always safe: exact Lake invocations, other groups unchanged).

Runs the `lean` invocations of a plan written by the planner (Lake 4.33.1's own computation of what `lake build` would
run) in dependency order, exactly as Lake's compileLeanModule runs them:
  * argv = [lean] + plan argv (weakLeanArgs ++ leanArgs, file, -o, -i, -c, --setup, --json), verbatim
  * the setup JSON written to the module's setupFile first (the exact text Lake writes), parent dirs of all outputs
    created, existing outputs removed (Lake's clearOutputArtifacts)
  * environment = this process's environment (= the environment the official `lake build` runs in) + LEAN_PATH
  * stdin = /dev/null, stdout/stderr captured, cwd = the plan's cwd (where `lake build` runs)
A module FAILS like in Lake: exit code != 0, or a JSON message of severity error on stdout.
It runs inside EXACTLY the official build's sandbox (build/official-build.sh) with no extra bind: the plan comes on stdin,
this source via `python3 -I -c`, captured lean output goes to the sandbox's private /tmp, the records to stdout (read by
build.sh outside the sandbox). The process makes itself non-dumpable so the lean children (untrusted code) cannot open
its /proc/<pid>/fd or memory.
Exit status: 0 = every module built; 1 = some module failed with lean's error exit (code 1 or an error message) - the
build is REJECTED, like the failing `lake build`; 3 = DECLINE (plan not executable exactly, or a lean process died from a
signal / exit code >= 2, e.g. out of memory: a resource failure, not a verdict -> official lake build); other = internal
error (treat as DECLINE). No retries, no skipped checks, no edited sources. After the first failure nothing new starts.
Priority (order only, no semantic effect): bottom level with cost 5 + sqrt(lines)/2 (replay of the official full-RH walls:
4,920 s vs 5,210 s for module-count height).
"""
import ctypes, hashlib, heapq, json, math, os, subprocess, sys, tempfile, time


def header_imports(data):
    """Direct imports of a NON-module, non-prelude Lean file whose header is plain `import Ident` lines (comments and
    blank lines allowed), in order; None for anything else (module system, prelude, public/meta/all, escaped names, a
    malformed header) - the caller then leaves that module untransformed. Mirrors Lean.Parser.Module.header (one ident
    per `import`) and HeaderSyntax.imports (Init + meta Init first, isExported = true for non-module files)."""
    try:
        t = data.decode('utf-8')
    except UnicodeDecodeError:
        return None
    i, n, toks = 0, len(t), []
    while i < n:
        c = t[i]
        if c.isspace(): i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i); i = n if j < 0 else j + 1; continue
        if t.startswith('/-', i):
            depth = 0
            while i < n:
                if t.startswith('/-', i): depth += 1; i += 2
                elif t.startswith('-/', i):
                    depth -= 1; i += 2
                    if depth == 0: break
                else: i += 1
            if depth != 0: return None
            continue
        j = i
        while j < n and not t[j].isspace() and not t.startswith('--', j) and not t.startswith('/-', j): j += 1
        tok = t[i:j]; i = j
        if toks and toks[-1] == 'import':
            if not tok or '\u00ab' in tok or '\u00bb' in tok or tok.startswith('.') or tok.endswith('.') or tok in ('all', 'import'): return None
            toks.append(tok); continue
        if tok == 'import': toks.append(tok); continue
        if tok in ('module', 'prelude', 'public', 'meta', 'all'): return None
        break   # first token of the body
    if toks and toks[-1] == 'import': return None
    return [x for x in toks if x != 'import']


def setup_with_imports(r, data, mods, extra_imports):
    """Lake's setup JSON for module r plus `imports` = the header's imports + extra_imports (ModuleSetup.imports?,
    which supersedes the header, Lean/Elab/Frontend.lean). None if the header is not plain or its project imports differ
    from the planner's (Lake's own header parse)."""
    imps = header_imports(data)
    if imps is None or r.get('isModule'):
        return None
    if set(x for x in imps if x in mods) != set(r['deps']) or len(set(imps)) != len(imps):
        return None
    try:
        st = json.loads(r['setup'])
    except ValueError:
        return None
    if 'imports' in st or st.get('isModule'):
        return None
    I = lambda mod, meta=False: {'module': mod, 'importAll': False, 'isExported': True, 'isMeta': meta}
    st['imports'] = [I('Init'), I('Init', True)] + [I(x) for x in imps] + [I(x) for x in extra_imports]
    return json.dumps(st)


def project_first(lean_path, header):
    """The same LEAN_PATH entries, reordered: the root package's lib dir first, then the others by descending number of
    .olean files (stable). With importArts = {} lean resolves every import by probing the LEAN_PATH entries in order
    (findOLean); Lake puts the project's own lib dir last, so every project import costs one failed probe per package
    dir. plancheck refuses any module present in two search roots, so every import still resolves to the same file."""
    root = [p['leanLibDir'] for p in header.get('packages', []) if p.get('isRoot')]
    first = [d for d in lean_path if d in root]
    rest = [d for d in lean_path if d not in root]
    def count(d):
        n = 0
        for _, _, fs in os.walk(d):
            n += sum(1 for f in fs if f.endswith('.olean'))
        return n
    cnt = {d: count(d) for d in rest}
    return first + sorted(rest, key=lambda d: -cnt[d])


def main():
    try:
        if sys.platform != 'darwin':   # macOS has no prctl; its sandbox profile grants no access to another process
            ctypes.CDLL(None).prctl(4, 0, 0, 0, 0)  # PR_SET_DUMPABLE = 0
    except Exception:  # noqa: BLE001
        print('DECLINE: cannot make the scheduler non-dumpable'); return 3
    jobs = int(sys.argv[1]); memfloor = 8.0; early = False; extra = []; retry_exact = False; lean_override = None
    native_ready = None; split_file = None; setup_import_append = []; lean_path_append = []; lean_path_order = None; no_src_check = False; cost_hints = None; check_tail = None
    merge_late = None
    zy_base = None; zyc = None; zy_repl = 16; zy_thp = '0'; zy_log = None; j1sat = False; zy_prefix = None
    ktc_exempt_translate = False
    cg_dirs = []; memfloor_given = False
    macos = None   # lib/budget.py, loaded for --macos-budget (this script runs as `python3 -I -c`: no sibling import)
    a = sys.argv[2:]
    while a:
        o = a.pop(0)
        if o == '--memfloor': memfloor = float(a.pop(0)); memfloor_given = True
        elif o == '--cgroup': cg_dirs.append(a.pop(0))   # D04: a cgroup (host path) whose memory.max - memory.current bounds the build
        elif o == '--macos-budget':   # macOS: no /proc and no cgroup, lib/budget.py supplies the memory figures
            try: import runpy; macos = runpy.run_path(a.pop(0)); macos_total = macos['host_limits']()['mem_total'] or 0
            except Exception as e:  # noqa: BLE001
                print(f'DECLINE: cannot read the host budget ({e})'); return 3
        elif o == '--early-release': early = True
        elif o == '--extra-arg': extra.append(a.pop(0))
        elif o == '--retry-exact': retry_exact = True
        elif o == '--lean': lean_override = a.pop(0)   # opt-in UNSAFE toolchain T1 (build.sh --unsafe toolchain-T1)
        elif o == '--setup-import-append': setup_import_append.append(a.pop(0))   # B3 premise-off (S07)
        elif o == '--lean-path-append': lean_path_append.append(a.pop(0))
        elif o == '--lean-path-order': lean_path_order = a.pop(0)   # B3 lean-path-order (S07)
        elif o == '--check-tail': check_tail = a.pop(0)   # (S07) long kernel-check jobs per module (order only)
        elif o == '--cost-hints': cost_hints = a.pop(0)   # (S07) per-module cost estimates (order / j1 slack only)
        elif o == '--no-src-check': no_src_check = True   # B3 sound-fast-path (S07): no source re-hashing (exactness guard)
        elif o == '--split-fallback': split_file = a.pop(0)   # B3 merge (untrusted): fallback records of merged groups
        elif o == '--merge-late': merge_late = a.pop(0)       # B3 merge=late (untrusted): swap merged groups in later
        elif o == '--native-ready': native_ready = a.pop(0)   # opt-in UNSAFE native package code (build.sh --unsafe native-pkg)
        elif o == '--zygote': zy_base = a.pop(0)          # S01 sound build: base zygote of these immutable modules
        elif o == '--zyc': zyc = a.pop(0)                  # the zygote client (falls back to plain lean without a zygote)
        elif o == '--zygote-replicas': zy_repl = int(a.pop(0))
        elif o == '--zygote-thp': zy_thp = a.pop(0)        # min KB of package oleans copied into anonymous THP windows (0 = off)
        elif o == '--zygote-log': zy_log = a.pop(0)        # per-child rusage log (LEAN_ZYGOTE_RUSAGE), measurement only
        elif o == '--zygote-prefix': zy_prefix = a.pop(0)  # the zygote also imports these completely (children continue)
        elif o == '--j1-when-saturated': j1sat = True      # -j1 while the ready queue fills every free slot (slack > 10%)
        elif o == '--ktc-exempt-translate': ktc_exempt_translate = True   # D04: translation modules keep the kernel check
        else:
            print(f'DECLINE: unknown scheduler option {o}'); return 3
    if zy_base and not zyc:
        print('DECLINE: --zygote needs --zyc'); return 3
    KTC_ARG = '-Ddebug.skipKernelTC=true'
    if ktc_exempt_translate and KTC_ARG not in extra:
        print('DECLINE: --ktc-exempt-translate needs --extra-arg ' + KTC_ARG); return 3
    if retry_exact and not (extra or lean_override or native_ready or setup_import_append or lean_path_order):
        print('DECLINE: --retry-exact needs --extra-arg or --lean'); return 3
    out = sys.stdout
    def rec(**kw):
        out.write(json.dumps(kw) + '\n'); out.flush()
    header = json.loads(sys.stdin.readline())
    mods = {}
    end = None
    for line in sys.stdin:
        r = json.loads(line)
        if 'end' in r:
            end = r['end']; break
        if r['name'] in mods:
            print(f'DECLINE: duplicate module {r["name"]} in plan'); return 3
        mods[r['name']] = r
    if end is None or end != len(mods) or header.get('nmods') != len(mods):
        print('DECLINE: truncated or inconsistent plan'); return 3
    fallback = {}; merged = {m: r['merged'] for m, r in mods.items() if r.get('merged')}
    if merged and not split_file and merge_late is None:
        print('DECLINE: merged plan records need --split-fallback'); return 3
    if split_file:
        with open(split_file) as ff:
            for line in ff:
                fr = json.loads(line); fallback[fr['name']] = fr
        for m, mem in merged.items():
            if mem[-1] != m or any(x not in fallback for x in mem):
                print(f'DECLINE: inconsistent merge fallback for {m}'); return 3
    split_done = set(); killed_merged = set(); scan_pos = {}; last_scan = [0.0]
    launched = set(); absorbed = set(); late_state = {'done': merge_late is None, 'last': 0.0}
    lean = lean_override or header['lean']; cwd = header['cwd']
    lean_path = header['leanPath'].split(':')
    if lean_path_order == 'project-first':
        lean_path = project_first(lean_path, header)
    elif lean_path_order is not None:
        print(f'DECLINE: unknown --lean-path-order {lean_path_order}'); return 3
    env = dict(os.environ); env['LEAN_PATH'] = ':'.join(lean_path + lean_path_append)
    dependents = {m: [] for m in mods}; nwait = {}
    for m, r in mods.items():
        ds = set(r['deps'])
        for d in ds:
            if d not in mods:
                print(f'DECLINE: {m} imports {d} which is not in the plan'); return 3
            dependents[d].append(m)
        nwait[m] = len(ds)
    order = [m for m in mods if nwait[m] == 0]; cnt = dict(nwait); i = 0
    while i < len(order):
        for d in dependents[order[i]]:
            cnt[d] -= 1
            if cnt[d] == 0: order.append(d)
        i += 1
    if len(order) != len(mods):
        print('DECLINE: import cycle among planned modules'); return 3
    w = {}; srchash = {}; setup_alt = {}; setup_skip = []; ext_imps = {}
    if any(x in mods for x in setup_import_append):
        print('DECLINE: a --setup-import-append module is also a project module'); return 3
    for m in mods:
        if no_src_check:   # S07 sound-fast-path: priority weight from the size (~40 bytes per line), no hashing
            try: sz = os.stat(mods[m]['src']).st_size
            except OSError: sz = 2000
            w[m] = 5.0 + math.sqrt(sz / 40.0) / 2.0
            continue
        with open(mods[m]['src'], 'rb') as f:
            data = f.read()
        w[m] = 5.0 + math.sqrt(data.count(b'\n')) / 2.0
        srchash[m] = hashlib.sha256(data).digest()
    nhint = 0; hinted = set()   # V07 (G1-ML-3): the modules whose cost comes from a hint (j1-saturated uses it)
    if cost_hints:   # S07: measured costs of a previous run of the same project replace the static estimate (order only)
        try:
            if cost_hints.endswith('.gz'):
                import gzip
                with gzip.open(cost_hints, 'rt') as hf: H = json.load(hf)
            else:
                with open(cost_hints) as hf: H = json.load(hf)
            for m in mods:
                mem = mods[m].get('merged')
                if mem:   # merged-group cost (S07): one process for the members' work
                    vs = [H.get(x) for x in mem]
                    if vs and all(isinstance(v, (int, float)) and v > 0 for v in vs):
                        w[m] = max(0.5, float(sum(vs)) - 0.7 * (len(vs) - 1)); nhint += 1; hinted.add(m)
                    continue
                v = H.get(m)
                if isinstance(v, (int, float)) and v > 0: w[m] = float(v); nhint += 1; hinted.add(m)
        except (OSError, ValueError) as ex:
            rec(event='cost-hints-unreadable', error=str(ex)[:200])
    # premise-off (S07): the setup rewrite is computed LAZILY when a module is launched (its dependencies have finished
    # by then, so their eligibility is known): only modules whose import closure already contains the
    # library-suggestions extension's home module (directly via one of these external imports, or through an eligible
    # project import) get the extra import, so it adds no module the official build would not load anyway
    HOME = ('Mathlib', 'Lean', 'Lean.LibrarySuggestions', 'Lean.LibrarySuggestions.Basic')
    elig = {}
    def poff_setup(name):
        if name in elig: return setup_alt.get(name)
        try:
            with open(mods[name]['src'], 'rb') as f: data = f.read()
        except OSError:
            data = None
        st = setup_with_imports(mods[name], data, mods, setup_import_append) if data is not None else None
        if st is not None:
            ext = [x for x in header_imports(data) if x not in mods]
            if any(x in HOME for x in ext) or any(elig.get(d, False) for d in mods[name]['deps']):
                elig[name] = True; setup_alt[name] = st; return st
        elig[name] = False; setup_skip.append(name)
        return None
    def src_unchanged(m):   # the source lean reads must be the one the plan (its header/deps) was made from
        if no_src_check: return True
        try:
            with open(mods[m]['src'], 'rb') as f:
                return hashlib.sha256(f.read()).digest() == srchash[m]
        except OSError:
            return False
    TAIL = {}
    if check_tail:   # S07: a module must END by (critical path - its longest kernel-check job) for the targeted check
        try:
            if check_tail.endswith('.gz'):
                import gzip
                with gzip.open(check_tail, 'rt') as tf: TT = json.load(tf)
            else:
                with open(check_tail) as tf: TT = json.load(tf)
            TAIL = {m: float(v) for m, v in TT.items() if m in mods and isinstance(v, (int, float)) and v > 0}
            for m in mods:   # merged group: the longest kernel job of any member (S07)
                mem = mods[m].get('merged')
                if mem:
                    tv = [float(TT[x]) for x in mem if isinstance(TT.get(x), (int, float))]
                    if tv: TAIL[m] = max(tv)
        except (OSError, ValueError) as ex:
            rec(event='check-tail-unreadable', error=str(ex)[:200])
    prio = {}
    for m in reversed(order):
        prio[m] = w[m] + max(max((prio[d] for d in dependents[m]), default=0.0), TAIL.get(m, 0.0))
    # S01 j1-saturated: slack of each module on the estimated critical path (same cost estimate); -j1 only with slack,
    # so near-critical modules keep their intra-file parallelism
    top = {}
    for m in order:
        top[m] = max((top[d] + w[d] for d in mods[m]['deps']), default=0.0)
    cp_est = max(prio.values(), default=0.0)
    slack = {m: cp_est - top[m] - prio[m] for m in mods}
    ready = [(-prio[m], m) for m in mods if nwait[m] == 0]; heapq.heapify(ready)
    tmp = tempfile.mkdtemp(prefix='fvsched.')   # sandbox-private /tmp
    running = {}
    completed = set()

    def split(name):   # merged sink failed -> its members' original invocations as a sub-DAG (sink last)
        mem = merged[name]; memset = set(mem)
        split_done.add(name)
        rec(event='split', module=name, members=len(mem))
        for i, m in enumerate(mem):
            mods[m] = fallback[m]; absorbed.discard(m)   # (merge=late: members swapped in earlier run again)
            elig.pop(m, None); setup_alt.pop(m, None)   # premise-off memo was computed from the MERGED source/record
            if not no_src_check:
                with open(mods[m]['src'], 'rb') as f:
                    srchash[m] = hashlib.sha256(f.read()).digest()
            prio[m] = prio[name] + (len(mem) - i) * 1e-3
            dependents.setdefault(m, [])
        for m in mem:
            pend = []
            for d in set(mods[m]['deps']):
                if d in memset:
                    if d != m: pend.append(d)
                elif d not in completed:   # external deps of a merged group completed before the group started
                    raise RuntimeError(f'split {name}: {m} depends on unfinished {d}')
            for d in pend: dependents[d].append(m)
            nwait[m] = len(pend)
            if not pend: heapq.heappush(ready, (-prio[m], m))

    def kill_failing_merged():   # early kill: a merged module whose output already shows an error message
        now = time.time()
        if now - last_scan[0] < 1.0: return
        last_scan[0] = now
        for pid, (nm, p, _t, outf, _e) in list(running.items()):
            if nm not in merged or nm in split_done or nm in killed_merged: continue
            try:   # pread: the file offset is shared with the running lean (its stdout), never move it
                fd = outf.fileno(); pos = scan_pos.get(pid, 0); size = os.fstat(fd).st_size
                chunk = os.pread(fd, size - pos, pos) if size > pos else b''
            except (OSError, ValueError):
                continue
            scan_pos[pid] = pos + len(chunk)
            if b'"severity":"error"' in chunk.replace(b' ', b''):
                killed_merged.add(nm)
                try: p.kill()
                except OSError: pass
    def merge_in():   # --merge-late: swap in every merged group none of whose members has been launched
        now = time.time()
        if late_state['done'] or now - late_state['last'] < 0.25: return
        late_state['last'] = now
        if os.path.exists(os.path.join(merge_late, 'FAILED')):
            late_state['done'] = True; rec(event='merge-late', applied=0, dissolved=0, failed=True, t=round(now - t_start, 3)); return
        if not os.path.exists(os.path.join(merge_late, 'READY')): return
        late_state['done'] = True
        applied = dissolved = 0; bad = None
        try:
            with open(os.path.join(merge_late, 'plan.jsonl')) as pf:
                pf.readline()
                recs = []
                for line in pf:
                    r = json.loads(line)
                    if 'end' in r: break
                    if r.get('merged'): recs.append(r)
        except (OSError, ValueError) as ex:
            recs = []; bad = str(ex)[:200]
        for r in recs:
            s_, mem = r['name'], r['merged']; memset = set(mem)
            if mem[-1] != s_ or any(m not in mods or m in launched or m in completed or m in absorbed or m in merged
                                    for m in mem) or any(d not in mods for d in r['deps']):
                dissolved += 1; continue
            for m in mem:
                fallback[m] = mods[m]
            pr = max(prio[m] for m in mem)
            for m in mem:
                if m != s_:
                    absorbed.add(m); del mods[m]; dependents.pop(m, None); nwait.pop(m, None)
            mods[s_] = r; merged[s_] = mem; prio[s_] = pr
            # merged-group weight as on the eager path (S07) and the tightest member slack (S01's j1 rule reads both)
            w[s_] = max(0.5, sum(w.get(m, 5.0) for m in mem) - 0.7 * (len(mem) - 1))
            if s_ in slack: slack[s_] = min(slack.get(m, slack[s_]) for m in mem)
            elig.pop(s_, None); setup_alt.pop(s_, None); wua.pop(s_, None)
            if not no_src_check:
                with open(r['src'], 'rb') as f: srchash[s_] = hashlib.sha256(f.read()).digest()
            n = 0
            for d in set(r['deps']):
                lst = [x for x in dependents[d] if x not in memset]
                lst.append(s_); dependents[d] = lst
                if d not in completed: n += 1
            nwait[s_] = n
            if n == 0: heapq.heappush(ready, (-prio[s_], s_))
            applied += 1
        rec(event='merge-late', applied=applied, dissolved=dissolved, absorbed=len(absorbed), error=bad,
            t=round(time.time() - t_start, 3))
    failed = []; crashed = []; srcchanged = []; done = 0; t_start = time.time()
    def cg_read(d, n):
        try:
            with open(os.path.join(d, n)) as f: v = f.read().strip()
            return None if v == 'max' else int(v)
        except (OSError, ValueError): return None
    cg_max = min([m for m in (cg_read(d, 'memory.max') for d in cg_dirs) if m] or [0]) / 1073741824.0
    if macos: cg_max = macos_total / 1073741824.0   # the machine's memory is the limit
    if cg_max and not memfloor_given:   # D04: inside a memory-limited cgroup the default 8 GB floor scales with the limit
        memfloor = min(memfloor, 0.25 * cg_max)

    rec(event='start', merged_groups=len(merged), mods=len(mods), jobs=jobs, lean=lean, early_release=early, extra_args=extra, retry_exact=retry_exact, lean_override=lean_override, native_ready=native_ready, zygote=zy_base, zygote_thp=zy_thp, zygote_replicas=zy_repl, zygote_prefix=zy_prefix, j1_when_saturated=j1sat, ktc_exempt_translate=ktc_exempt_translate,
        setup_import_append=setup_import_append, lean_path=env['LEAN_PATH'], no_src_check=no_src_check, cost_hints=cost_hints, cost_hints_used=nhint, check_tail=check_tail, check_tail_used=len(TAIL), cgroups=cg_dirs, memfloor=memfloor)

    def memavail_gb():
        v = 1e9
        if macos:   # lib/budget.py's estimate stands in for MemAvailable
            try: v = macos['darwin_memory_available']() / 1073741824.0
            except OSError: pass
        try:
            with open('/proc/meminfo') as f:
                for l in f:
                    if l.startswith('MemAvailable:'): v = int(l.split()[1]) / 1048576.0; break
        except OSError: pass
        for d in cg_dirs:   # D04: MemAvailable is the HOST's inside a cgroup (D09) -> also memory.max - memory.current
            mx, cur = cg_read(d, 'memory.max'), cg_read(d, 'memory.current')
            if mx is not None and cur is not None: v = min(v, (mx - cur) / 1073741824.0)
        return v

    PARTS = ('.olean', '.olean.server', '.olean.private', '.ir.sig', '.ir')   # what importers read
    def parts(name):
        return [o for o in mods[name]['outputs'] if o.endswith(PARTS)]
    retried = set(); released = set(); native_used = {}
    j1_used = {}; zygotes = {}; zy_plain = set()
    wua = {}

    def uses_wua(name):
        if name not in wua:
            try:
                with open(mods[name]['src'], 'rb') as f: wua[name] = b'with_unfolding_all' in f.read()
            except OSError: wua[name] = True
        return wua[name]
    trn = {}
    import re as _re
    TRN_RE = _re.compile(rb'\bto_(?:additive|dual)\b')

    def uses_translate(name):   # D04 (--ktc-exempt-translate): the module's (or merged group's) source names a translation
        if name not in trn:      # attribute; unreadable -> treated as using it (keeps the kernel check: the safe side)
            try:
                with open(mods[name]['src'], 'rb') as f: trn[name] = TRN_RE.search(f.read()) is not None
            except OSError: trn[name] = True
        return trn[name]
    ktc_exempted = set()
    msys = {}

    def is_modsys(name):   # D04 (finding 057): the module's header starts with the `module` keyword (module system)
        if name not in msys:
            try:
                with open(mods[name]['src'], 'rb') as f: t = f.read(65536)
            except OSError:
                msys[name] = True   # unreadable: treated as module-system -> plain lean without native code (safe side)
                return True
            i, n = 0, len(t)
            while i < n:   # skip blanks, `--` line comments and (nested) `/- -/` block comments
                if t[i:i + 1].isspace(): i += 1
                elif t.startswith(b'--', i):
                    j = t.find(b'\n', i); i = n if j < 0 else j + 1
                elif t.startswith(b'/-', i):
                    depth = 0
                    while i < n:
                        if t.startswith(b'/-', i): depth += 1; i += 2
                        elif t.startswith(b'-/', i):
                            depth -= 1; i += 2
                            if depth == 0: break
                        else: i += 1
                else: break
            j = i
            while j < n and not t[j:j + 1].isspace(): j += 1
            msys[name] = t[i:j] == b'module'
        return msys[name]
    tstack = max([int(x.split('=', 1)[1]) for r in mods.values() for x in r['argv'] if x.startswith('--tstack=')] or [0])
    prefix_opts = []
    if zy_prefix:   # the prefix is imported with the modules' options: the extra -D args + the most common setup options
        from collections import Counter
        cnt = Counter()
        for r in mods.values():
            try: cnt[json.dumps(json.loads(r['setup']).get('options', {}), sort_keys=True)] += 1
            except (ValueError, KeyError, AttributeError, TypeError): pass
        if cnt:
            for k, v in sorted(json.loads(cnt.most_common(1)[0][0]).items()):
                if isinstance(v, bool): prefix_opts.append(f'-D{k}={"true" if v else "false"}')
                elif isinstance(v, (int, str)): prefix_opts.append(f'-D{k}={v}')

    def zy_sock(nat):
        # one zygote (+ replicas) per --load-dynlib set, started lazily; zyc runs plain lean until its socket exists
        k = tuple(nat)
        if k not in zygotes:
            sock = os.path.join(tmp, f'zy{len(zygotes)}.sock'); dummy = os.path.join(tmp, 'zygote.lean')
            with open(dummy, 'w') as f: f.write('prelude\n')
            zenv = dict(env, LEAN_ZYGOTE_SOCK=sock, LEAN_ZYGOTE_BASE=zy_base, LEAN_ZYGOTE_IDLE='86400',
                        LEAN_ZYGOTE_REPLICAS=str(zy_repl))
            if zy_log: zenv['LEAN_ZYGOTE_DEBUG'] = '1'
            if zy_thp not in ('', '0'): zenv['LEAN_ZYGOTE_THP'] = zy_thp
            zenv['LEAN_ZYGOTE_RUSAGE'] = zy_log or os.path.join(tmp, 'zygote-rusage.log')
            popts = []
            if zy_prefix:
                zenv['LEAN_ZYGOTE_PREFIX'] = zy_prefix
                popts = [x for x in extra if x.startswith('-D')] + prefix_opts
            # plugins / dynlibs are loaded while the zygote parses its options; children skip them (they must be the same)
            plug = [x for x in extra if x.startswith('--plugin') or x.startswith('--load-dynlib') or x.startswith('-p')]
            zargv = [lean] + ([f'--tstack={tstack}'] if tstack else []) + plug + popts + list(nat) + [dummy]
            zlog = open(os.path.join(tmp, f'zy{len(zygotes)}.log'), 'w')
            zp = subprocess.Popen(zargv, cwd=tmp, env=zenv, stdin=subprocess.DEVNULL, stdout=zlog, stderr=subprocess.STDOUT,
                                  start_new_session=True)
            zygotes[k] = (zp, sock, zlog.name, time.time())
            rec(event='zygote', key=list(k), pid=zp.pid, argv=zargv, thp=zy_thp, replicas=zy_repl, prefix=zy_prefix)
        return zygotes[k][1]

    def zy_stop():
        for k, (zp, sock, zl, t0) in zygotes.items():
            try: os.killpg(zp.pid, 9)
            except (ProcessLookupError, PermissionError): pass
            try: zp.wait(timeout=10)
            except Exception: pass  # noqa: BLE001
            try:
                with open(zl) as f: tail = f.read()[-1500:]
            except OSError: tail = ''
            rec(event='zygote-stop', key=list(k), rc=zp.returncode, up=os.path.exists(sock), log_tail=tail)
        n = miss = 0; cpu = 0.0
        try:
            with open(zy_log or os.path.join(tmp, 'zygote-rusage.log')) as f:
                for l in f:
                    x = l.split()
                    if len(x) >= 4: n += 1; cpu += float(x[2]) + float(x[3]); miss += (x[1] == '211')
        except OSError: pass
        if zygotes: rec(event='zygote-children', n=n, cpu=round(cpu, 1), misses=miss)

    def launch(name, exact=False):
        launched.add(name)
        r = mods[name]
        for p in r['outputs'] + [r['setupFile']]:
            os.makedirs(os.path.dirname(p), exist_ok=True)
        for p in r['outputs']:
            try: os.unlink(p)
            except FileNotFoundError: pass
        st_alt = poff_setup(name) if (setup_import_append and not exact) else None
        with open(r['setupFile'], 'w') as sf: sf.write(st_alt or r['setup'])
        outf = tempfile.TemporaryFile(dir=tmp)
        errf = tempfile.TemporaryFile(dir=tmp)
        nat = []
        if native_ready and not exact and os.path.exists(native_ready):   # B3 native-pkg: once the lib is ready
            with open(native_ready) as nf: nat = [nf.read().strip()]
        if name in zy_plain: nat = []   # S01 v3: crash retry runs without the native-pkg dynlib (finding 057)
        if nat and is_modsys(name):   # D04: finding 057 - native package code crashes lean (SIGSEGV) on module-system files;
            nat = []                  # never give them the dynlib (before: crash + 'zygote-retry'/'retry-exact' per module)
        if nat and zy_base and not exact and name not in zy_plain and not os.path.exists(zy_sock(nat)) \
                and os.path.exists(zy_sock([])):
            nat = []   # S01 v2: the native zygote is still preparing -> the running pre-native zygote, without native code
        ex_args = extra
        ktc_off = bool(ktc_exempt_translate and not exact and uses_translate(name))
        if ktc_off:   # D04: this module keeps the build-time kernel check (translation attributes), plain lean, no zygote
            ex_args = [x for x in extra if x != KTC_ARG]
            if name not in ktc_exempted:
                ktc_exempted.add(name); rec(event='ktc-exempt', module=name)
        argv = ([header['lean']] if exact else [lean] + ex_args + nat) + r['argv']   # exact = the planned (official) invocation
        if not exact and j1sat and len(ready) >= jobs - len(running) - 1 and slack.get(name, 0.0) > 0.1 * cp_est \
                and not uses_wua(name) and (name in hinted or nhint >= 0.5 * len(mods)) and w.get(name, 0.0) < 15.0:
            # S01 v4: no -j1 for with_unfolding_all modules; S01 v5: with cost hints only for modules hinted < 15 s.
            # -j1 needs a cost estimate from hints: the module itself is hinted, or hints
            # cover at least half of the plan (RH: unchanged rule). Without applicable hints (nhint == 0: every
            # non-RH project with the preset's RH hints file) the static estimate cannot tell a 50 s module from a 2 s
            # one, and -j1 on an unhinted heavy module put it on the critical path (Mathlib Archive: Cex.GrothendieckPower
            # 17 s -> 51 s, build 35 s -> 78 s; whole Mathlib +150 s, 64 threads)
            argv = argv[:1] + ['-j1'] + argv[1:]; j1_used[name] = True   # saturated and off the critical path
        if not exact and zy_base and name not in zy_plain and not ktc_off:   # S01 zygote: the same argv, forked from a zygote
            argv = [zyc, zy_sock(nat)] + argv
        native_used[name] = bool(nat)
        p = subprocess.Popen(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=outf, stderr=errf)
        running[p.pid] = (name, p, time.time(), outf, errf)

    def scan(outf):
        outf.seek(0)
        data = outf.read().decode('utf-8', 'replace')
        err = False
        for line in data.split('\n'):
            line = line.strip()
            if not line.startswith('{'): continue
            try: msg = json.loads(line)
            except ValueError: continue
            if isinstance(msg, dict) and msg.get('severity') == 'error': err = True
        return err, data

    # Host resource failures are not verdicts: an mmap/thread/file-descriptor/memory failure makes lean exit 1 with an
    # error message although the official build on a capable host would succeed -> DECLINE (the official build decides).
    RES = ('Cannot allocate memory', 'failed to map', 'mmap', 'Resource temporarily unavailable', 'Too many open files',
           'out of memory', 'failed to create thread', 'Stack overflow', 'std::bad_alloc', 'No space left on device',
           "failed to read file '")   # mmap exhaustion shows as "failed to read file '<X>.olean.private'" at 1:0
    if macos:   # the macOS sandbox refuses (EPERM, EACCES) what the Linux one hides or holds in a tmpfs: handed over
        RES += ('Operation not permitted', 'operation not permitted', 'Permission denied', 'permission denied')
    def resource_failure(stdout, stderr):
        return any(p in stdout or p in stderr for p in RES)

    # Outputs must stay exactly what lean produced: a module whose elaboration-time code rewrites ANOTHER module's olean
    # (after it was built, before/while dependents import it) makes the result depend on timing, which differs from
    # Lake's -> fingerprint every output when its module finishes and re-check all at the end (ctime cannot be forged).
    produced = {}
    def fingerprint(path):
        st = os.lstat(path)
        return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns, st.st_mode)

    if zy_base:   # start the first zygote and wait (<= 60 s) for its socket: plain leans at the start cost more than the wait
        zsock = zy_sock([]); zp0 = zygotes[()][0]; t_zy = time.time()
        while not os.path.exists(zsock) and zp0.poll() is None and time.time() - t_zy < 60: time.sleep(0.05)
        rec(event='zygote-ready', up=os.path.exists(zsock), wait=round(time.time() - t_zy, 2))
    while ready or running:
        while ready and len(running) < jobs and not failed and not crashed and not srcchanged:
            if running and memavail_gb() < memfloor: break
            _, m = heapq.heappop(ready)
            if m in absorbed: continue   # swapped into a merged group (merge=late)
            if not src_unchanged(m):
                srcchanged.append(m); break
            launch(m)
        if merge_late is not None and not late_state['done']:
            merge_in()
            if not running and ready: continue
        if not running:
            if merge_late is not None and not late_state['done'] and not failed and not crashed and not srcchanged:
                time.sleep(0.05); continue   # (only possible if the plan is fully built before the merge planner ends)
            break
        if early:
            pid, status, ru = os.wait4(-1, os.WNOHANG)
            if pid == 0:
                progressed = False
                for _, (nm, _p, _t, _o, _e) in list(running.items()):
                    if nm in released: continue
                    ps = parts(nm)
                    if all(os.path.exists(x) for x in ps):
                        released.add(nm); progressed = True; completed.add(nm)
                        produced[nm] = {x: fingerprint(x) for x in ps}
                        rec(event='release', module=nm, t=round(time.time() - t_start, 3))
                        for d in dependents[nm]:
                            nwait[d] -= 1
                            if nwait[d] == 0: heapq.heappush(ready, (-prio[d], d))
                if merged: kill_failing_merged()
                if merge_late is not None and not late_state['done']: merge_in()
                if not progressed: time.sleep(0.05)
                continue
        else:
            pid, status, ru = os.wait4(-1, 0)
        if pid not in running: continue
        name, p, t0, outf, errf = running.pop(pid)
        rc = os.waitstatus_to_exitcode(status); p.returncode = rc
        err, data = scan(outf)
        ok = (rc == 0 and not err)
        if not src_unchanged(name):   # modified while lean ran
            srcchanged.append(name)
        missing = [o for o in mods[name]['outputs'] if ok and not os.path.exists(o)]
        if missing: ok = False
        r = dict(event='module', module=name, rc=rc, error_msg=err, missing=missing, wall=round(time.time() - t0, 3),
                 cpu=round(ru.ru_utime + ru.ru_stime, 3),   # S01: with a zygote only the client's (plain fallbacks: all)
                 start=round(t0 - t_start, 3))   # start: seconds since the scheduler started (timeline analysis)
        if native_ready: r['native'] = native_used.get(name, False)
        if j1sat: r['j1'] = j1_used.pop(name, False)
        if not ok:
            errf.seek(0)
            r['stdout_head'] = data[:4000]; r['stderr_head'] = errf.read().decode('utf-8', 'replace')[:2000]
        rec(**r)
        outf.close(); errf.close()
        if not ok and name in merged and name not in split_done and name not in released and not srcchanged:
            split(name); continue
        if zy_base and not ok and name not in zy_plain and name not in released and not srcchanged and \
                (rc not in (0, 1) or resource_failure(data, r.get('stderr_head', ''))):
            # S01: a zygote child that crashed / hit a resource limit runs once more as the plain lean without native code
            # (no verdict change: the plain lean is the build's own invocation)
            zy_plain.add(name); rec(event='zygote-retry', module=name, rc=rc); launch(name); continue
        if rc not in (0, 1) or (not ok and resource_failure(data, r.get('stderr_head', ''))):
            # S04 (B3 'retries', sound preset): a lean that died from a signal / exit >= 2 / a resource failure WITH the
            # unsafe settings (native code, plugin, patched toolchain, zygote) is rebuilt once with the exact official
            # invocation before the build gives up (S02's AMD run: one native-pkg SIGSEGV declined the whole build); a
            # crash of the exact invocation itself still declines as before
            if retry_exact and name not in retried and name not in released and not srcchanged:
                retried.add(name); rec(event='retry-exact', module=name, rc=rc, reason='crash'); launch(name, exact=True); continue
            crashed.append(name)
        elif not ok and retry_exact and name not in retried and name not in released and not srcchanged:
            retried.add(name); rec(event='retry-exact', module=name); launch(name, exact=True); continue
        if not ok:
            failed.append(name); continue
        done += 1; completed.add(name)
        fp = produced.setdefault(name, {})
        for o in mods[name]['outputs']:
            if o not in fp: fp[o] = fingerprint(o)
        if name not in released:
            for d in dependents[name]:
                nwait[d] -= 1
                if nwait[d] == 0: heapq.heappush(ready, (-prio[d], d))
    wall = time.time() - t_start
    zy_stop()
    if srcchanged:
        rec(event='summary', setup_transformed=len(setup_alt), setup_skipped=len(setup_skip), setup_skipped_sample=setup_skip[:20], built=done, sources_changed=srcchanged[:20], wall=round(wall, 1))
        print(f'DECLINE: sources changed during the build: {srcchanged[:5]}'); return 3
    if crashed:
        rec(event='summary', setup_transformed=len(setup_alt), setup_skipped=len(setup_skip), setup_skipped_sample=setup_skip[:20], built=done, crashed=crashed[:20], wall=round(wall, 1))
        print(f'DECLINE: lean died (signal or exit >= 2) in {crashed[:5]}'); return 3
    if failed:
        rec(event='summary', setup_transformed=len(setup_alt), setup_skipped=len(setup_skip), setup_skipped_sample=setup_skip[:20], built=done, failed=failed[:20], wall=round(wall, 1))
        print(f'BUILD FAILED: {failed[:5]}'); return 1
    if done != len(mods):
        print(f'INTERNAL: built {done} of {len(mods)}'); return 4
    changed = []
    for m, fps in produced.items():
        for o, fp in fps.items():
            try:
                if fingerprint(o) != fp: changed.append(o)
            except OSError:
                changed.append(o)
    if changed:
        rec(event='summary', setup_transformed=len(setup_alt), setup_skipped=len(setup_skip), setup_skipped_sample=setup_skip[:20], built=done, outputs_changed=changed[:20], wall=round(wall, 1))
        print(f'DECLINE: {len(changed)} build outputs changed after their module finished: {changed[:3]}'); return 3
    rec(event='summary', setup_transformed=len(setup_alt), setup_skipped=len(setup_skip), setup_skipped_sample=setup_skip[:20], built=done, failed=0, wall=round(wall, 1))
    print(f'BUILD OK: {done} modules in {wall:.1f} s'); return 0


if __name__ == '__main__':
    sys.exit(main())

#!/usr/bin/env python3
"""[O03 sched_c1l = O01 sched_c1 + CORE LAYOUT options: JOBS_MODE=phys (JOBS = #physical cores of the inherited affinity),
 CORE_RESERVE=K (K whole cores reserved via taskset for units whose priority is top CRIT_TOP(=K) among running; others on
 the remaining cores); LAYOUT_REBAL=s: every s seconds the K running units with the highest score elapsed+LAYOUT_W*succ_blevel
 hold the reserved cores (whole process moved via sched_setaffinity), PRIO_NICE=n (non-critical units under nice -n n)]
O01 sched_c1: direct DAG scheduler (derived from env/sched_plain.py, the reference), runs INSIDE the bwrap sandbox.
usage: sched_c1.py <proj_dir> <log_dir> <jobs> <mem_floor_gb> <lean>
Options from <log_dir>/sched_config.json (sandbox_run.sh clears the environment):
  NO_ILEAN=1   drop '-i' (.ilean is never read in this pipeline; documented lean option; oleans byte-identical)
  NO_C=1       drop '-c' (.c is never compiled in this pipeline; oleans byte-identical)
  PKG_LIB=dir  single hardlinked package lib tree: LEAN_PATH = dir:out (default: every package lib dir, like the reference)
  NATIVE_READY=file  once it exists, its non-empty lines (e.g. --load-dynlib=LIB) are appended to every later lean call;
               a native call that fails WITHOUT an elaboration error is retried once without it (3 such => native off)
  EARLY_RELEASE=1  dependents are released as soon as the module's .olean exists (lean writes it atomically via rename and
               only when the file had no errors); the job slot stays taken until the process is reaped
  ARGS_JSON=file  {module: [lean args]} (lakefile-equivalent); default = the reference's hard-coded RH args
  PRIO=height|lines|sqrtlines  ready-queue priority: module-count height (reference), line-weighted or sqrt(lines) bottom level
  EARLY_KILL=1 kill a lean whose output already shows 'file:l:c: error' (it can never succeed)
  LEAN_EXTRA="..."  extra lean options appended to every unit's args (only harness-approved options in submissions)
Outputs in <log_dir>: sched.log ('EXIT 0' iff all built), modules.jsonl, graph.tsv, sched_stats.tsv
"""
import heapq, json, os, re, select, signal, sys, tempfile, time

PROJ, LOGD, JOBS, MEM_FLOOR_GB, LEAN = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
SRC = os.path.join(PROJ, 'src')
OUT = os.path.join(PROJ, '.lake/build/lib/lean')
IRD = os.path.join(PROJ, '.lake/build/ir')
PKG = os.path.join(PROJ, '.lake/packages')
BASE = ['--tstack=400000', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3',
        '-Dpp.unicode.fun=true', '-DmaxHeartbeats=4000000']
FIELDS = ('GroundTheory.LocalFields.', 'GroundTheory.GlobalFields.')
FIELDS_ARGS = ['-DsynthInstance.maxHeartbeats=400000']
HDR_KW = ('import', 'public', 'meta', 'private', 'module', 'prelude')
ERR_RE = re.compile(r'^[^\n]*:\d+:\d+: error', re.M)
CFG = {}
_c = os.path.join(LOGD, 'sched_config.json')
if os.path.exists(_c): CFG = {k: str(v) for k, v in json.load(open(_c)).items()}
NO_ILEAN = CFG.get('NO_ILEAN') == '1'; NO_C = CFG.get('NO_C') == '1'; PKG_LIB = CFG.get('PKG_LIB')
NATIVE_READY = CFG.get('NATIVE_READY'); EARLY_RELEASE = CFG.get('EARLY_RELEASE') == '1'
EARLY_KILL = CFG.get('EARLY_KILL', '1') == '1'; PRIO = CFG.get('PRIO', 'height')
CORE_RESERVE = int(CFG.get('CORE_RESERVE', '0')); CRIT_TOP = int(CFG.get('CRIT_TOP', '0')); PRIO_NICE = int(CFG.get('PRIO_NICE', '0'))
LAYOUT_W = float(CFG.get('LAYOUT_W', '0.3'))   # rebalance score = elapsed_s + LAYOUT_W * (line-weighted bottom level of the successors)
REBAL = float(CFG.get('LAYOUT_REBAL', '0'))   # >0: every REBAL s the top-K running units (by priority) are moved onto the reserved cores
JOBS_MODE = CFG.get('JOBS_MODE', '')   # 'phys' => JOBS = number of physical cores in the inherited affinity (no SMT sharing)


def core_layout():
    """physical cores (lists of SMT sibling CPUs) of the inherited affinity, from /proc/cpuinfo (/sys is not in bwrap)"""
    allowed = set(os.sched_getaffinity(0)); cores, cur = {}, {}
    try:
        for line in open('/proc/cpuinfo'):
            k, _, v = line.partition(':'); k = k.strip()
            if k == 'processor': cur = {'p': int(v)}
            elif k == 'physical id': cur['s'] = int(v)
            elif k == 'core id':
                if cur['p'] in allowed: cores.setdefault((cur.get('s', 0), int(v)), []).append(cur['p'])
    except (OSError, ValueError, KeyError): cores = {}
    if not cores: cores = {(0, c): [c] for c in allowed}
    return [sorted(v) for _, v in sorted(cores.items())]
ARGS = json.load(open(CFG['ARGS_JSON'])) if CFG.get('ARGS_JSON') else None
LEAN_EXTRA = CFG.get('LEAN_EXTRA', '').split()   # extra documented lean options for every unit (e.g. pending-ruling knobs)
# O02 guard: modules whose OWN source may catch kernel errors (to_additive/to_dual, decide +kernel, metaprograms) keep the
# build-time kernel check, i.e. never get -Ddebug.skipKernelTC (list computed in-pipeline from the pristine sources)
KTC_GUARD = set(l.strip() for l in open(CFG['KTC_GUARD']) if l.strip()) if CFG.get('KTC_GUARD') else set()
# RETRY_PRISTINE: a module that fails (or is early-killed) after any pipeline transformation (deny line appended, extra
# lean options) is restored to its exact PRISTINE text (truncate to the size recorded by prep.py) and rebuilt ONCE with the
# reference arguments only; only if that also fails is it a failure.
DENY_SIZES = json.load(open(CFG['DENY_SIZES'])) if CFG.get('DENY_SIZES') and os.path.exists(CFG['DENY_SIZES']) else {}
RETRY_PRISTINE = CFG.get('RETRY_PRISTINE', '1') == '1'
# RETRY_OFFICIAL: with a harness-built toolchain (LEAN_TC), a module that still fails after the pristine retry is built
# once more with the OFFICIAL 4.33.1 lean (pristine text, reference args, no natives) - same oleans (245/245 identical in a check),
# so one toolchain bug/crash cannot kill a full run. OFFICIAL_LEAN = path of the official lean inside the sandbox.
OFFICIAL_LEAN = CFG.get('OFFICIAL_LEAN') or None


def header_imports(path):
    imps, depth = [], 0
    with open(path, encoding='utf-8', errors='replace') as f:
        for raw in f:
            line, out, i = raw.strip(), [], 0
            while i < len(line):
                if line.startswith('/-', i): depth += 1; i += 2; continue
                if depth and line.startswith('-/', i): depth -= 1; i += 2; continue
                if not depth: out.append(line[i])
                i += 1
            line = ''.join(out).split('--', 1)[0].strip()
            if not line: continue
            toks = line.split()
            if toks[0] not in HDR_KW: break
            if 'import' in toks:
                k = toks.index('import')
                imps.extend(t for t in toks[k + 1:] if t != 'all')
    return imps


def main():
    t_start = time.time()
    os.makedirs(LOGD, exist_ok=True)
    mods = {}
    if CFG.get('DEPS_JSON') and os.path.exists(CFG['DEPS_JSON']):   # graph computed by prep.py (same header rules)
        dj = json.load(open(CFG['DEPS_JSON']))
        mods = {m: v[0] for m, v in dj.items()}; deps = {m: v[1] for m, v in dj.items()}; del dj
    else:
        for root, _, files in os.walk(SRC):
            for fn in files:
                if fn.endswith('.lean'):
                    rel = os.path.relpath(os.path.join(root, fn), SRC)
                    mods[rel[:-5].replace(os.sep, '.')] = rel
        deps = {m: sorted(set(d for d in header_imports(os.path.join(SRC, r)) if d in mods)) for m, r in mods.items()}
    with open(os.path.join(LOGD, 'graph.tsv'), 'w') as g:
        for m, ds in deps.items():
            for d in ds: g.write(f'{m}\t{d}\n')
    rdeps = {m: [] for m in mods}
    for m, ds in deps.items():
        for d in ds: rdeps[d].append(m)
    order, indeg = [], {m: len(deps[m]) for m in mods}
    q = sorted(m for m in mods if indeg[m] == 0)
    while q:
        m = q.pop(); order.append(m)
        for r in rdeps[m]:
            indeg[r] -= 1
            if indeg[r] == 0: q.append(r)
    if len(order) != len(mods): raise SystemExit('import cycle among local modules')
    prio = {}
    if PRIO == 'lines':   # bottom level with cost ~ 3 s + lines/40 (global constants, no project data)
        size = {m: os.path.getsize(os.path.join(SRC, mods[m])) / 40.0 / 40.0 + 3.0 for m in mods}
        for m in reversed(order): prio[m] = size[m] + max((prio[r] for r in rdeps[m]), default=0.0)
    elif PRIO == 'sqrtlines':   # O01: bottom level, cost = 5 s + sqrt(lines)/2 (generic constants; best of the static
        # heuristics replayed on O0013's real rh-mid durations: makespan 771 s vs height 812 s at 136 jobs, oracle 619 s)
        def nlines(rel):
            with open(os.path.join(SRC, rel), 'rb') as f: return f.read().count(b'\n')
        cost = {m: 5.0 + nlines(mods[m]) ** 0.5 / 2.0 for m in mods}
        for m in reversed(order): prio[m] = cost[m] + max((prio[r] for r in rdeps[m]), default=0.0)
    else:
        for m in reversed(order): prio[m] = 1 + max((prio[r] for r in rdeps[m]), default=0)
    sbl, blw = {}, {}   # O03: line-weighted bottom level (3 s + bytes/1600 per module) of each module's successors
    for m in reversed(order):
        sbl[m] = max((blw[r] for r in rdeps[m]), default=0.0); blw[m] = 3.0 + os.path.getsize(os.path.join(SRC, mods[m])) / 1600.0 + sbl[m]
    CORES = core_layout(); NCORES = len(CORES); jobs = JOBS
    if JOBS_MODE == 'phys': jobs = min(JOBS, NCORES)
    K = min(CORE_RESERVE, max(0, NCORES - 1)); res = CORES[NCORES - K:] if K else []
    bulk_aff = ','.join(str(c) for cl in CORES[:NCORES - K] for c in cl)
    free_res = list(range(K)); ktop = CRIT_TOP or K
    pkg_paths = [PKG_LIB] if PKG_LIB else sorted(os.path.join(PKG, p, '.lake/build/lib/lean') for p in os.listdir(PKG))
    env = dict(os.environ, LEAN_PATH=':'.join(([PKG_LIB, OUT] if PKG_LIB else [OUT] + pkg_paths)))
    _le = json.load(open(_c)).get('LEAN_ENV') if os.path.exists(_c) else None   # extra env for every lean (runtime knobs)
    if _le: env.update({k: str(v) for k, v in (json.loads(_le) if isinstance(_le, str) else _le).items()})
    env_official = dict(env)   # RETRY_OFFICIAL: the official lean reads its OWN core lib (never the LEAN_TC copy below)
    if CFG.get('LEAN_PATH_PRE'): env['LEAN_PATH'] = CFG['LEAN_PATH_PRE'] + ':' + env['LEAN_PATH']   # node-local core lib copy first
    t_graph = time.time() - t_start
    N = len(mods)
    remaining = {m: len(deps[m]) for m in mods}
    ready = [(-prio[m], m) for m in mods if remaining[m] == 0]
    heapq.heapify(ready)
    running = {}            # pid -> dict(m, t0, outp, olean, released, native)
    released = set()
    done, failed, blocked = 0, 0, set()
    log = open(os.path.join(LOGD, 'sched.log'), 'a', buffering=1)
    recs = open(os.path.join(LOGD, 'modules.jsonl'), 'a', buffering=1)
    stats = open(os.path.join(LOGD, 'sched_stats.tsv'), 'a', buffering=1)
    log.write(f'START {t_start:.3f} modules={N} edges={sum(len(v) for v in deps.values())} graph_s={t_graph:.1f} jobs={jobs} cores={NCORES} reserved={K} '
              f'cfg={json.dumps(CFG, sort_keys=True)}\n')
    tmpd = tempfile.mkdtemp(prefix='sched-')
    last_stat = 0.0; last_kill_check = 0.0; last_rebal = 0.0
    native = {'args': None, 'off': not NATIVE_READY, 'crashes': 0}
    rfd, wfd = os.pipe(); os.set_blocking(rfd, False); os.set_blocking(wfd, False)
    signal.set_wakeup_fd(wfd, warn_on_full_buffer=False); signal.signal(signal.SIGCHLD, lambda *a: None)

    def mem_avail_gb():
        with open('/proc/meminfo') as f:
            for line in f:
                if line.startswith('MemAvailable:'): return int(line.split()[1]) / 1048576
        return 1e9

    def native_args():
        if native['off']: return []
        if native['args'] is None:
            if not os.path.exists(NATIVE_READY): return []
            native['args'] = [l.strip() for l in open(NATIVE_READY) if l.strip()]
            log.write(f'[{time.time() - t_start:.3f}] NATIVE {native["args"]}\n')
        return native['args']

    pristine_mode = set()   # modules restored to their pristine text, built with reference args only
    official_mode = set()   # modules rebuilt with the official lean (after a failed pristine retry)

    def restore_pristine(m):
        p = os.path.join(SRC, mods[m])
        if m in DENY_SIZES:
            with open(p, 'r+b') as f: f.truncate(int(DENY_SIZES[m]))
        pristine_mode.add(m)

    def launch(m, use_native=True):
        rel = mods[m]; stem = rel[:-5]
        olean, ilean, cfile = (os.path.join(OUT, stem + '.olean'), os.path.join(OUT, stem + '.ilean'),
                               os.path.join(IRD, stem + '.c'))
        os.makedirs(os.path.dirname(olean), exist_ok=True)
        if not NO_C: os.makedirs(os.path.dirname(cfile), exist_ok=True)
        margs = ARGS.get(m) if ARGS is not None else None
        if margs is None: margs = BASE + (FIELDS_ARGS if m.startswith(FIELDS) else [])
        nat = native_args() if use_native else []
        extra = [a for a in LEAN_EXTRA if not (m in KTC_GUARD and a.startswith('-Ddebug.skipKernelTC'))]
        if m in pristine_mode: extra, nat = [], []
        lean_bin = OFFICIAL_LEAN if m in official_mode else LEAN
        args = [lean_bin] + margs + extra + nat + ['-R', SRC, os.path.join(SRC, rel), '-o', olean] + \
               ([] if NO_ILEAN else ['-i', ilean]) + ([] if NO_C else ['-c', cfile])
        outp = os.path.join(tmpd, f'{len(running)}-{time.monotonic_ns()}.out')
        fd = os.open(outp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        t0 = time.time()
        pre, core, crit = [], None, False
        if K or PRIO_NICE:   # O03 layout: critical = priority among the top ktop of the running units (+ itself)
            if REBAL > 0:   # launch-time placement with the rebalance score (elapsed 0 for the new unit)
                now = time.time(); sc = LAYOUT_W * sbl[m]
                crit = sum(1 for R in running.values() if R['m'] not in released and (now - R['t0']) + LAYOUT_W * sbl[R['m']] > sc) < ktop
            else: crit = sum(1 for R in running.values() if prio[R['m']] > prio[m] and R['m'] not in released) < ktop
            if K:
                if crit and free_res: core = free_res.pop(); pre = ['/usr/bin/taskset', '-c', ','.join(map(str, res[core]))]
                else: pre = ['/usr/bin/taskset', '-c', bulk_aff]
            if PRIO_NICE and not crit: pre += ['/usr/bin/nice', '-n', str(PRIO_NICE)]
        exe = pre[0] if pre else lean_bin
        pid = os.posix_spawn(exe, pre + args, env_official if m in official_mode else env, file_actions=[(os.POSIX_SPAWN_DUP2, fd, 1), (os.POSIX_SPAWN_DUP2, fd, 2),
                                                            (os.POSIX_SPAWN_CLOSE, fd)])
        os.close(fd)
        running[pid] = dict(m=m, t0=t0, outp=outp, olean=olean, rel=False, native=bool(nat), killed=False, core=core, crit=crit, official=m in official_mode)

    def release(m, t):
        nonlocal done
        released.add(m); done += 1
        for r in rdeps[m]:
            remaining[r] -= 1
            if remaining[r] == 0 and r not in blocked: heapq.heappush(ready, (-prio[r], r))

    res_sets = [set(cl) for cl in res]; bulk_set = set(c for cl in CORES[:NCORES - K] for c in cl)
    nmoves = [0]
    def set_aff(pid, cpus, depth=0):
        """move every thread of pid and of its descendants (the timing wrapper forks the real lean) to cpus"""
        try: tids = os.listdir(f'/proc/{pid}/task')
        except OSError: return False
        kids = []
        for t in tids:
            try: os.sched_setaffinity(int(t), cpus)
            except OSError: pass
            try:
                with open(f'/proc/{pid}/task/{t}/children') as f: kids += [int(x) for x in f.read().split()]
            except (OSError, ValueError): pass
        if depth < 4:
            for k in kids: set_aff(k, cpus, depth + 1)
        return True
    def rebalance():
        """the K highest-priority live (not yet released) units hold the reserved cores; others are moved to the bulk cores"""
        now = time.time()
        live = [((now - R['t0']) + LAYOUT_W * sbl[R['m']], pid) for pid, R in running.items() if R['m'] not in released]
        want = set(pid for _, pid in sorted(live, reverse=True)[:K])
        for pid, R in running.items():
            if R.get('core') is not None and pid not in want:
                free_res.append(R['core']); R['core_used'] = R['core']; R['core'] = None
                set_aff(pid, bulk_set); nmoves[0] += 1
        for _, pid in sorted(((sc, p) for sc, p in live if p in want), reverse=True):
            R = running[pid]
            if R.get('core') is None and free_res:
                c = free_res.pop(); R['core'] = c; R['crit'] = True
                if set_aff(pid, res_sets[c]): nmoves[0] += 1

    def n_busy():  # slots: every live process counts (released ones too, they still hold CPU/memory briefly)
        return len(running)

    while ready or running:
        while ready and n_busy() < jobs and (n_busy() < 8 or mem_avail_gb() > MEM_FLOOR_GB):
            launch(heapq.heappop(ready)[1])
        if not running: break
        progressed = False
        # reap finished processes (drain the SIGCHLD wakeup pipe every iteration)
        try:
            while os.read(rfd, 65536): pass
        except (BlockingIOError, InterruptedError): pass
        while True:
            try: pid, status = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError: pid = 0
            if pid == 0: break
            if pid not in running: continue
            progressed = True
            R = running.pop(pid); m, t0, outp = R['m'], R['t0'], R['outp']
            if R.get('core') is not None: free_res.append(R['core']); R['core_used'] = R['core']; R['core'] = None
            t1 = time.time(); rc = os.waitstatus_to_exitcode(status)
            with open(outp, encoding='utf-8', errors='replace') as f: out = f.read()
            os.unlink(outp)
            nwarn = out.count(': warning:'); nerr = len(ERR_RE.findall(out))
            ok = rc == 0 or (m in released)
            rec = {'module': m, 't0': round(t0, 3), 't1': round(t1, 3), 'wall': round(t1 - t0, 3), 'rc': rc,
                   'prio': prio[m], 'n_deps': len(deps[m]), 'warnings': nwarn, 'errors': nerr, 'native': R['native'], 'crit': R.get('crit'), 'core': R.get('core_used'), 'official': R.get('official', False)}
            if 't_rel' in R: rec['t_release'] = round(R['t_rel'], 3)
            if rc != 0: rec['output_head'] = out[:4000]
            if not ok and R['native'] and nerr == 0 and not R['killed'] and native['crashes'] < 3:
                native['crashes'] += 1
                if native['crashes'] >= 3: native['off'] = True; log.write(f'[{t1 - t_start:.3f}] NATIVE OFF\n')
                rec['retry_plain'] = True; recs.write(json.dumps(rec) + '\n')
                log.write(f'[{t1 - t_start:.3f}] retry {m} without native (rc={rc})\n')
                launch(m, use_native=False); continue
            if (not ok and RETRY_PRISTINE and m not in pristine_mode
                    and (m in DENY_SIZES or [a for a in LEAN_EXTRA if not (m in KTC_GUARD and a.startswith('-Ddebug.skipKernelTC'))])):
                rec['retry_pristine'] = True; recs.write(json.dumps(rec) + '\n')
                log.write(f'[{t1 - t_start:.3f}] RETRY_PRISTINE {m} (rc={rc}, killed={R["killed"]}): {out[:300]!r}\n')
                restore_pristine(m); launch(m, use_native=False); continue
            if not ok and OFFICIAL_LEAN and OFFICIAL_LEAN != LEAN and m not in official_mode:
                rec['retry_official'] = True; recs.write(json.dumps(rec) + '\n')
                log.write(f'[{t1 - t_start:.3f}] RETRY_OFFICIAL {m} (rc={rc}, killed={R["killed"]}): {out[:300]!r}\n')
                if m not in pristine_mode: restore_pristine(m)
                official_mode.add(m); launch(m, use_native=False); continue
            recs.write(json.dumps(rec) + '\n')
            if ok:
                if rc != 0: log.write(f'[{t1 - t_start:.3f}] NOTE {m} rc={rc} after its olean was written\n')
                if m not in released: release(m, t1)
                log.write(f'[{t1 - t_start:.3f}] ✔ [{done}/{N}] Built {m} ({t1 - t0:.1f}s)\n')
            else:
                failed += 1
                log.write(f'[{t1 - t_start:.3f}] ✖ [{done}/{N}] Failed {m} ({t1 - t0:.1f}s) rc={rc}\n')
                stack = list(rdeps[m])
                while stack:
                    r = stack.pop()
                    if r not in blocked: blocked.add(r); stack.extend(rdeps[r])
        # early release: olean present (atomic rename, only written without errors)
        if EARLY_RELEASE:
            for pid, R in running.items():
                if R['m'] in released: continue
                try: st = os.stat(R['olean'])
                except FileNotFoundError: continue
                if st.st_mtime >= R['t0'] - 1:
                    R['t_rel'] = time.time(); release(R['m'], R['t_rel']); progressed = True
                    if R.get('core') is not None: free_res.append(R['core']); R['core_used'] = R['core']; R['core'] = None
        if EARLY_KILL and time.time() - last_kill_check >= 1.0:
            last_kill_check = time.time()
            for pid, R in running.items():
                if R['killed'] or R['m'] in released: continue
                try:
                    sz = os.path.getsize(R['outp'])
                    if sz == R.get('sz', 0): continue
                    R['sz'] = sz
                    with open(R['outp'], encoding='utf-8', errors='replace') as f: o = f.read(262144)
                except OSError: continue
                if ERR_RE.search(o):
                    try: os.kill(pid, signal.SIGKILL); R['killed'] = True
                    except ProcessLookupError: pass
        t = time.time()
        if K and REBAL > 0 and t - last_rebal >= REBAL:
            last_rebal = t; rebalance()
        if t - last_stat >= 10:
            stats.write(f'{t:.3f}\t{len(running)}\t{len(ready)}\t{done}\t{failed}\t{len(blocked)}\t{mem_avail_gb():.1f}\n')
            last_stat = t
        if not progressed and running:
            if ready and n_busy() < jobs: continue
            try: select.select([rfd], [], [], 0.02 if EARLY_RELEASE else (min(1.0, REBAL) if (K and REBAL > 0) else 1.0))
            except InterruptedError: pass
            try:
                while os.read(rfd, 4096): pass
            except (BlockingIOError, InterruptedError): pass
    log.write(f'SUMMARY built={done}/{N} failed={failed} blocked={len(blocked)} wall_s={time.time() - t_start:.1f} layout_moves={nmoves[0]} retried_pristine={len(pristine_mode)}\n')
    log.write(f'EXIT {0 if failed == 0 and done == N else 1}\n')


if __name__ == '__main__':
    main()

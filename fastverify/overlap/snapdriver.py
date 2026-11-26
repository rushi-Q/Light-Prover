#!/usr/bin/env python3
"""snapdriver.py - UNTRUSTED snapshot producer for the overlapped Lean-kernel leg.

While the (untrusted) build runs, export the constants of already-built modules ("snapshots", native exporter in snapshot
mode, sandboxed like export/export.sh) and hand them to the running incremental kernel leg
(`pleanchecker --incremental=DIR`) by writing `snap PATH` lines to DIR/cmd. Nothing here can influence a verdict: the
kernel leg checks every constant it ingests with the official kernel, and the final export decides (PChk/Incr.lean).

usage: snapdriver.py --log BUILDLOG --proj PROJ --toolchain TC --binds BINDS.tsv --exporter BIN --incr-dir DIR
                     --snap-dir SNAPDIR [--threads N] [--min-new K] [--min-frac F] [--max-snaps M] [--server-log FILE]
Stops when BUILDLOG/sched.out reports the end of the build, or when SNAPDIR/STOP exists.
"""
import argparse, json, os, re, subprocess, sys, threading, time
from concurrent.futures import ProcessPoolExecutor

# ---- static scan for hand-written theorems declared in more than one module (Lean keeps the LAST module's version in
# the solution module's import order; exporting another version first only costs a re-check). Approximate on purpose.
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma)\s+([^\s:({\[]+)')
NS = re.compile(r'^\s*namespace\s+([^\s]+)')
SEC = re.compile(r'^\s*(?:noncomputable\s+)?section\b\s*([^\s]*)')
END = re.compile(r'^\s*end\b\s*([^\s]*)')


CONFINE = [None]   # realpath of the project: dupscan reads only regular files inside it


def scan(path_mod):
    path, mod = path_mod
    out = []
    try:   # O_PATH first (never opens a FIFO / device), checked inside the project, then re-opened through the descriptor
        pfd = os.open(path, os.O_PATH | os.O_CLOEXEC)
        try:
            import stat as _st
            if not _st.S_ISREG(os.fstat(pfd).st_mode) or CONFINE[0] is None or \
                    not os.readlink(f'/proc/self/fd/{pfd}').startswith(CONFINE[0] + os.sep):
                return out
            text = open(f'/proc/self/fd/{pfd}', encoding='utf-8', errors='replace').read()
        finally:
            os.close(pfd)
    except OSError:
        return out
    stack = []   # (kind, name parts)
    depth = 0
    for line in text.split('\n'):
        if '/-' in line or depth:   # crude block-comment skipping
            o, c = line.count('/-'), line.count('-/')
            if depth or o:
                depth = max(0, depth + o - c)
                if depth or o: continue
        m = NS.match(line)
        if m: stack.append(('ns', m.group(1).split('.'))); continue
        m = SEC.match(line)
        if m and not line.lstrip().startswith('section_'): stack.append(('sec', [])); continue
        m = END.match(line)
        if m:
            if stack: stack.pop()
            continue
        m = DECL.match(line)
        if m:
            if m.group(1) == 'private': continue
            n = m.group(2)
            if n.startswith('_root_.'):
                full = n[len('_root_.'):]
            else:
                pre = [p for k, ps in stack if k == 'ns' for p in ps]
                full = '.'.join(pre + [n])
            out.append(full)
    return [(n, mod) for n in out]




def dupscan(src, jobs):
    files = []
    for root, _, fs in os.walk(src):
        if '/.lake' in root or root.endswith('.lake'): continue
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(root, f)
                files.append((p, os.path.relpath(p, src)[:-5].replace(os.sep, '.')))
    decl = {}
    with ProcessPoolExecutor(jobs) as ex:
        for res in ex.map(scan, files, chunksize=256):
            for n, m in res:
                decl.setdefault(n, set()).add(m)
    return {n: ms for n, ms in decl.items() if len(ms) > 1}


# the kernel-implicit names of PChk/Incr.lean (implicitNames): in targeted mode the server skips a target only if every
# one of them that the final export declares was present when the target was checked -> exported with the first snapshot
IMPLICIT = ['Nat', 'Nat.zero', 'Nat.succ', 'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod',
            'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight', 'String',
            'String.ofList', 'String.mk', 'Char', 'Char.ofNat', 'List', 'List.cons', 'List.nil', 'Bool', 'Bool.true',
            'Bool.false', 'eagerReduce', 'Eq', 'Eq.refl', 'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind', 'dontcare',
            'optParam', 'autoParam', 'semiOutParam', 'outParam']


def log(msg):
    sys.stderr.write(f'[snapdriver {time.strftime("%H:%M:%S")}] {msg}\n'); sys.stderr.flush()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--log', required=True); ap.add_argument('--proj', required=True)
    ap.add_argument('--toolchain', required=True); ap.add_argument('--binds', default='')
    ap.add_argument('--exporter', required=True); ap.add_argument('--incr-dir', required=True)
    ap.add_argument('--snap-dir', required=True); ap.add_argument('--threads', type=int, default=64)
    ap.add_argument('--min-new', type=int, default=100); ap.add_argument('--min-frac', type=float, default=0.10)
    ap.add_argument('--max-snaps', type=int, default=120); ap.add_argument('--server-log', default='')
    ap.add_argument('--poll', type=float, default=2.0)
    ap.add_argument('--root-module', default='Main',
                    help="the solution module: snapshot roots are ordered like its import order, so that duplicated "
                         "theorems resolve like in the final export (the later module wins)")
    ap.add_argument('--drain-avail', type=float, default=0.12,
                    help='snapshots are taken while at least this fraction of the CPU is idle or nice (build draining)')
    ap.add_argument('--max-new-frac', type=float, default=0.08,
                    help='at most this fraction of the modules enters one snapshot (oldest first): a snapshot that is '
                         'still being ingested when the build ends delays the final step by at most its own duration')
    ap.add_argument('--tail-left', type=float, default=0.0,
                    help='no new snapshot once fewer than this fraction of the modules (at least 10) is left: the final '
                         'step checks those, and a snapshot still being ingested would delay it')
    ap.add_argument('--early-frac', type=float, default=0.0,
                    help='also take a snapshot when this fraction of the modules is new even if the machine is busy (0 = never)')
    ap.add_argument('--targets', default='',
                    help='TARGETED mode (server started with --targeted): file of declaration names (the kernel hint '
                         'list); a snapshot = the closure of the target names found in the finished modules that are '
                         'not exported yet, taken as soon as new modules finished (no drain condition)')
    ap.add_argument('--min-interval', type=float, default=15.0,
                    help='targeted mode: at least this many seconds between two snapshot exports')
    ap.add_argument('--nice', type=int, default=None,
                    help='nice level of the snapshot exporter (default 19; targeted mode 0: its snapshots must not '
                         'starve behind a saturated build)')
    # optional defaults from overlap/snapdriver.json next to this script (e.g. {"early_frac": 0.15} on shared test hosts)
    cf = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'snapdriver.json')
    if os.path.exists(cf):
        try: ap.set_defaults(**json.load(open(cf)))
        except (OSError, ValueError, TypeError): pass
    a = ap.parse_args()
    os.makedirs(a.snap_dir, exist_ok=True)
    targets = set()      # targeted mode: target names not exported yet
    if a.targets:
        try:
            targets = {ln.strip() for ln in open(a.targets) if ln.strip() and not ln.startswith('#')}
        except OSError as e:
            log(f'cannot read targets ({e}): no snapshots'); return 0
        if a.nice is None: a.nice = 0
        log(f'targeted mode: {len(targets)} target names')
    tall = set(targets)
    if a.nice is None: a.nice = 19
    sched_out = os.path.join(a.log, 'sched.out'); plan = os.path.join(a.log, 'plan.jsonl')
    stop = os.path.join(a.snap_dir, 'STOP')
    # wait for the plan header (leanPath, number of modules)
    hdr = None
    while hdr is None:
        if os.path.exists(stop): log('stopped before the plan existed'); return 0
        try:
            with open(plan) as f:
                line = f.readline()
            if line.endswith('\n'): hdr = json.loads(line)
        except (OSError, ValueError):
            pass
        if hdr is None: time.sleep(a.poll)
    lp = hdr['leanPath'] + ':' + os.path.join(a.toolchain, 'lib', 'lean')
    # position of every project module in the root module's import order (post-order DFS, imports in header order,
    # = Lean's importModules order): roots of a snapshot are passed in this order
    ipos = {}
    srcdir = None
    try:
        deps = {}
        with open(plan) as f:
            f.readline()
            for ln in f:
                if not ln.startswith('{'): continue
                try: r = json.loads(ln)
                except ValueError: continue
                if 'name' in r:
                    deps[r['name']] = r.get('deps', [])
                    if srcdir is None and r.get('src', '').endswith(r['name'].replace('.', '/') + '.lean'):
                        srcdir = r['src'][:-len(r['name'].replace('.', '/') + '.lean')]
        if a.root_module in deps:
            done = set(); stack = [(a.root_module, 0)]; done.add(a.root_module)
            while stack:
                m, i = stack.pop()
                ds = deps.get(m, [])
                if i < len(ds):
                    stack.append((m, i + 1))
                    d = ds[i]
                    if d in deps and d not in done:
                        done.add(d); stack.append((d, 0))
                else:
                    ipos[m] = len(ipos)
        log(f'import order of {a.root_module}: {len(ipos)} modules')
    except OSError as e:
        log(f'no import order ({e})')
    nmods = int(hdr.get('nmods', 0)) or 1
    binds = []
    if a.binds and os.path.exists(a.binds):
        for ln in open(a.binds):
            ln = ln.rstrip('\n')
            if ln:
                p = ln.split('\t'); binds.append((p[0], p[1] if len(p) > 1 and p[1] else p[0]))
    # the S4 masks of every untrusted sandbox - every top-level dir but the system ones
    # hidden (read-only again after the binds); the exporter binary, toolchain, project, packages, snapshot dir bound back.
    # bind destinations must be plain paths inside the project reached through no symlink (the untrusted build runs
    # concurrently and could plant one): else no snapshots at all (the overlap leg is an untrusted speed-up only)
    keep = ('bin', 'sbin', 'lib', 'lib32', 'lib64', 'libx32', 'usr', 'etc', 'dev', 'proc', 'sys', 'nix', 'gnu',
            'home', 'root', 'tmp', 'run', 'var')
    masks = ['/' + d for d in sorted(os.listdir('/')) if d not in keep and os.path.isdir('/' + d) and not os.path.islink('/' + d)]
    def plain(x):
        return x.startswith('/') and not any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in x) and \
            all(c not in ('', '.', '..') for c in x[1:].split('/'))
    rproj = os.path.realpath(a.proj)
    for src, dst in binds:
        if not (plain(src) and plain(dst)) or (src != dst and (not dst.startswith(rproj + '/') or
                                                                os.path.realpath(dst) != dst or not os.path.isdir(dst))):
            log(f'bind {src!r} -> {dst!r} is not a plain directory inside the project: no snapshots')
            return 2
    sbx = ['/usr/bin/bwrap', '--ro-bind', '/', '/', '--tmpfs', '/home', '--tmpfs', '/root', 
           '--tmpfs', '/tmp', '--dir', '/tmp/home', '--tmpfs', '/run', '--tmpfs', '/var']
    for d in masks: sbx += ['--tmpfs', d]
    sbx += ['--dev', '/dev', '--proc', '/proc', '--clearenv', '--ro-bind', a.toolchain, a.toolchain, '--ro-bind', a.proj, a.proj]
    for src, dst in binds: sbx += ['--ro-bind', src, dst]
    # the exporter (it parses oleans produced from project code) must not even see the incremental leg's directory
    sbx += ['--tmpfs', os.path.realpath(a.incr_dir)]
    sbx += ['--ro-bind', a.snap_dir, a.snap_dir, '--ro-bind', a.exporter, a.exporter]
    for d in masks + [os.path.realpath(a.incr_dir)]: sbx += ['--remount-ro', d]
    sbx += ['--setenv', 'PATH', f'{a.toolchain}/bin:/usr/bin:/bin',
            '--setenv', 'HOME', '/tmp/home', '--setenv', 'LANG', 'C.UTF-8', '--setenv', 'LEAN_PATH', lp,
            '--setenv', 'LEAN4EXPORT_SNAP', '1', '--setenv', 'LEAN4EXPORT_THREADS', str(a.threads),
            '--setenv', 'LEAN4EXPORT_VERBOSE', '1']
    if nmods > 100000: sbx += ['--setenv', 'LEAN4EXPORT_EXPR_ESTIMATE_LOG2', '31']
    # hand-written duplicate theorem names (static scan, in the background): such a name is exported only once the
    # module whose version the final export keeps (the last declaring module in the root module's import order) is built
    dupwin = [{}]   # replaced atomically by the scan thread
    def run_dupscan():
        try:
            CONFINE[0] = os.path.realpath(a.proj)
            rs = os.path.realpath(srcdir) if srcdir else None
            if rs and (rs == CONFINE[0] or rs.startswith(CONFINE[0] + os.sep)):   # srcDir comes from the untrusted lakefile
                d = dupscan(rs, max(1, min(16, a.threads)))
                dupwin[0] = {n: max(ms, key=lambda m: ipos.get(m, -1)) for n, ms in d.items()}
                log(f'dupscan: {len(dupwin[0])} duplicated theorem names')
        except Exception as e:  # noqa: BLE001 - a hint only
            log(f'dupscan failed: {e}')
    threading.Thread(target=run_dupscan, daemon=True).start()
    finished = []; seen = set(); pos = 0; buf = ''; ended = False
    sent = 0; nsnap = 0; exported = set()   # module names already in a snapshot
    excl = set()                             # constants exported and not (yet) known to be left out by the server
    pending = []                             # [(k, dumped names)] of snapshots sent and not finished by the server
    cmd_path = os.path.join(a.incr_dir, 'cmd')
    t_start = time.time(); t_last = 0.0

    def cpu_sample():
        with open('/proc/stat') as f:
            v = [int(x) for x in f.readline().split()[1:]]
        return v[3] + v[4] + v[1], sum(v[:8])   # idle + iowait + nice, total
    hist = [(time.time(), *cpu_sample())]

    def avail_frac(window=30.0):
        now = time.time(); a, t = cpu_sample(); hist.append((now, a, t))
        while len(hist) > 2 and now - hist[1][0] >= window: hist.pop(0)
        t0, a0, tt0 = hist[0]
        return (a - a0) / max(1, t - tt0)

    def server_progress():
        """number of snapshots the server has finished (ingested or dropped), from its log (untrusted hint)"""
        if not a.server_log: return sent
        try:
            with open(a.server_log, errors='replace') as f:
                return sum(1 for ln in f if ln.startswith('[incr] snapshot') and
                           ('ingested (' in ln or 'admitted (' in ln or 'dropped' in ln or 'skipped' in ln))
        except OSError:
            return sent

    while True:
        # read new scheduler records
        try:
            with open(sched_out, errors='replace') as f:
                f.seek(pos); chunk = f.read(); pos = f.tell()
        except OSError:
            chunk = ''
        buf += chunk
        lines = buf.split('\n'); buf = lines.pop()
        for ln in lines:
            if ln.startswith('BUILD ') or ln.startswith('DECLINE') or ln.startswith('INTERNAL'): ended = True; continue
            if not ln.startswith('{'): continue
            try: r = json.loads(ln)
            except ValueError: continue
            ev = r.get('event')
            if ev == 'summary': ended = True
            elif ev == 'module' and r.get('rc') == 0 and not r.get('error_msg') and not r.get('missing'):
                m = r.get('module')
                if m and m not in seen: seen.add(m); finished.append(m)
        if ended or os.path.exists(stop):
            log(f'build ended / stop: {len(finished)} modules finished, {nsnap} snapshots sent'); return 0
        new = [m for m in finished if m not in exported]
        done_n = server_progress()
        # at most one snapshot waits behind the one being ingested (the server parses it meanwhile)
        busy = sent - done_n >= 2
        while pending and pending[0][0] <= done_n:
            k, names = pending.pop(0)
            try:
                with open(a.server_log, errors='replace') as f:
                    dropped = any(ln.startswith(f'[incr] snapshot {k}') and ('dropped' in ln or 'skipped' in ln) for ln in f)
            except OSError:
                dropped = True
            if dropped:
                excl -= names                    # export them again
                if a.targets: targets |= names & tall
            else:
                try:
                    lo = set(open(os.path.join(a.incr_dir, f'leftout-{k}.txt')).read().split('\n'))
                    excl -= lo
                    if a.targets: targets |= lo & tall
                except OSError: pass
        av = avail_frac()
        if a.targets:
            # targeted: whenever modules finished since the last snapshot and some target is not exported yet
            want = bool(new) and bool(targets) and time.time() - t_last >= a.min_interval
            near_end = False
        else:
            draining = av >= a.drain_avail
            want = (draining and len(new) >= a.min_new) or (a.early_frac > 0 and len(new) >= a.early_frac * nmods)
            near_end = a.tail_left > 0 and nmods - len(finished) < max(10, int(a.tail_left * nmods))
        if not busy and nsnap < a.max_snaps and want and not near_end:
            nsnap += 1
            base = os.path.join(a.snap_dir, f'snap{nsnap:03d}')
            # roots = every finished module: constants already ingested are excluded, so this exports the new modules'
            # constants plus whatever an earlier snapshot left out (e.g. waiting for another module)
            if not a.targets:
                new = new[:max(a.min_new, int(a.max_new_frac * nmods))]   # oldest first (finish order)
            roots = sorted(list(exported) + new, key=lambda m: ipos.get(m, len(ipos)))
            with open(base + '.roots', 'w') as f: f.write('\n'.join(roots) + '\n')
            exf = base + '.exclude'
            fin = set(finished)
            deferred = [n for n, w in dupwin[0].items() if w not in fin and n not in excl]
            with open(exf, 'w') as fo:
                fo.write('\n'.join(excl) + '\n')
                if deferred: fo.write('\n'.join(deferred) + '\n')
            env_extra = ['--setenv', 'LEAN4EXPORT_EXCLUDE', exf, '--bind', a.snap_dir, a.snap_dir,
                         '--setenv', 'LEAN4EXPORT_DUMPED', base + '.dumped']
            if a.targets:
                # + deferred duplicate theorem names whose final module is built now (a target's closure may need them)
                ripe = [n for n, w in dupwin[0].items() if w in fin and n not in excl]
                prim = [n for n in IMPLICIT if n not in excl]
                with open(base + '.targets', 'w') as f: f.write('\n'.join(prim + sorted(targets) + ripe) + '\n')
                env_extra += ['--setenv', 'LEAN4EXPORT_SNAP_TARGETS', base + '.targets']
            t0 = time.time(); t_last = t0
            with open(base + '.export.part', 'wb') as out, open(base + '.log', 'wb') as err:
                rc = subprocess.call(sbx + env_extra + ['--unshare-all', '--die-with-parent', '--new-session',
                                     '--chdir', a.proj, '--', '/usr/bin/nice', '-n', str(a.nice), a.exporter,
                                     '@' + base + '.roots'],
                                     stdout=out, stderr=err, env={})
            if rc != 0:
                log(f'snapshot {nsnap}: exporter exit {rc} after {time.time() - t0:.1f} s; no more snapshots')
                a.max_snaps = nsnap; continue
            os.rename(base + '.export.part', base + '.export')
            exported.update(new)
            try:
                names = set(open(base + '.dumped').read().split('\n')); names.discard('')
            except OSError:
                names = set()
            excl |= names; pending.append((nsnap, names))
            if a.targets:
                targets -= excl   # exported now or earlier (e.g. inside another target's closure)
                if not names:   # nothing new among the targets: not sent (the server is not bothered)
                    log(f'snapshot {nsnap}: no target in the finished modules yet (export {time.time() - t0:.1f} s)')
                    try: os.unlink(base + '.export')
                    except OSError: pass
                    pending.pop(); nsnap -= 1
                    continue
            try:
                fd = os.open(cmd_path, os.O_WRONLY | os.O_NONBLOCK)
                os.write(fd, f'snap {base}.export\n'.encode()); os.close(fd)
                sent += 1
                log(f'snapshot {nsnap}: {len(new)} modules ({len(finished)}/{nmods} finished, CPU available {av:.2f}), {os.path.getsize(base + ".export")} bytes, export {time.time() - t0:.1f} s, sent at +{time.time() - t_start:.0f} s')
            except OSError as e:
                log(f'snapshot {nsnap}: cannot send ({e}); no more snapshots'); a.max_snaps = nsnap
        time.sleep(a.poll)


if __name__ == '__main__':
    sys.exit(main())

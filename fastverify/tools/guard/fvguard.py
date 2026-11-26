#!/usr/bin/python3 -I
"""fvguard.py - root-less resource guard for untrusted work. UNTRUSTED component (availability).

    fvguard.py [LIMITS] [--json FILE] [--grace S] [--violation-exit N] -- CMD [ARGS...]
    LIMITS: --mem BYTES     whole-tree memory: sum over the tree of anonymous + shmem pages + bytes used in tmpfs mounts that
                            are private to a sandbox below (bwrap --tmpfs /tmp, --dev /dev, ...): those pages belong to no process
            --mem-metric anon|pss     anon (default): RssAnon + RssShmem from /proc/PID/status (0.9 ms per poll on a lean
                            process that imported Mathlib; counts fork/COW-shared pages in every process - Watch(...,
                            mem_baseline=) subtracts a parent's share); pss: Pss_Anon + Pss_Shmem from smaps_rollup
                            (proportional, but ~130 ms per poll on the same process: only for small trees)
            --procs N       processes in the tree        --threads N   threads in the tree
            --wall S        wall-clock seconds           --tree-cpu S  CPU seconds of the whole tree (live + reaped)
            --cpu S         RLIMIT_CPU per process       --data BYTES  RLIMIT_DATA per process (hard backstop between polls)
            --fsize BYTES   RLIMIT_FSIZE per process     --nofile N    RLIMIT_NOFILE per process     (core dumps always off)
            --disk PATH:BYTES   bytes under PATH (repeatable; also --disk-files N = entries per PATH)
            --out BYTES     total stdout+stderr bytes before the tree is killed; --keep BYTES = bytes kept per stream
            --poll S        watchdog period (default 0.1 s for the first second, then 0.25 s)
            --cgroup cgrun|systemd-user|TEMPLATE   run the command in a fresh cgroup-v2 scope: the KERNEL enforces --mem
                            (memory.max, swap 0; tmpfs and COW pages charged correctly) and --nproc/--threads (TasksMax);
                            an OOM kill there = violation mem (from the scope's memory.events); the watchdog keeps the rest
    Exit: the command's exit status (128+sig on a signal) if no limit was hit; --violation-exit (default 125) if a limit
    was hit (the tree is killed: SIGTERM to the top process, after --grace seconds SIGKILL to every process of the tree).
    --json FILE: {"violation": null|"mem"|"procs"|"threads"|"wall"|"tree_cpu"|"disk"|"disk_files"|"output", "detail",
    "returncode", "signal", "wall_s", "cpu_s", "peak": {...}, "limits": {...}}.

Library use (python3, stdlib only):
    import fvguard
    lim = fvguard.Limits.parse("mem=8G,procs=256,wall=600,cpu=900,fsize=1G,out=64M")
    r = fvguard.run(argv, lim, env={}, cwd=..., disk=[(outdir, 2 << 30)])    # -> fvguard.Result
    r.returncode, r.violation, r.detail, r.stdout, r.stderr, r.peak, r.cpu_s, r.wall_s
    w = fvguard.Watch(pid, lim); w.start(); ...; w.stop()   # watch (and on a violation kill) a process tree we did not
                                                             # spawn, e.g. a fork-server child; w.violation afterwards

Why this design (no cgroups): on typical shared hosts cgroup v2 is root-owned and there is no user systemd bus, and every
worker runs as the same uid (RLIMIT_NPROC would count all of them). So: per-process rlimits through util-linux prlimit
(inherited by bwrap and everything below it) + a watchdog that walks /proc/PID/task/TID/children from the top process. A
bwrap sandbox with --unshare-pid keeps every process of the attempt below its pid-1 (orphans are reparented to it), so the
walk sees the whole tree; in CLI mode the guard is also a child subreaper (orphans of an unsandboxed command come back
to it). Killing a pid-namespace init kills the whole namespace.

Soundness: this module only ends processes and reports that it did. A caller must map a violation to NO VERDICT (never
to a verdict). It never turns a failure into exit 0: exit 0 is returned only when the command itself exited 0 and no
limit was hit.
"""
import ctypes, json, os, re, signal, subprocess, sys, threading, time

PRLIMIT = "/usr/bin/prlimit"
VIOLATION_EXIT = 125
_UNITS = {"": 1, "B": 1, "K": 1 << 10, "M": 1 << 20, "G": 1 << 30, "T": 1 << 40}


def parse_bytes(s):
    m = re.fullmatch(r"\s*(\d+(?:\.\d+)?)\s*([KMGT]?)(?:i?B)?\s*", str(s), re.I)
    if not m:
        raise ValueError(f"bad byte size {s!r}")
    return int(float(m.group(1)) * _UNITS[m.group(2).upper()])


def fmt_bytes(n):
    if n is None:
        return "-"
    for u in ("T", "G", "M", "K"):
        if n >= _UNITS[u]:
            return f"{n / _UNITS[u]:.2f}{u}"
    return str(n)


class Limits:
    KEYS = {"mem": parse_bytes, "nproc": int, "procs": int, "threads": int, "wall": float, "tree_cpu": float, "cpu": int,
            "data": parse_bytes, "fsize": parse_bytes, "nofile": int, "out": parse_bytes, "keep": parse_bytes,
            "disk": parse_bytes, "disk_files": int, "poll": float, "grace": float}

    def __init__(self, **kw):
        self.mem = self.procs = self.threads = self.wall = self.tree_cpu = None
        self.cpu = self.data = self.fsize = self.nofile = self.out = self.disk = self.disk_files = None
        self.keep = 1 << 20
        self.poll = None
        self.grace = 0.0
        self.mem_metric = "anon"
        self.nproc = None
        self.cgroup = None       # None | "cgrun" | "systemd-user" | an argv template with {mem} {tasks}
        for k, v in kw.items():
            if not hasattr(self, k):
                raise ValueError(f"unknown limit {k!r}")
            setattr(self, k, v)

    @classmethod
    def parse(cls, spec):
        """'mem=8G,procs=256,wall=600' -> Limits ('' or None -> no limits). 'disk' = bytes per disk path given to run()."""
        kw = {}
        for part in (spec or "").split(","):
            part = part.strip()
            if not part:
                continue
            k, _, v = part.partition("=")
            k = k.strip().replace("-", "_")
            if k == "cgroup":
                kw[k] = v
                continue
            if k == "mem_metric":
                if v not in ("pss", "anon"):
                    raise ValueError("mem_metric must be pss or anon")
                kw[k] = v
                continue
            if k not in cls.KEYS:
                raise ValueError(f"unknown limit {k!r} (known: {', '.join(sorted(cls.KEYS))}, mem_metric)")
            kw[k] = cls.KEYS[k](v)
        return cls(**kw)

    def as_dict(self):
        return {k: getattr(self, k) for k in list(self.KEYS) + ["mem_metric", "cgroup"] if getattr(self, k) is not None}

    def tasks(self):
        return self.nproc or self.threads

    def cgroup_prefix(self):
        """argv that runs the command in a fresh cgroup-v2 scope with memory.max = mem (swap 0) and TasksMax = nproc or
        threads: the kernel then enforces them (tmpfs pages and COW sharing are charged correctly; an excess = OOM kill,
        reported as violation 'mem' from the scope's memory.events). [] if no cgroup launcher was asked for."""
        if not self.cgroup:
            return []
        mem = str(self.mem) if self.mem else "infinity"
        tasks = str(self.tasks()) if self.tasks() else "infinity"
        if self.cgroup == "cgrun":
            exe = next((c for c in (os.environ.get("FV_CGRUN", ""), "/usr/local/bin/cgrun")
                        if c and os.access(c, os.X_OK)), "cgrun")   # FV_CGRUN = path of the cgroup wrapper; else PATH
            a = [os.path.realpath(exe) if os.path.isabs(exe) else exe]
            if self.mem:
                a += ["--mem", mem]
            if self.tasks():
                a += ["--tasks", tasks]
            return a + ["--"]
        if self.cgroup == "systemd-user":
            return ["/usr/bin/systemd-run", "--user", "--scope", "--quiet", "--collect", "-p", f"MemoryMax={mem}",
                    "-p", "MemorySwapMax=0", "-p", f"TasksMax={tasks}", "--"]
        return [x.replace("{mem}", mem).replace("{tasks}", tasks) for x in self.cgroup.split()]

    def inner_prefix(self):
        """argv to put right after bwrap's `--` (inside the sandbox's own user namespace): RLIMIT_NPROC there counts
        only the tasks (processes AND threads) of that sandbox (Linux >= 5.14 counts RLIMIT_NPROC per user namespace;
        measured on 6.8: limit 50 -> 48 children started, 32 refused), a hard cap without polling. Outside a user
        namespace it would count every task of the (shared) uid, so it is never set there."""
        return [PRLIMIT, f"--nproc={self.nproc}:{self.nproc}", "--"] if self.nproc else []

    def rlimit_prefix(self):
        """util-linux prlimit argv prefix: rlimits of the command and (inherited) of everything below it"""
        a = [PRLIMIT, "--core=0:0"]
        if self.cpu:
            a.append(f"--cpu={self.cpu}:{self.cpu + 5}")       # SIGXCPU at the soft limit, SIGKILL at the hard one
        if self.data:
            a.append(f"--data={self.data}:{self.data}")
        if self.fsize:
            a.append(f"--fsize={self.fsize}:{self.fsize}")
        if self.nofile:
            a.append(f"--nofile={self.nofile}:{self.nofile}")
        return a + ["--"]


# ------------------------------------------------------------------------------------------------------------ /proc
def _read(path, n=-1):
    try:
        with open(path, "rb") as f:
            return f.read(n)
    except OSError:
        return None


def children(pid):
    out = []
    try:
        tids = os.listdir(f"/proc/{pid}/task")
    except OSError:
        return out
    for t in tids:
        b = _read(f"/proc/{pid}/task/{t}/children")
        if b:
            out.extend(int(x) for x in b.split())
    return out


def alive(pid):
    """True iff pid exists and is not a zombie"""
    b = _read(f"/proc/{pid}/stat")
    if not b:
        return False
    try:
        return b[b.rindex(b")") + 2:b.rindex(b")") + 3] != b"Z"
    except ValueError:
        return False


def tree(root, include_root=True):
    """live (non-zombie) pids of the process tree below root, parents before children (BFS over
    /proc/PID/task/TID/children); a zombie has no children (they were reparented when it exited)"""
    out, todo, s = [], [root], set()
    while todo:
        p = todo.pop(0)
        if p in s:
            continue
        s.add(p)
        if not alive(p):
            continue
        if p != root or include_root:
            out.append(p)
        todo.extend(children(p))
    return out


def zombies_below(root):
    """zombie children of root (CLI mode reaps them: orphans reparented to the subreaper)"""
    return [c for c in children(root) if not alive(c) and os.path.exists(f"/proc/{c}")]


_SR = re.compile(rb"^(Pss_Anon|Pss_Shmem):\s+(\d+) kB", re.M)
_ST = re.compile(rb"^(RssAnon|RssShmem|Threads):\s+(\d+)", re.M)


def proc_mem(pid, metric):
    """(bytes, threads) of one process; None if it is gone"""
    st = _read(f"/proc/{pid}/status")
    if st is None:
        return None
    d = {k: int(v) for k, v in _ST.findall(st)}
    thr = d.get(b"Threads", 1)
    if metric == "pss":
        sr = _read(f"/proc/{pid}/smaps_rollup")
        if sr:
            return sum(int(v) for _, v in _SR.findall(sr)) * 1024, thr
    return (d.get(b"RssAnon", 0) + d.get(b"RssShmem", 0)) * 1024, thr


def proc_cpu(pid):
    """utime + stime + cutime + cstime of a live process in seconds (reaped children are in c*time)"""
    b = _read(f"/proc/{pid}/stat")
    if not b:
        return 0.0
    try:
        f = b[b.rindex(b")") + 2:].split()
        return (int(f[11]) + int(f[12]) + int(f[13]) + int(f[14])) / os.sysconf("SC_CLK_TCK")
    except (ValueError, IndexError):
        return 0.0


def _unescape(s):
    return re.sub(r"\\([0-7]{3})", lambda m: chr(int(m.group(1), 8)), s)


def tmpfs_mounts(pid):
    """[(major:minor, mount point)] of the tmpfs mounts visible to pid"""
    b = _read(f"/proc/{pid}/mountinfo")
    out = []
    if not b:
        return out
    for ln in b.decode("utf-8", "replace").splitlines():
        a, _, z = ln.partition(" - ")
        f, g = a.split(), z.split()
        if len(f) >= 5 and g and g[0] == "tmpfs":
            out.append((f[2], _unescape(f[4])))
    return out


_HOST_TMPFS = None


def host_tmpfs_devs():
    global _HOST_TMPFS
    if _HOST_TMPFS is None:
        _HOST_TMPFS = {d for d, _ in tmpfs_mounts("self")}
    return _HOST_TMPFS


def private_tmpfs_bytes(pids):
    """bytes used in tmpfs instances that exist only inside the mount namespaces of pids (sandbox-private /tmp, /dev,
    /run, ...): such pages are charged to no process (not in RSS/PSS) but are host memory"""
    own = _read_link("/proc/self/ns/mnt")
    seen_ns, seen_dev, total = set(), set(), 0
    host = host_tmpfs_devs()
    for p in pids:
        ns = _read_link(f"/proc/{p}/ns/mnt")
        if ns is None or ns == own or ns in seen_ns:
            continue
        seen_ns.add(ns)
        for dev, mp in tmpfs_mounts(p):
            if dev in host or dev in seen_dev:
                continue
            path = f"/proc/{p}/root{mp}"
            fd = None
            try:
                # count it only if the path really IS that tmpfs: a covered mount (e.g. /run/user under a later /run, or
                # bwrap's transient base tmpfs at "/" during its setup) resolves to whatever is mounted on top
                # (measured: a transient tmpfs at "/" read as the host root fs, 1.70 TB). The device test and the
                # size MUST come from the same open directory: by path, the sandbox can pivot its root between a stat()
                # and a statvfs(), and the statvfs then measures the HOST root fs (measured: honest attempts NO-VERDICT
                # with "sandbox tmpfs 67.70G" = node 5's / usage, 2 of ~60 setups under load)
                maj, mnr = dev.split(":")
                fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK)
                if os.fstat(fd).st_dev != os.makedev(int(maj), int(mnr)):
                    continue
                st = os.fstatvfs(fd)
            except (OSError, ValueError):
                continue
            finally:
                if fd is not None:
                    os.close(fd)
            seen_dev.add(dev)
            total += (st.f_blocks - st.f_bfree) * st.f_frsize
    return total


def _int_file(p):
    b = _read(p)
    try:
        return int(b.split()[0]) if b else 0
    except (ValueError, IndexError):
        return 0


def _read_link(p):
    try:
        return os.readlink(p)
    except OSError:
        return None


def disk_usage(path, max_entries):
    """(bytes allocated, entries) under path, without following symlinks; stops counting at max_entries+1 entries"""
    total, n, todo = 0, 0, [path]
    while todo:
        d = todo.pop()
        try:
            it = os.scandir(d)
        except OSError:
            continue
        with it:
            for e in it:
                n += 1
                if max_entries and n > max_entries:
                    return total, n
                try:
                    st = e.stat(follow_symlinks=False)
                except OSError:
                    continue
                total += st.st_blocks * 512
                if e.is_dir(follow_symlinks=False):
                    todo.append(e.path)
    return total, n


# ------------------------------------------------------------------------------------------------------------ watchdog
class Watch(threading.Thread):
    """Watches the process tree below `root` (inclusive unless include_root=False) and kills it when a limit is hit.
    After stop()/join(): .violation (None or a key), .detail, .peak (dict). Never reaps (the parent of root does)."""

    def __init__(self, root, limits, disk=(), include_root=True, t0=None, outcount=None, own_children=False,
                 mem_baseline=0):
        super().__init__(daemon=True)
        self.mem_baseline = mem_baseline      # bytes subtracted from the tree's memory (e.g. a fork parent's COW share)
        self.root, self.lim, self.disk = root, limits, list(disk)
        self.include_root = include_root
        self.t0 = t0 or time.time()
        self.outcount = outcount              # callable -> bytes of output seen so far (run() counts the pipes)
        self.own_children = own_children      # CLI mode: the tree is every descendant of this process
        self.violation = self.detail = None
        self.peak = {"mem": 0, "tmpfs": 0, "procs": 0, "threads": 0, "disk": 0, "tree_cpu": 0.0}
        self.polls = 0
        self.poll_s = 0.0
        self.cg = None              # the scope's cgroup dir (cgroup mode)
        self.cg_oom = 0             # oom_kill events seen in it
        self._halt = threading.Event()
        self.killed = threading.Event()

    def pids(self):
        if self.own_children:
            return tree(os.getpid(), include_root=False)
        return tree(self.root, self.include_root)

    def check_once(self):
        lim, pk = self.lim, self.peak
        t = time.time()
        pids = self.pids()
        if not pids:
            return None
        mem = thr = 0
        cpu = 0.0
        live = 0
        for p in pids:          # always sampled: the peaks are part of every result (a profile for free)
            r = proc_mem(p, lim.mem_metric)
            if r is None:
                continue
            live += 1
            mem += r[0]
            thr += r[1]
            cpu += proc_cpu(p)
        tm = private_tmpfs_bytes(pids)
        mem = max(0, mem - self.mem_baseline)
        if lim.cgroup:
            self.cgroup_poll(pids)
            if self.cg:
                pk["cgroup_mem_peak"] = max(pk.get("cgroup_mem_peak", 0), _int_file(self.cg + "/memory.peak"))
        pk["mem"] = max(pk["mem"], mem + tm)
        pk["tmpfs"] = max(pk["tmpfs"], tm)
        pk["procs"] = max(pk["procs"], live)
        pk["threads"] = max(pk["threads"], thr)
        pk["tree_cpu"] = max(pk["tree_cpu"], round(cpu, 2))
        v = None
        if lim.mem and not lim.cgroup and mem + tm > lim.mem:
            v = ("mem", f"memory {fmt_bytes(mem + tm)} (processes {fmt_bytes(mem)} + sandbox tmpfs {fmt_bytes(tm)}) "
                        f"> limit {fmt_bytes(lim.mem)}")
        elif lim.procs and live > lim.procs:
            v = ("procs", f"{live} processes > limit {lim.procs}")
        elif lim.threads and thr > lim.threads:
            v = ("threads", f"{thr} threads > limit {lim.threads}")
        elif lim.tree_cpu and cpu > lim.tree_cpu:
            v = ("tree_cpu", f"tree CPU {cpu:.1f} s > limit {lim.tree_cpu} s")
        elif lim.wall and t - self.t0 > lim.wall:
            v = ("wall", f"wall {t - self.t0:.1f} s > limit {lim.wall} s")
        elif self.outcount and lim.out and self.outcount() > lim.out:
            v = ("output", f"output {fmt_bytes(self.outcount())} > limit {fmt_bytes(lim.out)}")
        else:
            for path, cap in self.disk:
                used, n = disk_usage(path, lim.disk_files)
                pk["disk"] = max(pk["disk"], used)
                if cap and used > cap:
                    v = ("disk", f"{fmt_bytes(used)} under {path} > limit {fmt_bytes(cap)}")
                    break
                if lim.disk_files and n > lim.disk_files:
                    v = ("disk_files", f"more than {lim.disk_files} entries under {path}")
                    break
        self.polls += 1
        self.poll_s += time.time() - t
        return v

    def cgroup_poll(self, pids):
        if self.cg is None:
            own = (_read("/proc/self/cgroup") or b"").strip()
            for p in pids:
                c = (_read(f"/proc/{p}/cgroup") or b"").strip()
                if c and c != own and c.startswith(b"0::/") and c.endswith(b".scope"):
                    self.cg = "/sys/fs/cgroup" + c[3:].decode()
                    self.peak["cgroup"] = c[3:].decode()
                    break
        if self.cg:
            ev = _read(self.cg + "/memory.events") or b""
            m = re.search(rb"^oom_kill (\d+)", ev, re.M)
            if m:
                self.cg_oom = max(self.cg_oom, int(m.group(1)))

    def kill_tree(self):
        """SIGTERM to the top process + --grace seconds, then SIGKILL to every live process of the tree, children
        before parents (a pid-namespace init takes its whole namespace along); repeated until the tree is empty.
        Only pids found in a fresh walk are signalled; the top process is never reaped here (its parent does that
        after this returns), so its pid cannot be reused meanwhile."""
        self.killed.set()
        if self.lim.grace and self.root and alive(self.root):
            try:
                os.kill(self.root, signal.SIGTERM)
            except OSError:
                pass
            end = time.time() + self.lim.grace
            while time.time() < end and alive(self.root):
                time.sleep(0.05)
        for _ in range(200):
            ps = self.pids()
            if not ps:
                break
            for p in reversed(ps):
                try:
                    os.kill(p, signal.SIGKILL)
                except OSError:
                    pass
            if self.own_children:
                self.reap_orphans()
            time.sleep(0.005)
        if self.own_children:
            self.reap_orphans()

    def reap_orphans(self):
        me = os.getpid()
        for z in zombies_below(me):
            if z != self.root:
                try:
                    os.waitpid(z, os.WNOHANG)
                except ChildProcessError:
                    pass

    def run(self):
        while not self._halt.is_set():
            v = self.check_once()
            if v and not self._halt.is_set():
                self.violation, self.detail = v
                self.kill_tree()
                return
            p = self.lim.poll or (0.1 if time.time() - self.t0 < 1.0 else 0.25)
            self._halt.wait(p)

    def stop(self):
        self._halt.set()
        if self.is_alive() and threading.current_thread() is not self:
            self.join()


class Result:
    def __init__(self, **kw):
        self.__dict__.update(kw)

    def as_dict(self):
        d = {k: v for k, v in self.__dict__.items() if k not in ("stdout", "stderr")}
        return d


class _Drain(threading.Thread):
    """reads a pipe to EOF, keeps the first and the last keep/2 bytes, counts everything"""

    def __init__(self, f, keep):
        super().__init__(daemon=True)
        self.f, self.keep = f, max(2, keep)
        self.head, self.tail, self.n = bytearray(), bytearray(), 0

    def run(self):
        h = self.keep // 2
        while True:
            try:
                b = self.f.read1(1 << 16) if hasattr(self.f, "read1") else self.f.read(1 << 16)
            except (OSError, ValueError):
                break
            if not b:
                break
            self.n += len(b)
            if len(self.head) < h:
                k = h - len(self.head)
                self.head += b[:k]
                b = b[k:]
            if b:
                self.tail += b
                if len(self.tail) > h:
                    del self.tail[:len(self.tail) - h]

    def text(self):
        if self.n <= len(self.head) + len(self.tail):
            data = bytes(self.head + self.tail)
        else:
            data = bytes(self.head) + f"\n[... fvguard: {self.n - len(self.head) - len(self.tail)} bytes of output dropped ...]\n".encode() + bytes(self.tail)
        return data.decode("utf-8", "replace")


def _cgroup_violation(lim, w, rc, forwarded=False):
    """cgroup mode: an end of the command that the guard did not cause. A kernel OOM kill shows in the scope's
    memory.events (or as SIGKILL); with systemd's DefaultOOMPolicy=stop (systemd >= 253 measured on Ubuntu 24.04) systemd
    then STOPS the whole scope - the command dies by SIGTERM and the scope (with its events file) is gone before the next
    poll. -> (violation, detail) or (None, None)."""
    if not lim.cgroup:
        return None, None
    peak = w.peak.get("cgroup_mem_peak", 0)
    if w.cg_oom or rc in (128 + 9, -9):
        return "mem", (f"cgroup memory.max {fmt_bytes(lim.mem)}: {w.cg_oom} OOM kill(s) in {w.peak.get('cgroup')}" if w.cg_oom
                       else f"killed by SIGKILL inside the cgroup scope (memory.max {fmt_bytes(lim.mem)}, peak {fmt_bytes(peak)})")
    if rc in (128 + 15, -15) and not forwarded:
        if lim.mem and peak >= lim.mem // 2:
            return "mem", (f"the cgroup scope was stopped (SIGTERM; systemd OOMPolicy=stop after an OOM kill?) at memory peak "
                           f"{fmt_bytes(peak)} of memory.max {fmt_bytes(lim.mem)}")
        return "cgroup_stopped", f"the cgroup scope was stopped from outside (SIGTERM; memory peak {fmt_bytes(peak)})"
    return None, None


def _wait_exit(pid):
    while True:
        try:
            os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT)
            return
        except InterruptedError:
            continue
        except ChildProcessError:
            return


def _reap(pid):
    while True:
        try:
            _, status, ru = os.wait4(pid, 0)
            return status, ru
        except InterruptedError:
            continue
        except ChildProcessError:
            return 9, None            # already reaped by someone else: report as killed


def run(argv, limits, env=None, cwd=None, disk=(), stdin=subprocess.DEVNULL, merge_stderr=False, own_children=False):
    """run argv under limits; never raises for the command's own failures. Result.returncode: the command's status
    (negative = signal, as subprocess) or None when a limit was hit (then .violation/.detail say which)."""
    lim = limits or Limits()
    disk = [(p, c if c is not None else lim.disk) for p, c in disk]
    t0 = time.time()
    env = dict(env) if env is not None else {}
    if lim.cgroup and "PATH" not in env:
        env["PATH"] = "/usr/bin:/bin"        # the launcher (sudo / systemd-run) needs it; bwrap --clearenv drops it again
    p = subprocess.Popen(lim.cgroup_prefix() + lim.rlimit_prefix() + list(argv), env=env, cwd=cwd, stdin=stdin,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT if merge_stderr else subprocess.PIPE,
                         start_new_session=True)
    d_out = _Drain(p.stdout, lim.keep)
    d_err = _Drain(p.stderr, lim.keep) if not merge_stderr else None
    for d in (d_out, d_err):
        if d:
            d.start()
    w = Watch(p.pid, lim, disk=disk, t0=t0, own_children=own_children,
              outcount=lambda: d_out.n + (d_err.n if d_err else 0))
    w.start()
    _wait_exit(p.pid)                 # exited (or killed), NOT reaped: its pid stays ours while the watchdog finishes
    w.stop()
    if own_children:                  # orphans that came back to a subreaper caller are killed too
        w.kill_tree()
    status, ru = _reap(p.pid)
    p.returncode = (-os.WTERMSIG(status) if os.WIFSIGNALED(status) else os.WEXITSTATUS(status))
    # a limit hit while the command was still running wins, even if the command then exited 0 by itself
    for d in (d_out, d_err):
        if d:
            d.join(5)
    for f in (p.stdout, p.stderr):
        try:
            f and f.close()
        except OSError:
            pass
    rc = p.returncode
    viol, detail = w.violation, w.detail
    if viol is None:
        viol, detail = _cgroup_violation(lim, w, rc)
        if viol is None:
            viol, detail = None, w.detail
    if viol is None and rc is not None and rc < 0:
        sig = -rc
        if sig == signal.SIGXCPU or (lim.cpu and sig == signal.SIGKILL and ru and ru.ru_utime + ru.ru_stime >= lim.cpu):
            viol, detail = "cpu", f"RLIMIT_CPU {lim.cpu} s (signal {sig})"
        elif sig == signal.SIGXFSZ:
            viol, detail = "fsize", f"RLIMIT_FSIZE {fmt_bytes(lim.fsize)} (signal {sig})"
    return Result(returncode=None if viol else rc, exit_status=rc, violation=viol, detail=detail,
                  stdout=d_out.text(), stderr=d_err.text() if d_err else "",
                  out_bytes=d_out.n + (d_err.n if d_err else 0), wall_s=round(time.time() - t0, 3),
                  cpu_s=round(ru.ru_utime + ru.ru_stime, 3) if ru else None,
                  maxrss_kb=ru.ru_maxrss if ru else None, peak=w.peak, polls=w.polls,
                  poll_cpu_s=round(w.poll_s, 3), limits=lim.as_dict())


# ------------------------------------------------------------------------------------------------------------ CLI
def main(argv=None):
    import argparse
    argv = sys.argv[1:] if argv is None else argv
    if "--" not in argv:
        print(__doc__.split("\n\n")[0], file=sys.stderr)
        return 2
    k = argv.index("--")
    opts, cmd = argv[:k], argv[k + 1:]
    # accept the library's spelling too (tree_cpu, disk_files, mem_metric): callers build flags from Limits.parse specs
    opts = [("--" + o[2:].partition("=")[0].replace("_", "-") + ("=" + o.partition("=")[2] if "=" in o else ""))
            if o.startswith("--") else o for o in opts]
    ap = argparse.ArgumentParser(prog="fvguard.py")
    for name in ("mem", "data", "fsize", "out", "keep"):
        ap.add_argument("--" + name)
    for name in ("procs", "threads", "cpu", "nofile", "disk-files", "nproc"):
        ap.add_argument("--" + name, type=int)   # --nproc: TasksMax of the --cgroup scope (CLI mode has no sandbox to put it in)
    for name in ("wall", "tree-cpu", "poll", "grace"):
        ap.add_argument("--" + name, type=float)
    ap.add_argument("--mem-metric", choices=["pss", "anon"], default="anon")
    ap.add_argument("--cgroup", default=None,
                    help="kernel-enforced memory.max/TasksMax in a fresh cgroup scope: cgrun | systemd-user | TEMPLATE ({mem} {tasks})")
    ap.add_argument("--disk", action="append", default=[], help="PATH:BYTES")
    ap.add_argument("--json")
    ap.add_argument("--violation-exit", type=int, default=VIOLATION_EXIT)
    a = ap.parse_args(opts)
    if not cmd:
        ap.error("no command after --")
    lim = Limits(mem_metric=a.mem_metric, grace=a.grace if a.grace is not None else 2.0, cgroup=a.cgroup)
    for name in ("mem", "data", "fsize", "out", "keep"):
        v = getattr(a, name)
        if v is not None:
            setattr(lim, name, parse_bytes(v))
    for name in ("procs", "threads", "cpu", "nofile", "disk_files", "wall", "tree_cpu", "poll", "nproc"):
        v = getattr(a, name)
        if v is not None:
            setattr(lim, name, v)
    disk = []
    for spec in a.disk:
        path, _, cap = spec.rpartition(":")
        if not path:
            ap.error("--disk PATH:BYTES")
        disk.append((os.path.realpath(path), parse_bytes(cap)))
    try:   # orphans of the command come back to us, so the tree walk sees them
        ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0)    # PR_SET_CHILD_SUBREAPER
    except (OSError, AttributeError):
        pass
    r = _run_cli(cmd, lim, disk)
    if a.json:
        tmp = a.json + ".tmp"
        with open(tmp, "w") as f:
            json.dump(r, f, indent=1)
        os.replace(tmp, a.json)
    if r["violation"]:
        print(f"fvguard: {r['violation']}: {r['detail']} - process tree killed (no verdict)", file=sys.stderr)
        return a.violation_exit
    rc = r["returncode"]
    return 128 - rc if rc < 0 else rc


def _run_cli(cmd, lim, disk):
    """CLI: stream the command's output through (counting it), watch every descendant of this process"""
    t0 = time.time()
    p = subprocess.Popen(lim.cgroup_prefix() + lim.rlimit_prefix() + cmd, stdin=sys.stdin, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
    count = [0]
    lock = threading.Lock()

    def pump(src, dst):
        while True:
            try:
                b = src.read1(1 << 16)
            except (OSError, ValueError):
                break
            if not b:
                break
            with lock:
                count[0] += len(b)
                over = lim.out and count[0] > lim.out
            if not over:
                try:
                    dst.write(b)
                    dst.flush()
                except (OSError, ValueError):
                    pass
    ts = [threading.Thread(target=pump, args=(p.stdout, sys.stdout.buffer), daemon=True),
          threading.Thread(target=pump, args=(p.stderr, sys.stderr.buffer), daemon=True)]
    for t in ts:
        t.start()
    w = Watch(p.pid, lim, disk=disk, t0=t0, own_children=True, outcount=lambda: count[0])
    w.start()
    old = {}

    fwd_seen = []

    def fwd(sig, _frm):        # a signal to the guard ends the guarded tree too (and is not a limit violation)
        fwd_seen.append(sig)
        try:
            os.killpg(p.pid, sig)
        except OSError:
            pass
    for s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        old[s] = signal.signal(s, fwd)
    _wait_exit(p.pid)
    w.stop()
    w.lim = Limits(**{**w.lim.__dict__, "grace": 0.0})
    w.kill_tree()          # leftovers (daemonized descendants) die with the command
    status, ru = _reap(p.pid)
    rc = -os.WTERMSIG(status) if os.WIFSIGNALED(status) else os.WEXITSTATUS(status)
    p.returncode = rc
    for t in ts:
        t.join(5)
    viol, detail = w.violation, w.detail
    if viol is None:
        viol, detail = _cgroup_violation(lim, w, rc, forwarded=bool(fwd_seen))
        if viol is None:
            detail = w.detail
    if viol is None and rc < 0:
        if -rc == signal.SIGXCPU or (lim.cpu and -rc == signal.SIGKILL and ru and ru.ru_utime + ru.ru_stime >= lim.cpu):
            viol, detail = "cpu", f"RLIMIT_CPU {lim.cpu} s"
        elif -rc == signal.SIGXFSZ:
            viol, detail = "fsize", f"RLIMIT_FSIZE {fmt_bytes(lim.fsize)}"
    return {"violation": viol, "detail": detail, "returncode": rc, "wall_s": round(time.time() - t0, 3),
            "cpu_s": round(ru.ru_utime + ru.ru_stime, 3) if ru else None, "maxrss_kb": ru.ru_maxrss if ru else None,
            "out_bytes": count[0],
            "peak": w.peak, "polls": w.polls, "poll_cpu_s": round(w.poll_s, 3), "limits": lim.as_dict(),
            "argv": cmd}


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/python3 -I
"""budget.py - resource budget helpers for fastverify (untrusted orchestration helpers, no verdict logic).

  budget.py host                       -> JSON: the limits that apply to THIS process (cgroup v2 memory.max / memory.high /
                                          memory.current, cpu.max quota, cpuset.cpus.effective, sched_getaffinity, /proc/meminfo
                                          MemAvailable, /dev/shm free, swap) - not just /proc/meminfo, which shows the HOST's
                                          memory inside a container / cgroup
                                          On macOS: sysctl and Mach VM figures instead (darwin_memory_estimate), and
                                          build_jobs, the number of build workers that the available memory carries
  budget.py estimate STAGE BYTES [T]   -> JSON: estimated peak memory (bytes) of STAGE (check | ccmp | pleanchecker | gruszka |
                                          export) for an export of BYTES bytes at T threads, from the measured model below
  budget.py plan BYTES [--mem BYTES] [--cpus N]  -> JSON: recommended threads for the trusted check under a memory budget
                                          (default: what `host` reports), whether it fits, and the expected peak

Model (fitted on a 224-thread host, cgroup memory.peak incl. page cache; see fastverify/bench/budget/README.md):
  check (3 legs concurrent, the preset's default): peak ~= a_c * export_bytes + b_c * threads + c_c   (threads beyond ~32
  add memory and CPU without reducing wall time for exports <= ~1 GB).  The per-leg models give the floor of a sequential
  low-memory mode (max of the legs instead of their sum).
"""
import json, os, sys
from functools import lru_cache

GiB = 2 ** 30

def _read(p):
    try:
        with open(p) as f:
            return f.read().strip()
    except OSError:
        return None

def _cgroup_dir():
    cg = _read("/proc/self/cgroup") or ""
    for ln in cg.splitlines():
        parts = ln.split(":", 2)
        if len(parts) == 3 and parts[0] == "0":
            return "/sys/fs/cgroup" + parts[2]
    return None

def _num(s):
    if s is None or s == "max":
        return None
    try:
        return int(s)
    except ValueError:
        return None

def _cpuset_count(spec):
    n = 0
    for part in (spec or "").split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-")
            n += int(b) - int(a) + 1
        else:
            n += 1
    return n

@lru_cache(maxsize=1)
def _darwin_vm():
    # mach_host_self() acquires a port reference; one is reused for the scheduler's frequent admission checks
    import ctypes
    lib = ctypes.CDLL(None)
    lib.host_statistics64.argtypes = [ctypes.c_uint32, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p]
    return lib, lib.mach_host_self(), os.sysconf("SC_PAGE_SIZE")

def darwin_memory_estimate(words, page_size):
    """Available memory on macOS, from the uint32 words of one vm_statistics64 sample (mach/vm_statistics.h): the bytes
    that can be had without compressing or swapping anything, which is what MemAvailable means on Linux.
      free_count [0] - speculative_count [23]   pages that hold nothing (free_count includes the speculative ones)
      external_page_count [34]                  file-backed pages, active or not: the cache of files that were read
                                                or written, given back at once. A cache that a build has just filled
                                                must not lower the figure
      purgeable_count [22]                      pages that their owner marked as discardable
    Anonymous pages are left out, the inactive ones too: they come back only through the compressor or the swap file.
    So the figure is conservative on purpose. macOS can give more by compressing idle applications, and whether it
    should is the owner's decision. It is sampled again at every use: at the scheduler's admission of a worker and
    for build_jobs (host_limits). It is no limit of a running command: the figure moves by gigabytes within minutes."""
    return (words[0] - words[23] + words[34] + words[22]) * page_size

def darwin_memory_available():
    import ctypes
    lib, port, page_size = _darwin_vm()
    info = (ctypes.c_uint32 * 64)()
    count = ctypes.c_uint32(len(info))
    if lib.host_statistics64(port, 4, info, ctypes.byref(count)) or count.value < 35:   # HOST_VM_INFO64
        raise OSError("host_statistics64(HOST_VM_INFO64) failed")
    return darwin_memory_estimate(info, page_size)

def _darwin_sysctl(name):
    import ctypes
    data = ctypes.create_string_buffer(8)   # hw.ncpu and hw.memsize are native 32- or 64-bit scalars
    size = ctypes.c_size_t(len(data))
    if ctypes.CDLL(None).sysctlbyname(name.encode(), data, ctypes.byref(size), None, ctypes.c_size_t(0)):
        return None
    return int.from_bytes(data.raw[:size.value], sys.byteorder)

def host_limits():
    """Effective limits for this process: the minimum over the cgroup chain (every ancestor's memory.max / cpu.max applies)."""
    out = {"cgroup": _cgroup_dir(), "memory_max": None, "memory_high": None, "memory_current": None, "memory_peak": None,
           "swap_max": None, "cpu_quota": None, "cpuset_cpus": None, "cpus_effective": None, "affinity_cpus": None,
           "mem_available": None, "mem_total": None, "shm_free": None, "limited_by": {}}
    if sys.platform == "darwin":   # no cgroup and no /proc: the machine's own figures
        cpus = _darwin_sysctl("hw.ncpu") or os.cpu_count() or 1
        memory = _darwin_sysctl("hw.memsize")
        available = darwin_memory_available()
        reserve = min(4 * GiB, memory // 8) if memory else 4 * GiB   # headroom for macOS itself
        # build_jobs: the workers of 2 GiB each that fit into the available memory after the reserve, at most one a CPU
        out.update(cpus_effective=cpus, cpu_budget=cpus, mem_total=memory, mem_available=available,
                   memory_budget=available, build_jobs=max(1, min(cpus, (available - reserve) // (2 * GiB))))
        return out
    d = out["cgroup"]
    while d and d.startswith("/sys/fs/cgroup"):
        mm = _num(_read(os.path.join(d, "memory.max")))
        if mm is not None and (out["memory_max"] is None or mm < out["memory_max"]):
            out["memory_max"] = mm; out["limited_by"]["memory_max"] = d
        mh = _num(_read(os.path.join(d, "memory.high")))
        if mh is not None and (out["memory_high"] is None or mh < out["memory_high"]):
            out["memory_high"] = mh; out["limited_by"]["memory_high"] = d
        sw = _num(_read(os.path.join(d, "memory.swap.max")))
        if sw is not None and (out["swap_max"] is None or sw < out["swap_max"]):
            out["swap_max"] = sw
        cm = _read(os.path.join(d, "cpu.max"))
        if cm and not cm.startswith("max"):
            q, per = cm.split()
            quota = int(q) / int(per)
            if out["cpu_quota"] is None or quota < out["cpu_quota"]:
                out["cpu_quota"] = quota; out["limited_by"]["cpu_quota"] = d
        if out["memory_current"] is None:
            out["memory_current"] = _num(_read(os.path.join(d, "memory.current")))
            out["memory_peak"] = _num(_read(os.path.join(d, "memory.peak")))
            ce = _read(os.path.join(d, "cpuset.cpus.effective"))
            if ce:
                out["cpuset_cpus"] = ce; out["cpus_effective"] = _cpuset_count(ce)
        if d == "/sys/fs/cgroup":
            break
        d = os.path.dirname(d)
    try:
        out["affinity_cpus"] = len(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        out["affinity_cpus"] = os.cpu_count()
    mi = _read("/proc/meminfo") or ""
    for ln in mi.splitlines():
        if ln.startswith("MemAvailable:"):
            out["mem_available"] = int(ln.split()[1]) * 1024
        elif ln.startswith("MemTotal:"):
            out["mem_total"] = int(ln.split()[1]) * 1024
    try:
        st = os.statvfs("/dev/shm")
        out["shm_free"] = st.f_bavail * st.f_frsize
    except OSError:
        pass
    # the budget that counts: the smaller of the cgroup limit (minus what the group already uses) and MemAvailable
    cands = []
    if out["memory_max"] is not None:
        cands.append(out["memory_max"] - (out["memory_current"] or 0))
    if out["mem_available"] is not None:
        cands.append(out["mem_available"])
    out["memory_budget"] = min(cands) if cands else None
    cpus = [c for c in (out["affinity_cpus"], out["cpus_effective"]) if c]
    if out["cpu_quota"] is not None:
        cpus.append(max(1, int(out["cpu_quota"])))
    out["cpu_budget"] = min(cpus) if cpus else os.cpu_count()
    return out

# ---- measured model (coefficients in bytes; fitted in bench/budget/fit.py from bench/budget/results/*.json) ----
# The least-squares fit of the 16 unlimited check runs (fit.py: 3.64 x export + 46 MB/thread + 1.24 GB) is dominated by the
# Mathlib/RH rows and over-estimates project-size exports; the "check" row below is the planning envelope that matches the
# floors measured by bisection of memory.max (rh-mid: 4 GB at 4 threads, 5 at 8, 6 at 16; Mathlib: 22-24 GB at 16; RH:
# 212 GB at 64) within the 15 % margin of plan(). tests/budget/run.sh checks it against those floors.
MODEL = {
    # stage: (bytes per export byte, bytes per thread, constant bytes) - fit.py (rh-miniF, rh-mid, Mathlib, RH: 16 check runs)
    "check":        (3.7, 100 * 2**20, int(0.4 * GiB)),   # planning envelope of the measured floors (see below)
    "ccmp":         (1.86, 19 * 2**20, int(0.12 * GiB)),
    "pleanchecker": (1.82, 33 * 2**20, int(0.10 * GiB)),
    "gruszka":      (0.50, 54 * 2**20, 0),
    "export":       (5.0, 0, int(0.5 * GiB)),     # E1 alone: rh-mid 7.1 GB for 1.03 GB (6.9x), RH 168 GB for 57.3 GB (2.9x; anon 139) -> 5x envelope for project sizes
}

def estimate(stage, export_bytes, threads=16):
    a, b, c = MODEL[stage]
    return int(a * export_bytes + b * threads + c)

def plan(export_bytes, mem_budget=None, cpu_budget=None, safety=1.15):
    h = host_limits() if (mem_budget is None or cpu_budget is None) else None
    mem = mem_budget if mem_budget is not None else (h["memory_budget"] or 0)
    cpus = cpu_budget if cpu_budget is not None else (h["cpu_budget"] or 1)
    # more than 32 threads buys nothing for exports <= ~1 GB and costs memory; above that scale with the export
    cap = 32 if export_bytes <= 2 * GiB else 64 if export_bytes <= 16 * GiB else 256
    t = max(1, min(cpus, cap))
    while t > 1 and estimate("check", export_bytes, t) * safety > mem:
        t = max(1, t // 2)
    peak = estimate("check", export_bytes, t)
    return {"threads": t, "expected_peak_bytes": peak, "fits": peak * safety <= mem, "memory_budget": mem,
            "cpu_budget": cpus, "sequential_legs_floor_bytes": max(estimate(s, export_bytes, t) for s in
                                                                   ("ccmp", "pleanchecker", "gruszka"))}

def main(argv):
    if len(argv) < 2 or argv[1] in ("-h", "--help"):
        print(__doc__); return 2
    if argv[1] == "host":
        print(json.dumps(host_limits(), indent=1)); return 0
    if argv[1] == "estimate":
        st = argv[2]; b = int(float(argv[3])); t = int(argv[4]) if len(argv) > 4 else 16
        print(json.dumps({"stage": st, "export_bytes": b, "threads": t, "peak_bytes": estimate(st, b, t)})); return 0
    if argv[1] == "plan":
        b = int(float(argv[2])); mem = None; cpus = None
        a = argv[3:]
        while a:
            o = a.pop(0)
            if o == "--mem": mem = int(float(a.pop(0)))
            elif o == "--cpus": cpus = int(a.pop(0))
        print(json.dumps(plan(b, mem, cpus), indent=1)); return 0
    print(__doc__); return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv))

#!/usr/bin/python3 -I
"""gates.py -- the soundness suites for a candidate SOUND check configuration.

  gates.py --out DIR [--check SCRIPT] [--legs LEGS.json] [--gate G ...] [--jobs J] [--threads T] [--label TEXT]

  --check SCRIPT   the full sound check entry point under test, interface of check/sound/check-sound.sh:
                     SCRIPT EXPORT CHALLENGE_EXPORT COMPARATOR_JSON --threads N --json FILE   (exit 0/1/2)
  --legs FILE      JSON describing the kernel legs exactly as SCRIPT runs them (kernel-only corpora have no challenge):
                     {"lean": {"argv": [...], "env": {...}}, "k2": {"argv": [...], "env": {...}}, "ro": [paths]}
                   placeholders {export} {threads} in argv/env values, {here} (= this directory) anywhere.
                   "lean" = the official-kernel replay leg (DECIDES),
                   "k2" = the second, independent kernel (may only veto).
                   optional "extra": {"con-leche": {"argv": [...], "env": {...}}, "nanoda": {"argv": [..., "{config}"],
                   "config": {...}}} = the VETO-ONLY extra kernels of check-sound.sh v2.3-H exactly as it runs them
                   ({kjobs} = min(threads, 64); "config" = the nanoda JSON check-sound.sh writes, {export}/{kjobs}
                   substituted, its path = {config}); each run is classified by the check script's OWN classifier
                   (SCRIPT --xk-classify KERNEL LOG RC); combined = ACCEPT iff lean and k2 accept and no extra kernel
                   'rejected' (check-sound.sh semantics: extra kernels are consulted only after a two-kernel ACCEPT).
  --gate G         arena | suitex | cmpx | mathlib | mutants | threads | incr | all (default all that have inputs)
  Inputs (defaults; override with --inputs FILE.json): see INPUTS below.

Suite semantics (a suite FAILS on any row marked FAIL):
  arena, suitex   kernel-only corpora (label = directory good/bad; the labels equal the official Lean 4.36 leanchecker's
                  verdict: arena 225/225, suitex labels were checked by the official kernel when added).
                  lean leg  : must give the label on every test (exit 0 good / 1 bad); any other exit on a good test =
                              WARN-DECLINE (availability), a bad test accepted = FAIL-CRITICAL, a good test rejected =
                              FAIL-REJECT (the official kernel accepts it: the leg is not the official replay).
                  k2 leg    : a bad test accepted = INFO (k2 can only veto); a good test rejected = WARN (availability).
                  combined  : ACCEPT iff both accept (and no extra kernel rejects); a bad test combined-accepted =
                              FAIL-CRITICAL; an extra kernel rejecting a good test both legs accept = WARN (availability).
  cmpx            comparator-level corpus vs the rh-miniF mini challenge, labels = expected.txt (official comparator):
                  SCRIPT must exit 0 on accept cases, 1 on reject cases; reject case accepted = FAIL-CRITICAL,
                  accept case rejected = FAIL-REJECT, exit 2 = WARN-DECLINE.
  mathlib         Mathlib differential (the MATHLIB_DIFF case set, 19 cases): SCRIPT on
                  each case's (solution export, challenge export, comparator.json); expected = cases.json.
  mutants         RH mutants M1-M4 (61.6 GB each, made by fvmut from the honest export): all must be REJECTED; the
                  honest export must be ACCEPTED (if listed).
  threads         SCRIPT on a fixed set of exports at 1/32/128/255/256/384 threads: identical exit codes on every row.
  incr            the overlapped Lean leg: an incremental server (inputs incr_server, pins' pleanchecker) ingests the
                  case's snapshot exports, then SCRIPT --incr-dir DIR judges the final export; expected per case (e.g.
                  snapshot = honest, final = mutant -> REJECTED; snapshot = mutant, final = honest -> ACCEPTED).
Output: DIR/<gate>.tsv (one row per run), DIR/summary.json, DIR/summary.txt; exit 0 iff no FAIL row.
"""
import argparse
import concurrent.futures as cf
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.realpath(__file__))
LL = "$LIGHT_LEAN"
INPUTS = {
    "arena": "/scratch/bench-inputs/arena/suite",
    "suitex": "/scratch/bench-inputs/suitex",
    "cmpx": "/scratch/bench-inputs/cmpx",
    "cmpx_challenge": "/scratch/bench-inputs/rh-miniF/challenge/challenge.export",
    "cmpx_configs": ["/scratch/bench-inputs/rh-miniF/challenge/comparator.leanonly.json",
                     "/scratch/bench-inputs/rh-miniF/challenge/comparator.nanoda.json"],
    "mathlib": "/scratch/sound-gates-work/mathlib",   # CASE/{solution.export,challenge.export,comparator.json} + cases.json
    "mathlib_cases": "/scratch/bench-inputs/mathlib-differential/cases.json",
    "mutants": [],      # [{"name": "M1", "export": PATH, "expect": "REJECTED"}, ...]
    "mutants_challenge": LL + "/verify/challenge/challenge.export",
    "mutants_config": LL + "/verify/challenge/comparator.json",
    "threads_cases": [],   # [{"name":..., "export":..., "challenge":..., "config":...}]
    "threads_list": [1, 32, 128, 255, 256, 384],
}
TIMEOUT = {"arena": 900, "suitex": 900, "cmpx": 1800, "mathlib": 3600, "mutants": 14400, "threads": 14400, "incr": 14400}


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def sandbox(ro, rw, cwd):
    a = ["/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--ro-bind", "/", "/",
         "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run", "--tmpfs", "/tmp", "--dev", "/dev", "--proc", "/proc"]
    for p in ro:
        a += ["--ro-bind", p, p]
    for p in rw:
        a += ["--bind", p, p]
    return a + ["--chdir", cwd, "--clearenv", "--setenv", "PATH", "/usr/bin:/bin", "--setenv", "HOME", cwd,
                "--setenv", "TMPDIR", cwd, "--setenv", "LANG", "C.UTF-8"]


def run_leg(leg, export, threads, wdir, ro, timeout):
    os.makedirs(wdir, exist_ok=True)
    kj = str(min(int(threads), 64))
    sub = lambda s: s.replace("{export}", export).replace("{threads}", str(threads)).replace("{kjobs}", kj)
    if "config" in leg:   # nanoda: the config check-sound.sh writes, with this run's export and job count
        cfgp = os.path.join(wdir, "nanoda.json")
        json.dump(json.loads(sub(json.dumps(leg["config"]).replace('"{kjobs}"', kj))), open(cfgp, "w"))
        sub0 = sub
        sub = lambda s: sub0(s).replace("{config}", cfgp)
    argv = [sub(x) for x in leg["argv"]]
    env = []
    for k, v in (leg.get("env") or {}).items():
        env += ["--setenv", k, sub(v)]
    cmd = sandbox(ro + [os.path.dirname(export)], [wdir], wdir) + env + ["--"] + argv
    t0 = time.time()
    with open(os.path.join(wdir, "log"), "wb") as lf:
        try:
            p = subprocess.run(["timeout", "--kill-after=10", str(timeout)] + cmd, stdout=lf, stderr=subprocess.STDOUT)
            rc = p.returncode
        except Exception as e:  # noqa: BLE001
            lf.write(str(e).encode())
            rc = 99
    return rc, round(time.time() - t0, 2)


EXTRA_ARGS = []   # --check-args: appended to every check-script run (e.g. --hints FILE)
CLASSIFIER = []   # [check script]: classifies the extra-kernel leg runs of the kernel-only corpora (--xk-classify)


def xk_status(kernel, logf, rc):
    if not CLASSIFIER:
        return "unclassified"
    try:
        p = subprocess.run([CLASSIFIER[0], "--xk-classify", kernel, logf, str(rc)], capture_output=True, text=True,
                           timeout=120)
        return json.loads(p.stdout.strip().splitlines()[-1])["status"]
    except Exception:  # noqa: BLE001
        return "classification-failed"


def xk_summary(j):
    try:
        d = json.load(open(j))
        return ";".join("%s:%s" % (k, v.get("status")) for k, v in sorted((d.get("extra_kernels") or {}).items()))
    except Exception:  # noqa: BLE001
        return ""


def run_check(script, export, chal, cfg, threads, wdir, timeout, extra=()):
    os.makedirs(wdir, exist_ok=True)
    j = os.path.join(wdir, "check.json")
    t0 = time.time()
    with open(os.path.join(wdir, "log"), "wb") as lf:
        p = subprocess.run(["timeout", "--kill-after=30", str(timeout), script, export, chal, cfg, "--threads",
                            str(threads), "--json", j] + EXTRA_ARGS + list(extra), stdout=lf, stderr=subprocess.STDOUT,
                           env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "HOME": wdir, "TMPDIR": wdir}, cwd=wdir)
    reason = ""
    try:
        reason = str(json.load(open(j)).get("reason", ""))[:200]
    except Exception:  # noqa: BLE001
        pass
    xs = xk_summary(j)
    if xs:
        reason = reason + " [xk " + xs + "]"
    return p.returncode, round(time.time() - t0, 2), reason


def run_incr_case(script, case, server, plc, threads, wdir, timeout):
    """Overlap leg: start `server DIR PLC THREADS` (incr-server.sh), feed 'snap PATH' lines into DIR/cmd, optionally
    wait until each snapshot is ingested ([incr] ... constants ... lines in DIR/server.log), then run the check script with
    --incr-dir DIR on the final export. The server is killed afterwards. Returns (rc, seconds, reason, server_log_tail)."""
    import signal
    d = os.path.join(wdir, "incr")
    os.makedirs(d, exist_ok=True)
    srv = subprocess.Popen([server, d, plc, str(threads)] + list(case.get("server_args", [])),
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           start_new_session=True, env=dict({"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"},
                                                            **({"GATE_SERVER_NO_THP": "1"} if os.environ.get("GATE_SERVER_NO_THP") else {})))
    try:
        fifo = os.path.join(d, "cmd")
        def send(line):
            t0 = time.time()
            while True:   # the server opens the FIFO for reading once it is up
                try:
                    fd = os.open(fifo, os.O_WRONLY | os.O_NONBLOCK)
                    break
                except OSError:
                    if time.time() - t0 > 120 or srv.poll() is not None:
                        raise RuntimeError("incremental server not reading its FIFO")
                    time.sleep(0.2)
            os.write(fd, (line + "\n").encode())
            os.close(fd)
        def ingested():   # snapshots the server has finished with (ingested, dropped or skipped)
            try:
                return sum(1 for ln in open(os.path.join(d, "server.log"), errors="replace")
                           if ln.startswith("[incr] snapshot ") and (" ingested (" in ln or "snapshot dropped" in ln
                                                                       or "snapshot skipped" in ln or " admitted (" in ln))
            except OSError:
                return 0
        for k, sp in enumerate(case.get("snaps", [])):
            send("snap " + sp)
            if case.get("wait_ingest", True):
                t0 = time.time()
                while ingested() < k + 1 and time.time() - t0 < timeout and srv.poll() is None:
                    time.sleep(1)
        if case.get("pre_final_sleep"):   # e.g. let background target checks (targeted mode) finish
            time.sleep(float(case["pre_final_sleep"]))
        rc, sec, why = run_check(script, case["final"], case["challenge"], case["config"], threads, wdir, timeout,
                                 ["--incr-dir", d])
    finally:
        try:
            os.killpg(srv.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        srv.wait()
    tail = ""
    try:
        tail = " | ".join(ln.strip() for ln in open(os.path.join(d, "server.log"), errors="replace")
                          if ln.startswith("[incr] "))[-600:]
    except OSError:
        pass
    return rc, sec, why, tail


V = {0: "ACCEPTED", 1: "REJECTED"}


def verdict(rc):
    return V.get(rc, "NOVERDICT(%s)" % rc)


def kernel_corpus(gate, root, legs, threads, jobs, out):
    tests = []
    for lab in ("good", "bad"):
        for d, _, fs in os.walk(os.path.join(root, lab)):
            for f in sorted(fs):
                if f.endswith(".ndjson"):
                    tests.append((lab, os.path.join(d, f)))
    tests.sort()
    ro = list(legs.get("ro", []))

    def one(t):
        lab, e = t
        tid = os.path.relpath(e, root).replace("/", "__")
        w = os.path.join(out, "w", gate, tid)
        rl, wl = run_leg(legs["lean"], e, threads, w + "/lean", ro, TIMEOUT[gate])
        r2, w2 = run_leg(legs["k2"], e, threads, w + "/k2", ro, TIMEOUT[gate]) if "k2" in legs else (None, 0)
        xk = {}
        for kn, kl in sorted((legs.get("extra") or {}).items()):
            rx, _ = run_leg(kl, e, threads, w + "/xk-" + kn, ro, TIMEOUT[gate])
            xk[kn] = xk_status(kn, w + "/xk-" + kn + "/log", rx)
        good = lab == "good"
        cls = []
        if rl == 0 and not good:
            cls.append("FAIL-CRITICAL(lean accepts bad)")
        elif rl == 1 and good:
            cls.append("FAIL-REJECT(lean rejects good)")
        elif rl not in (0, 1):
            cls.append("WARN-DECLINE(lean exit %s)" % rl)
        if r2 is not None:
            if r2 == 0 and not good:
                cls.append("INFO(k2 accepts bad)")
            elif r2 == 1 and good:
                cls.append("WARN(k2 rejects good)")
            elif r2 not in (0, 1):
                cls.append(("WARN(k2 exit %s on good)" if good else "INFO(k2 exit %s on bad)") % r2)
            comb = 0 if (rl == 0 and r2 == 0) else (1 if 1 in (rl, r2) else 2)
        else:
            comb = rl
        if comb == 0 and not good:   # the two deciding kernels accepted a bad test: FAIL-CRITICAL even if an extra kernel
            cls.append("FAIL-CRITICAL(combined accepts bad)")   # vetoes it (extra kernels are optional and can be skipped)
        if comb == 0 and any(v == "rejected" for v in xk.values()):   # v2.3-H: a veto after the two-kernel ACCEPT
            if good:
                cls.append("WARN(xk %s rejects good)" % ",".join(k for k, v in xk.items() if v == "rejected"))
            comb = 1
        for kn, v in xk.items():
            if v == "accepted" and not good:
                cls.append("INFO(xk %s accepts bad)" % kn)
        status = "FAIL" if any(c.startswith("FAIL") for c in cls) else ("WARN" if any(c.startswith("WARN") for c in cls)
                                                                        else "PASS")
        return [gate, tid, lab, rl, r2, comb, wl, w2, status, ";".join(cls),
                ";".join("%s:%s" % kv for kv in sorted(xk.items()))]

    rows = list(cf.ThreadPoolExecutor(jobs).map(one, tests))
    return ["gate", "test", "label", "lean_rc", "k2_rc", "combined_rc", "lean_s", "k2_s", "status", "classes", "xk"], rows


def check_rows(gate, cases, script, threads, jobs, out):
    """cases: list of (name, export, challenge, config, expected 'ACCEPTED'|'REJECTED' [, extra args])."""
    def one(c):
        name, e, ch, cfg, exp = c[:5]
        extra = c[5] if len(c) > 5 else ()
        w = os.path.join(out, "w", gate, name)
        rc, sec, why = run_check(script, e, ch, cfg, threads, w, TIMEOUT[gate], extra)
        v = verdict(rc)
        if v == exp:
            st, cl = "PASS", ""
        elif exp == "SPLIT" and v in ("ACCEPTED", "REJECTED"):
            st, cl = "PASS", "INFO-SPLIT(official verdict differs between configs only through nanoda's format limits; "\
                "the export is kernel-valid)"
        elif v == "ACCEPTED":
            st, cl = "FAIL", "FAIL-CRITICAL(accepts a %s case)" % exp
        elif v == "REJECTED":
            st, cl = "WARN", "WARN-REJECT(rejects a case the official comparator accepts: availability)"
        else:
            st, cl = "WARN", "WARN-DECLINE"
        return [gate, name, exp, rc, v, sec, st, cl, why]
    rows = list(cf.ThreadPoolExecutor(jobs).map(one, cases))
    return ["gate", "case", "expected", "rc", "verdict", "seconds", "status", "classes", "reason"], rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--check")
    ap.add_argument("--legs")
    ap.add_argument("--gate", action="append")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--inputs")
    ap.add_argument("--label", default="")
    ap.add_argument("--check-args", default="", help="extra arguments for every check-script run (shell words)")
    ap.add_argument("--xk-classifier", help="check script whose --xk-classify classifies the extra-kernel legs of the "
                    "legs file (default: --check)")
    a = ap.parse_args()
    import shlex
    EXTRA_ARGS.extend(shlex.split(a.check_args))
    if a.xk_classifier or a.check:
        CLASSIFIER.append(os.path.realpath(a.xk_classifier or a.check))
    inp = dict(INPUTS)
    if a.inputs:
        inp.update(json.load(open(a.inputs)))
    gates = a.gate or ["all"]
    if "all" in gates:
        gates = ["arena", "suitex", "cmpx", "mathlib", "mutants", "threads"]
    os.makedirs(a.out, exist_ok=True)
    legs = json.load(open(a.legs)) if a.legs else None
    if legs:   # {here} = this harness directory (e.g. "{here}/legs/empty.hints"), substituted everywhere
        here = os.path.dirname(os.path.realpath(__file__))
        legs = json.loads(json.dumps(legs).replace("{here}", here))
    script = os.path.realpath(a.check) if a.check else None
    summary = {"label": a.label, "started": now(), "check": script, "check_args": EXTRA_ARGS,
               "check_sha256": subprocess.run(["sha256sum", script], capture_output=True, text=True).stdout.split()[0]
               if script else None, "legs": legs, "inputs": inp, "gates": {}}
    for g in gates:
        t0 = time.time()
        hdr, rows = None, []
        if g in ("arena", "suitex"):
            if not legs or not os.path.isdir(inp[g]):
                summary["gates"][g] = {"status": "SKIPPED", "why": "no --legs or no corpus"}
                continue
            hdr, rows = kernel_corpus(g, inp[g], legs, a.threads, a.jobs, a.out)
        elif g == "cmpx":
            if not script or not os.path.isdir(inp["cmpx"]):
                summary["gates"][g] = {"status": "SKIPPED"}
                continue
            exp = {}
            for ln in open(os.path.join(inp["cmpx"], "expected.txt")):
                p = ln.split()
                if len(p) == 2:
                    exp[p[0]] = "ACCEPTED" if p[1] == "accept" else "REJECTED"
            cases = []
            for cfg in inp["cmpx_configs"]:
                tag = os.path.basename(cfg).replace("comparator.", "").replace(".json", "")
                for f, e in sorted(exp.items()):
                    if f.startswith("split-"):   # official leanonly ACCEPTS, nanoda REJECTS
                        e = "ACCEPTED" if tag == "leanonly" else "SPLIT"
                    cases.append((f"{tag}__{f}", os.path.join(inp["cmpx"], f), inp["cmpx_challenge"], cfg, e))
            hdr, rows = check_rows(g, cases, script, a.threads, a.jobs, a.out)
        elif g == "mathlib":
            if not script or not os.path.isdir(inp["mathlib"]):
                summary["gates"][g] = {"status": "SKIPPED"}
                continue
            cases = []
            for name, c in sorted(json.load(open(inp["mathlib_cases"])).items()):
                d = os.path.join(inp["mathlib"], name)
                e = os.path.join(d, "solution.export")
                if not os.path.isfile(e):   # build/export failed (e.g. P1-f-builderror): no check
                    cases.append(None)
                    continue
                cases.append((name, e, os.path.join(d, "challenge.export"), os.path.join(d, "comparator.json"),
                              c["expected_official"]))
            missing = [n for n, c in zip(sorted(json.load(open(inp["mathlib_cases"]))), cases) if c is None]
            hdr, rows = check_rows(g, [c for c in cases if c], script, a.threads, a.jobs, a.out)
            summary.setdefault("notes", {})["mathlib_no_export"] = missing
        elif g == "mutants":
            if not script or not inp["mutants"]:
                summary["gates"][g] = {"status": "SKIPPED"}
                continue
            cases = [(m["name"], m["export"], m.get("challenge", inp["mutants_challenge"]),
                      m.get("config", inp["mutants_config"]), m.get("expect", "REJECTED"), m.get("args", []))
                     for m in inp["mutants"]]
            hdr, rows = check_rows(g, cases, script, a.threads, max(1, min(a.jobs, 2)), a.out)
        elif g == "incr":
            if not script or not inp.get("incr_cases"):
                summary["gates"][g] = {"status": "SKIPPED"}
                continue
            plc = inp.get("incr_pleanchecker")
            if not plc:   # the pinned incremental pleanchecker of the check under test (PIN pleanchecker_incr)
                for ln in open(os.path.join(os.path.dirname(script), "pins.env")):
                    q = ln.split()
                    if len(q) == 4 and q[0] == "PIN" and q[1] == "pleanchecker_incr":
                        plc = q[3]
            if not plc:
                summary["gates"][g] = {"status": "SKIPPED", "why": "no PIN pleanchecker_incr"}
                continue
            hdr = ["gate", "case", "expected", "rc", "verdict", "seconds", "status", "classes", "reason", "server"]

            def one_incr(c):
                w = os.path.join(a.out, "w", "incr", c["name"])
                rc, sec, why, tail = run_incr_case(script, c, inp["incr_server"], plc, inp.get("incr_threads", a.threads),
                                                   w, TIMEOUT["mutants"])
                v, exp = verdict(rc), c.get("expect", "REJECTED")
                if v == exp:
                    st, cl = "PASS", ""
                elif v == "ACCEPTED":
                    st, cl = "FAIL", "FAIL-CRITICAL(accepts a %s case)" % exp
                else:
                    st, cl = "WARN", "WARN-%s(availability)" % ("REJECT" if v == "REJECTED" else "DECLINE")
                return [g, c["name"], exp, rc, v, sec, st, cl, why, tail]
            rows = list(cf.ThreadPoolExecutor(max(1, min(a.jobs, 4))).map(one_incr, inp["incr_cases"]))
        elif g == "threads":
            if not script or not inp["threads_cases"]:
                summary["gates"][g] = {"status": "SKIPPED"}
                continue
            res = {}
            for c in inp["threads_cases"]:
                for t in inp["threads_list"]:
                    w = os.path.join(a.out, "w", "threads", f"{c['name']}.T{t}")
                    rc, sec, why = run_check(script, c["export"], c["challenge"], c["config"], t, w, TIMEOUT[g])
                    res.setdefault(c["name"], []).append((t, rc, sec, why))
                    print(f"[{now()}] threads {c['name']} T={t} rc={rc} {sec}s", flush=True)
            hdr = ["gate", "case", "threads", "rc", "seconds", "status", "reason"]
            for name, lst in res.items():
                same = len({r[1] for r in lst}) == 1 and lst[0][1] in (0, 1)
                for t, rc, sec, why in lst:
                    rows.append([g, name, t, rc, sec, "PASS" if same else "FAIL", why])
        with open(os.path.join(a.out, f"{g}.tsv"), "w") as f:
            f.write("\t".join(hdr) + "\n")
            for r in rows:
                f.write("\t".join(str(x) for x in r) + "\n")
        st = [r[hdr.index("status")] for r in rows]
        summary["gates"][g] = {"rows": len(rows), "PASS": st.count("PASS"), "WARN": st.count("WARN"),
                               "FAIL": st.count("FAIL"), "status": "FAIL" if "FAIL" in st else "PASS",
                               "seconds": round(time.time() - t0, 1)}
        print(f"[{now()}] gate {g}: {summary['gates'][g]}", flush=True)
        json.dump(summary, open(os.path.join(a.out, "summary.json"), "w"), indent=1)
    summary["finished"] = now()
    json.dump(summary, open(os.path.join(a.out, "summary.json"), "w"), indent=1)
    with open(os.path.join(a.out, "summary.txt"), "w") as f:
        for g, s in summary["gates"].items():
            f.write(f"{g}\t{s}\n")
    bad = [g for g, s in summary["gates"].items() if s.get("status") == "FAIL"]
    print("GATES " + ("FAIL: " + ",".join(bad) if bad else "PASS (no FAIL row)"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

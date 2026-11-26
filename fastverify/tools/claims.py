#!/usr/bin/python3 -I
"""tools/claims.py — verify MANY comparator claims of ONE project with ONE build (untrusted driver, additive).

  claims.py pin    CHALLENGES_ROOT WS GIVEN_ROOT [CLAIM...]
  claims.py verify PROJECT GIVEN_ROOT WS OUT [--threads N] [--claims C1,C2,...] [-- EXTRA_FASTVERIFY_ARGS...]

A repository of AI-generated proofs often ships several comparator claims (openai/ten-proofs: 12 ComparatorChallenges/*.json;
an AI lab's release; a library's main theorems). Verifying them one by one with bin/fastverify rebuilds the project per claim.

pin    : for every claim directory CHALLENGES_ROOT/<claim>/ (clean challenge: comparator.json, lean-toolchain, lakefile,
         manifest, challenge module source) the OFFICIAL challenge export is produced exactly as bin/fastverify's prepare
         step does it (build/official-build.sh = official sandboxed lake build with the project's official toolchain, then
         the release's official exporter in bwrap with LEAN_ABORT_ON_PANIC=1 and the target list Lake's 4.36 comparator
         derives) into GIVEN_ROOT/<claim>/ (+ challenge.export.sha256). Identical bytes to a reference run's challenge export.
verify : 1. bin/fastverify PROJECT GIVEN_ROOT/<C1> OUT/<C1> --preset sound --challenge-sha256 .. --keep-work: the project's
            default targets are built ONCE (untrusted, every solution module in parallel), claim C1 is exported + judged;
         2. every other claim Ck: its export targets are exported from the KEPT build tree by the release's OFFICIAL exporter
            (config/components.json) in bwrap (tree read-only, dependency packages bound read-only, no network,
            LEAN_ABORT_ON_PANIC=1), then judged by `bin/fastverify PROJECT GIVEN_ROOT/<Ck> OUT/<Ck> --from-export EXPORT
            --preset sound --challenge-sha256 ..` (export-in: private copy; the unchanged trusted check CS + the
            cross-version gate). An export that fails gives that claim NO verdict here (rerun it alone).
         OUT/claims.tsv: claim, verdict, exit, seconds (C1 includes the build), export seconds.
Why sound: every ACCEPTED is CS's acceptance of an export against that claim's own pinned official challenge export; the
shared build tree and the per-claim export are untrusted exactly as in a single run (wrong/stale -> rejected or no verdict).
For rewards: NO verdict counts as REJECTED."""
import json, os, shutil, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
FV = os.path.join(ROOT, "bin", "fastverify")
PRIMS = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land",
         "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
         "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam"]   # = lib/fastverify.py


def targets(cfg):
    axs = list(cfg["permitted_axioms"])
    b = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in axs else []
    return b + list(cfg["theorem_names"]) + axs + PRIMS + list(cfg.get("definition_names") or [])


def toolchain(d):
    cfg = json.load(open(os.path.join(ROOT, "config", "components.json")))
    t = cfg["lean_toolchains"][open(os.path.join(d, "lean-toolchain")).read().strip()]
    return t["prefix"], t["official_lean4export"]["path"], t["official_lean4export"]["sha256"]


def sha256(p):
    return subprocess.run(["sha256sum", p], capture_output=True, text=True).stdout.split()[0]


def export(proj, tcp, exp, binds, lean_path, module, tg, out):
    argv = ["/usr/bin/bwrap", "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp", "--dir",
            "/tmp/home", "--tmpfs", "/run", "--dev", "/dev", "--proc", "/proc", "--clearenv", "--ro-bind", tcp, tcp,
            "--ro-bind", proj, proj, "--ro-bind", exp, exp]
    for src, dst in binds:
        argv += ["--ro-bind", src, dst]
    for k, v in {"PATH": f"{tcp}/bin:/usr/bin:/bin", "HOME": "/tmp/home", "LANG": "C.UTF-8", "LEAN_PATH": lean_path,
                 "LEAN_ABORT_ON_PANIC": "1"}.items():
        argv += ["--setenv", k, v]
    argv += ["--unshare-all", "--die-with-parent", "--new-session", "--chdir", proj, "--", exp, module, "--"] + tg
    with open(out, "wb") as f, open(out + ".err", "wb") as ef:
        return subprocess.run(argv, stdout=f, stderr=ef, env={}).returncode


def pin(a):
    CR, WS, GR = a[:3]
    claims = a[3:] or sorted(os.listdir(CR))
    bad = 0
    for c in claims:
        t0 = time.time()
        cd = os.path.join(CR, c)
        cfg = json.load(open(os.path.join(cd, "comparator.json")))
        tcp, exp, esha = toolchain(cd)
        if sha256(exp) != esha:
            print(c, "official exporter sha256 mismatch"); bad += 1; continue
        w = tempfile.mkdtemp(prefix="claims-pin.")
        work = os.path.join(w, "challenge")
        shutil.copytree(cd, work, symlinks=True, ignore=shutil.ignore_patterns(".lake"))
        lp = os.path.join(w, "lean_path")
        r = subprocess.run([os.path.join(ROOT, "build", "official-build.sh"), work, WS, tcp, "--lean-path-out", lp, "--log",
                            os.path.join(w, "log")], capture_output=True, text=True)
        if r.returncode != 0:
            print(c, "challenge does not build officially", r.returncode); bad += 1; continue
        m = subprocess.run(["/usr/bin/python3", "-I", os.path.join(ROOT, "lib", "manifest.py"), work, WS],
                           capture_output=True, text=True)
        if m.returncode != 0:
            print(c, "challenge dependencies:", m.stderr.strip()[-200:]); bad += 1; continue
        binds = [tuple(l.split("\t")) for l in m.stdout.splitlines() if l]
        g = os.path.join(GR, c)
        shutil.rmtree(g, ignore_errors=True)
        shutil.copytree(cd, g, symlinks=True, ignore=shutil.ignore_patterns(".lake"))
        ce = os.path.join(g, "challenge.export")
        if export(work, tcp, exp, binds, open(lp).read().strip(), cfg["challenge_module"], targets(cfg), ce) != 0:
            print(c, "challenge cannot be exported officially"); bad += 1; os.unlink(ce); continue
        os.unlink(ce + ".err")
        s = sha256(ce)
        open(ce + ".sha256", "w").write(s + "\n")
        # the comparator config pin, required by bin/fastverify's sound mode together with the challenge pin
        open(os.path.join(g, "comparator.json.sha256"), "w").write(sha256(os.path.join(g, "comparator.json")) + "\n")
        shutil.rmtree(w, ignore_errors=True)
        print(c, "pinned", s[:16], round(time.time() - t0, 1), "s", flush=True)
    return 1 if bad else 0


def verify(a):
    extra = []
    if "--" in a:
        i = a.index("--"); extra = a[i + 1:]; a = a[:i]
    # forwarded options: build / check TUNING only (exact names, also --opt=VALUE); anything that
    # could change the judged solution or the challenge identity (--from-export, --export, pins, preset, checks, ...) is refused
    allow = {  # pure tuning options only (cannot change the solution source or the challenge identity)
        "--threads", "--build", "--unsafe", "--export-dir", "--keep-work", "--no-build-fallback",
        "--no-integrity-cache", "--build-cache", "--overlap", "--overlap-targeted", "--overlap-targets", "--extra-kernel",
        "--require-kernel", "--skip-extra-kernel", "--check-hints", "--check-hide", "--official-timeout", "--parallel-checks",
        "--sequential-checks", "--no-confirm-build-failure", "--confirm-build-failure-full", "--confirm-reject", "--no-confirm-reject", "--reference-export",
        "--require-sorried-holes", "--preflight-only"}
    for x in extra:
        if x.startswith("-") and x.split("=", 1)[0] not in allow:
            print(f"claims.py: forwarded option {x.split('=', 1)[0]} is not a tuning option: refused (allowed: "
                  f"{' '.join(sorted(allow))})", file=sys.stderr)
            return 2
    opt = {"--threads": str(os.cpu_count() or 8), "--claims": ""}
    pos = []
    i = 0
    while i < len(a):
        if a[i] in opt:
            opt[a[i]] = a[i + 1]; i += 2
        else:
            pos.append(a[i]); i += 1
    P, G, WS, OUT = pos
    claims = opt["--claims"].split(",") if opt["--claims"] else sorted(os.listdir(G))
    tcp, exp, esha = toolchain(P)
    os.makedirs(OUT, exist_ok=True)
    env = {"HOME": os.environ.get("HOME", "/tmp"), "PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}
    rows = []

    def fv(c, more):
        g = os.path.join(G, c)
        sha = open(os.path.join(g, "challenge.export.sha256")).read().split()[0]
        # written by `pin` (a root pinned before has none: re-run pin; bin/fastverify refuses without the pin)
        cpf = os.path.join(g, "comparator.json.sha256")
        cpin = ["--comparator-sha256", open(cpf).read().split()[0]] if os.path.isfile(cpf) else []
        o = os.path.join(OUT, c)
        shutil.rmtree(o, ignore_errors=True)
        t0 = time.time()
        with open(o + ".log", "w") as lf:
            r = subprocess.run([FV, P, g, o, "--preset", "sound", "--threads", opt["--threads"], "--packages", WS,
                                "--challenge-sha256", sha] + cpin + more + extra, stdout=lf, stderr=subprocess.STDOUT, env=env)
        try:
            v = json.load(open(os.path.join(o, "result.json"))).get("verdict")
        except Exception:
            v = None
        return v, r.returncode, round(time.time() - t0, 2)

    first = claims[0]
    v, rc, sec = fv(first, ["--keep-work"])
    rows.append((first, v, rc, sec, "-"))
    print(first, v, rc, sec, flush=True)
    W = os.path.join(OUT, first)
    proj = os.path.join(W, "work", "proj")
    if not os.path.isfile(os.path.join(W, "log", "lean_path.txt")) or not os.path.isdir(proj):
        print("first claim left no build tree (build failed?): the other claims get no verdict here")
        rows += [(c, "NO-VERDICT(no build)", 2, 0, "-") for c in claims[1:]]
    else:
        lp = open(os.path.join(W, "log", "lean_path.txt")).read().strip()
        binds = [tuple(l.rstrip("\n").split("\t")) for l in open(os.path.join(W, "log", "binds.tsv")) if l.strip()]
        if sha256(exp) != esha:
            sys.exit("official exporter sha256 mismatch")
        for c in claims[1:]:
            cfg = json.load(open(os.path.join(G, c, "comparator.json")))
            ex = os.path.join(OUT, c + ".export")
            t0 = time.time()
            erc = export(proj, tcp, exp, binds, lp, cfg["solution_module"], targets(cfg), ex)
            esec = round(time.time() - t0, 2)
            if erc != 0:
                rows.append((c, "NO-VERDICT(export failed)", 2, esec, esec)); print(c, "export failed", flush=True)
                continue
            v, rc, sec = fv(c, ["--from-export", ex])
            rows.append((c, v, rc, round(sec + esec, 2), esec))
            print(c, v, rc, sec, esec, flush=True)
            for f in (ex, ex + ".err"):
                if os.path.exists(f):
                    os.unlink(f)
    with open(os.path.join(OUT, "claims.tsv"), "w") as f:
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    return 0 if all(r[1] in ("ACCEPTED", "REJECTED") for r in rows) else 2


if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] not in ("pin", "verify"):
        sys.stderr.write(__doc__); sys.exit(2)
    sys.exit(pin(sys.argv[2:]) if sys.argv[1] == "pin" else verify(sys.argv[2:]))

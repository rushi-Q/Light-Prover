#!/usr/bin/python3 -I
"""tests/frontier-adversarial/test.py [WORKDIR] [--jobs N] [--threads T] [--oracle DIR] [--plain PATH]

Adversarial regression test of the CONDITIONAL verdict modulo a sorry frontier (check/frontier/check-frontier.sh,
"sound" below), independent of tests/frontier-conditional:

 1. 26 source cases (cases.py: core-only Lean 4.33.1 challenges/solutions with sorry patterns: frontier lemmas, chains,
    universe-polymorphic, two targets; hidden sorries in definitions / statements / targets / proof obligations /
    Prop-class instances; project axiom; native_decide (Lean 4.33: an auxiliary AXIOM, not ofReduceBool); changed
    statement; kernel-invalid lemma under debug.skipKernelTC) are built with the OFFICIAL Lean 4.33.1 and exported with
    the OFFICIAL lean4export (the comparator's export targets), each inside bwrap without network;
 2. 13 crafted export mutants (xmut.py: canonical forms under mdata/beta/let/beta-to-argument, sorry under a theorem
    application, non-Prop theorem unused/used, fake `Foo.sorryAx` axiom, a frontier name with newlines and fake
    success/JSON lines, duplicate sorryAx, sorry-typed frontier statement, unused bad lemma, canonical target);
 3. every input through the PUBLISHED check/frontier/check-frontier.sh; verdict class + frontier compared with the
    expectation: `REJ` rows (soundness: must be REJECTED or no verdict, never exit 0/3), `OK:<names>` rows (exact
    verdict + frontier), `?` rows (semantic choices / availability, recorded only).
 Optional: --oracle DIR / --plain PATH also run the independent oracle (rewrite + ccmp-frontier) and the
 zero-trusted-change frontier.py ("plain") on the same inputs (3-way differential, diff.py).
Prints PASS/FAIL/INFO rows and `RESULT pass=N fail=M`; exit 0 iff no FAIL. ~2-4 min on a test host (8 jobs).
"""
import json
import os
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.realpath(__file__))
PKG = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import cases as C   # noqa: E402
import xmut         # noqa: E402

PRIMITIVES = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble",
              "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat",
              "List", "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam",
              "outParam"]
# expectation of the published (check-frontier.sh) semantics per source case: REJ = must not be accepted in any form,
# OK:<names> = conditional with exactly this frontier (OK: = plain ACCEPTED or empty frontier), ? = recorded only
EXPECT_SRC = {
    # since prep 114eaea9 (sketch abstraction) a Prop-sorry inside a TARGET or a definition's proof position becomes an
    # open lemma T._fv_sorry_k: f04 / f15 / m11 are design rows (recorded, not judged)
    "f01-basic": "OK:helper", "f02-closed": "OK:", "f03-def-sorry": "REJ", "f04-target-sorried": "?",
    "f05-statement-sorry": "REJ", "f06-nested-have": "?", "f07-unused-sorry": "OK:", "f08-chain": "OK:l1",
    "f09-user-axiom": "REJ", "f10-native-decide": "REJ", "f11-statement-changed": "REJ",
    "f12-challenge-name": "OK:aux_lemma", "f12b-challenge-export-name": "?", "f13-universe": "OK:uhelper",
    "f14-proof-in-def": "OK:", "f15-proof-obligation-sorry": "?", "f16-two-frontier": "OK:a1,a2",
    "f17-ill-typed-with-sorry": "REJ", "f18-sorry-in-instance": "?", "f19-dotted-name": "REJ",
    "f20-private-lemma": "OK:_private.Solution.0.helper", "f21-sketch-let": "SKETCH-LET",
    "f22-sketch-induction": "SKETCH-OK", "f23-sketch-cases-exists": "SKETCH-OK", "f24-sketch-universe": "SKETCH-OK",
    "f25-sketch-chain": "SKETCH-OK",
}
EXPECT_MUT = {   # xmut ids -> expectation (overrides the generator's column for the published semantics)
    "m01-mdata-wrap": "?",          # gruszka declines an mdata node with empty data (crafted): no verdict
    "m04-myid-wrap": "?", "m04b-beta-to-arg": "?", "m07-name-injection": "?", "m11-target-canonical": "?",
}


def comps_cfg(cfg):
    axs = cfg["permitted_axioms"]
    builtin = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in axs else []
    return builtin + cfg["theorem_names"] + axs + PRIMITIVES + list(cfg.get("definition_names") or [])


def sandbox(work, argv, env):
    return (["env", "-i", "/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session",
             "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp", "--dev", "/dev",
             "--proc", "/proc", "--ro-bind", env["T33"], env["T33"], "--ro-bind", env["EXP"], env["EXP"],
             "--bind", work, work, "--chdir", work, "--setenv", "PATH", env["T33"] + "/bin:/usr/bin:/bin",
             "--setenv", "LEAN_PATH", env["T33"] + "/lib/lean:" + work, "--setenv", "LEAN_ABORT_ON_PANIC", "1",
             "--setenv", "HOME", work] + argv)


def build_export(d, module, targets, env):
    """official lean 4.33.1 -o + official lean4export (sandboxed); returns the export path or None"""
    r = subprocess.run(sandbox(d, ["lean", "-o", module + ".olean", module + ".lean"], env), capture_output=True)
    if r.returncode != 0:
        open(os.path.join(d, "build.log"), "wb").write(r.stdout + r.stderr)
        return None
    out = os.path.join(d, module + ".export")
    with open(out, "wb") as f:
        r = subprocess.run(sandbox(d, [env["EXP"], module, "--"] + targets, env), stdout=f, stderr=subprocess.PIPE)
    if r.returncode != 0:
        open(os.path.join(d, "export.log"), "wb").write(r.stderr)
        return None
    return out


def norm(j, rc):
    v = j.get("verdict")
    if rc == 0 and v == "ACCEPTED":
        return ("OK", ())
    if rc == 3 and v == "CONDITIONAL":
        return ("OK", tuple(sorted(e["name"] if isinstance(e, dict) else e for e in j.get("frontier") or [])))
    if rc == 1 and v == "REJECTED":
        return ("REJ", ())
    if rc in (0, 3):
        return ("OK?", ())      # an acceptance-like exit code without the matching verdict field: treated as OK
    return ("NOV", ())


def main(argv):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("work", nargs="?")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--oracle", help="oracle tools/frontier dir (fv-frontier) for a 3-way differential")
    ap.add_argument("--plain", help="zero-trusted-change frontier.py for a 3-way differential")
    ap.add_argument("--e2e-preset", default="sound", help="preset for --e2e (sound | sound-auto)")
    ap.add_argument("--e2e", action="store_true", help="also run key source cases through bin/fastverify --preset sound "
                    "--modulo-frontier (the user-facing entry point: exit 0/1/3, verdict, frontier)")
    ap.add_argument("--project-scale", metavar="RHMID", nargs="?", const="/scratch/bench-inputs/rh-mid",
                    help="also the project-scale case: rh-mid (RHMID/ref/solution.export + RHMID/challenge) "
                         "with 1 project theorem set to sorry (mkfrontier.py); expected CONDITIONAL with that lemma")
    a = ap.parse_args(argv)
    cfgc = json.load(open(os.path.join(PKG, "config", "components.json")))
    lt = cfgc["lean_toolchains"]["leanprover/lean4:v4.33.1"]
    env = {"T33": lt["prefix"], "EXP": lt["official_lean4export"]["path"]}
    work = a.work or os.path.join((os.environ.get("SCRATCH") or os.environ.get("TMPDIR") or "/tmp"), os.environ.get("USER", "u") + "-frontier-adversarial")
    if os.path.isdir(work):
        shutil.rmtree(work)
    os.makedirs(work)
    t0 = time.time()
    # 1. source cases
    C.main(os.path.join(work, "corpus"))
    rows = []

    def build_case(cid):
        base = os.path.join(work, "corpus")
        cfg = json.load(open(os.path.join(base, "challenges", cid, "comparator.json")))
        tg = comps_cfg(cfg)
        ce = build_export(os.path.join(base, "challenges", cid), "Challenge", tg, env)
        se = build_export(os.path.join(base, "projects", cid), "Solution", tg, env)
        return cid, ce, se, os.path.join(base, "challenges", cid, "comparator.json")

    with ThreadPoolExecutor(a.jobs) as pool:
        built = list(pool.map(build_case, sorted(C.CASES)))
    runs = os.path.join(work, "runs")
    for cid, ce, se, cfg in built:
        if ce is None or se is None:
            rows.append(("BUILD", cid, None, None, cfg, EXPECT_SRC.get(cid, "?")))
            continue
        # xmut expects BASE/<case>/plain/{solution,challenge}.export
        pd = os.path.join(runs, cid, "plain")
        os.makedirs(pd, exist_ok=True)
        shutil.copy(se, os.path.join(pd, "solution.export"))
        shutil.copy(ce, os.path.join(pd, "challenge.export"))
        rows.append(("SRC", cid, os.path.join(pd, "solution.export"), os.path.join(pd, "challenge.export"), cfg,
                     EXPECT_SRC.get(cid, "?")))
    # 2. crafted mutants (on the official exports of f01)
    mdir = os.path.join(work, "mutants")
    xmut.main(runs, os.path.join(work, "corpus"), mdir)
    for ln in open(os.path.join(mdir, "cases.tsv")):
        mid, ex, ch, cf, ee = ln.rstrip("\n").split("\t")
        e = EXPECT_MUT.get(mid, "REJ" if ee == "REJECTED" else ee)
        rows.append(("MUT", mid, ex, ch, cf, e))
    # 3. the published check-frontier.sh
    cf_sh = os.path.join(PKG, "check", "frontier", "check-frontier.sh")

    def judge(r):
        kind, cid, ex, ch, cfg, exp = r
        if ex is None:
            return r + (("NOV", ()), "build/export failed", 0.0)
        od = os.path.join(work, "judge", cid)
        os.makedirs(od, exist_ok=True)
        t = time.time()
        p = subprocess.run([cf_sh, ex, ch, cfg, "--threads", str(a.threads if kind != "PROJ" else max(a.threads, 16)),
                        "--json", os.path.join(od, "r.json"),
                            "--log", os.path.join(od, "r.log")], capture_output=True, text=True)
        try:
            j = json.load(open(os.path.join(od, "r.json")))
        except Exception:
            j = {}
        why = (j.get("reason") or "")[:240]
        if exp in ("SKETCH-LET", "SKETCH-OK"):
            why = json.dumps([(e.get("name"), e.get("statement") or e.get("type")) for e in (j.get("frontier") or [])
                              if isinstance(e, dict)])[:400]
        return r + (norm(j, p.returncode), why, round(time.time() - t, 2))

    with ThreadPoolExecutor(a.jobs) as pool:
        res = list(pool.map(judge, rows))
    if a.project_scale:
        rm = a.project_scale
        pe = os.path.join(work, "rhmid-k1.export")
        r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "mkfrontier.py"),
                            os.path.join(rm, "ref", "solution.export"), os.path.join(rm, "challenge", "comparator.json"),
                            pe, "1", "--seed", "7", "--exclude-export", os.path.join(rm, "challenge", "challenge.export"),
                            "--prefix", "GlobalTheory.,Formalism.,GroundTheory."], capture_output=True, text=True)
        nm = open(pe + ".names").read().split()[0] if r.returncode == 0 else "?"
        row = ("PROJ", "rhmid-k1", pe, os.path.join(rm, "challenge", "challenge.export"),
               os.path.join(rm, "challenge", "comparator.json"), "OK:" + nm)
        res.append(judge(row) if r.returncode == 0 else row + (("NOV", ()), "generator failed", 0.0))
    if a.e2e:
        E2E = {"f01-basic": (3, "CONDITIONAL", ["helper"]), "f02-closed": (0, "ACCEPTED", []),
               "f03-def-sorry": (1, "REJECTED", None), "f06-nested-have": (3, "CONDITIONAL", ["helper"]),
               "f10-native-decide": (1, "REJECTED", None), "f11-statement-changed": (1, "REJECTED", None),
               "f16-two-frontier": (3, "CONDITIONAL", ["a1", "a2"]),
               "f20-private-lemma": (3, "CONDITIONAL", ["_private.Solution.0.helper"])}
        fvbin = os.path.join(PKG, "bin", "fastverify")

        def e2e(cid):
            base = os.path.join(work, "corpus")
            od = os.path.join(work, "e2e", cid)
            os.makedirs(os.path.dirname(od), exist_ok=True)
            t = time.time()
            p = subprocess.run(["env", "-i", "HOME=" + os.environ.get("HOME", "/tmp"), "PATH=/usr/bin:/bin", "LANG=C.UTF-8",
                                fvbin, os.path.join(base, "projects", cid), os.path.join(base, "challenges", cid), od,
                                "--preset", a.e2e_preset, "--modulo-frontier", "--threads", str(max(4, a.threads))],
                               capture_output=True, text=True)
            try:
                r = json.load(open(os.path.join(od, "result.json")))
            except Exception:
                r = {}
            names = sorted(e.get("name") for e in ((r.get("frontier") or {}).get("frontier") or []) if isinstance(e, dict))
            return cid, p.returncode, r.get("verdict"), names, round(time.time() - t, 1), (r.get("verdict_basis") or "")[:200]

        with ThreadPoolExecutor(max(1, a.jobs // 2)) as pool:
            for cid, rc, v, names, sec, why in pool.map(e2e, sorted(E2E)):
                erc, ev, en = E2E[cid]
                ok = rc == erc and v == ev and (en is None or names == sorted(en))
                tag = "FAIL CRITICAL" if (ev == "REJECTED" and rc in (0, 3)) else ("PASS" if ok else "FAIL")
                res.append(("E2E", cid, None, None, None, f"rc={erc} {ev} {en}", ("E2E", ()),
                            f"{tag}|rc={rc} verdict={v} frontier={names} {why}", sec))
    npass = nfail = 0
    out_rows = []
    for kind, cid, ex, ch, cfg, exp, got, why, sec in res:
        g = f"{got[0]}{list(got[1])}"
        if kind == "E2E":
            tag, detail = why.split("|", 1)
            if tag == "PASS":
                npass += 1
            else:
                nfail += 1
            line = f"{tag} E2E {cid}: expect {exp} got {detail} ({sec}s)"
            out_rows.append(line)
            print(line)
            continue
        if exp == "SKETCH-OK":   # availability of sketch verification: a CONDITIONAL verdict is expected
            ok = got[0] == "OK" and len(got[1]) >= 1
            tag = "PASS" if ok else "FAIL"
        elif exp == "SKETCH-LET":
            # acceptable: REJECTED, or CONDITIONAL whose open lemma keeps `let n := m + 0` instead of quantifying the
            # let-bound n (fixed in prep bfb07011: an unrelated, possibly false subgoal before the fix)
            ok = got[0] in ("REJ", "NOV") or (got[0] == "OK" and "forall (n : Nat)" not in why and "let n " in why)
            tag = "PASS" if ok else "FAIL"
        elif exp == "REJ":
            ok = got[0] in ("REJ", "NOV")
            tag = "PASS" if ok else "FAIL CRITICAL"
        elif exp == "?":
            ok, tag = True, "INFO"
        else:
            want = ("OK", tuple(sorted(x for x in exp[3:].split(",") if x)))
            ok = got == want
            tag = "PASS" if ok else "FAIL"
        if tag == "INFO":
            pass
        elif ok:
            npass += 1
        else:
            nfail += 1
        line = f"{tag} {kind} {cid}: expect={exp} got={g} ({sec}s)" + ("" if tag == "PASS" else f" reason={why}")
        out_rows.append(line)
        print(line)
    # optional 3-way differential on the same inputs
    if a.oracle or a.plain:
        tsv = os.path.join(work, "all.tsv")
        with open(tsv, "w") as f:
            for kind, cid, ex, ch, cfg, exp in rows:
                if ex is not None:
                    e2 = "REJECTED" if exp == "REJ" else ("?" if exp in ("SKETCH-LET", "SKETCH-OK") else exp)
                    f.write("\t".join([cid, ex, ch, cfg, e2]) + "\n")
        cmd = [sys.executable, "-I", os.path.join(HERE, "diff.py"), tsv, os.path.join(work, "diff"),
               "--jobs", str(a.jobs), "--threads", str(a.threads), "--sound", cf_sh]
        if a.oracle:
            cmd += ["--oracle", os.path.join(a.oracle, "fv-frontier")]
        if a.plain:
            cmd += ["--with-plain"]
        p = subprocess.run(cmd, capture_output=True, text=True)
        print("--- 3-way differential (diff.py) ---")
        print(p.stdout[-6000:])
    print(f"RESULT pass={npass} fail={nfail} ({len(res)} inputs, {round(time.time() - t0, 1)} s)")
    with open(os.path.join(work, "result.txt"), "w") as f:
        f.write("\n".join(out_rows) + f"\nRESULT pass={npass} fail={nfail}\n")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

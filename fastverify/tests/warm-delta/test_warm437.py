#!/usr/bin/python3 -I
"""Live regression test for Lean 4.37.0-rc1 warm delta verification.

Exercises the LIVE default paths end-to-end (no --bins-dir, no --bin override):
  - `check/warm/fvcheckd.py serve --pins check/warm/pins-437.env`
  - `tools/delta-export/export-delta.sh --toolchain $TC437` (auto-selects lean4export-delta-437)
Verifies 10 cases (C1+C7, C2 Tier-2 --exclude, C3 mid-DAG clean importer, C4 mid-DAG drift dual-kernel,
C5 sorry, C6 4.37 'Challenge definition is not sorried', C8 #15101 FakeQuot, C9 B4 --pins
confinement, C10 4.37 --conditional-mode Check A, C11 --hide E2E & adversarial refusal).
"""
import argparse, hashlib, json, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.realpath(__file__))
PKG = os.path.realpath(os.path.join(HERE, "..", ".."))
EXTRACT = "/scratch/fastverify-next/warm/v1/warm-delta-extract"


def find_tc437():
    comp_p = os.path.join(PKG, "config", "components.json")
    if os.path.isfile(comp_p):
        try:
            ent = (json.load(open(comp_p)).get("lean_toolchains") or {}).get("leanprover/lean4:v4.37.0-rc1")
            if isinstance(ent, dict) and ent.get("prefix") and os.path.isdir(ent["prefix"]):
                return os.path.realpath(ent["prefix"])
        except Exception:
            pass
    cand = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.37.0-rc1")
    return os.path.realpath(cand) if os.path.isdir(cand) else ""


def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for ch in iter(lambda: f.read(1 << 20), b""):
            h.update(ch)
    return h.hexdigest()


def run_bwrap(tc, cwd, env_extra, cmd, stdout_file=None):
    bcmd = [
        "/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session",
        "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root",
        "--tmpfs", "/run", "--tmpfs", "/tmp", "--dev", "/dev", "--proc", "/proc", "--clearenv",
        "--ro-bind", tc, tc, "--bind", cwd, cwd,
        "--setenv", "HOME", "/tmp", "--setenv", "TMPDIR", "/tmp", "--setenv", "LANG", "C.UTF-8",
        "--setenv", "PATH", f"{tc}/bin:/usr/bin:/bin",
        "--setenv", "LEAN_ABORT_ON_PANIC", "1",
    ]
    for k, v in env_extra.items():
        bcmd += ["--setenv", k, v]
    bcmd += ["--chdir", cwd, "--", *cmd]
    if stdout_file:
        with open(stdout_file, "wb") as fo:
            p = subprocess.run(bcmd, stdout=fo, stderr=subprocess.PIPE, env={}, timeout=120)
        return p.returncode, p.stderr.decode("utf-8", "replace")
    p = subprocess.run(bcmd, capture_output=True, text=True, env={}, timeout=120)
    return p.returncode, p.stdout + p.stderr


def build_437_proj(tc, proj_dir, mod_files):
    src = os.path.join(proj_dir, "src")
    out = os.path.join(proj_dir, ".lake", "build", "lib", "lean")
    os.makedirs(src, exist_ok=True); os.makedirs(out, exist_ok=True)
    for mod, code in mod_files.items():
        fp = os.path.join(src, mod.replace(".", "/") + ".lean")
        os.makedirs(os.path.dirname(fp), exist_ok=True)
        open(fp, "w", encoding="utf-8").write(code)
    for mod in mod_files:
        rel = mod.replace(".", "/")
        fp = os.path.join(src, rel + ".lean")
        ol = os.path.join(out, rel + ".olean")
        il = os.path.join(out, rel + ".ilean")
        os.makedirs(os.path.dirname(ol), exist_ok=True)
        rc, log = run_bwrap(tc, proj_dir, {"LEAN_PATH": out},
                            [os.path.join(tc, "bin", "lean"), "-R", src, "-o", ol, "-i", il, fp])
        assert rc == 0 and os.path.isfile(ol), f"4.37 build {mod} failed (rc={rc}): {log}"


def official_export_437(tc, proj_dir, mod, targets, out_path):
    lp = os.path.join(proj_dir, ".lake", "build", "lib", "lean")
    rc, err = run_bwrap(tc, proj_dir, {"LEAN_PATH": lp},
                        [os.path.join(tc, "bin", "leanexport"), mod, "--", *targets], stdout_file=out_path)
    assert rc == 0 and os.path.getsize(out_path) > 0, f"official 4.37 leanexport failed: {err}"


def start_warm(fvcheckd, state, chal, base, cfg, pins, extra=None):
    cmd = [
        "/usr/bin/python3", "-I", fvcheckd, "serve",
        "--state", state, "--challenge", chal, "--challenge-sha256", sha256(chal),
        "--config", cfg, "--base", base, "--pins", pins, "--pkgroot", PKG, "--threads", "4",
    ] + (extra or [])
    log_p = state + ".log"
    lf = open(log_p, "w")
    p = subprocess.Popen(cmd, stdout=lf, stderr=subprocess.STDOUT)
    sock = os.path.join(state, "sock")
    for _ in range(300):
        if os.path.exists(sock):
            return p, lf
        if p.poll() is not None:
            lf.close()
            raise RuntimeError(f"daemon exited rc={p.returncode}: {open(log_p).read()}")
        time.sleep(0.1)
    p.kill(); lf.close()
    raise RuntimeError(f"daemon timeout: {open(log_p).read()}")


def stop_warm(fvcheckd, state, p, lf):
    try:
        subprocess.run(["/usr/bin/python3", "-I", fvcheckd, "stop", "--state", state], capture_output=True, timeout=10)
    except Exception:
        pass
    try:
        p.wait(timeout=5)
    except Exception:
        p.kill(); p.wait()
    try:
        lf.close()
    except Exception:
        pass


def query_warm(fvcheckd, state, delta, cfg=None):
    cmd = ["/usr/bin/python3", "-I", fvcheckd, "check-delta", "--state", state, "--delta", delta]
    if cfg:
        cmd += ["--config", cfg]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    j = json.loads(p.stdout.strip().splitlines()[-1])
    return p.returncode, j


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--pkgroot", default=PKG)
    args = ap.parse_args()

    tc = find_tc437()
    pins = os.path.join(args.pkgroot, "check", "warm", "pins-437.env")
    fvcheckd = os.path.join(args.pkgroot, "check", "warm", "fvcheckd.py")
    export_delta_sh = os.path.join(args.pkgroot, "tools", "delta-export", "export-delta.sh")
    if not tc or not os.path.isfile(pins) or not os.path.isfile("/scratch/fastverify-next/warm/07b058aa/ccmp-warm"):
        print("SKIP 4.37 warm test: v4.37.0-rc1 toolchain or /scratch/fastverify-next/warm/v1-437 binaries absent")
        sys.exit(0)

    w = os.path.realpath(args.work)
    shutil.rmtree(w, ignore_errors=True)
    os.makedirs(w)
    passed = failed = 0

    def rec(cid, desc, ok, info=""):
        nonlocal passed, failed
        if ok: passed += 1
        else: failed += 1
        print(f"[{'PASS' if ok else 'FAIL'}] {cid}: {desc}" + (f" ({info})" if info else ""))

    chal_dir = os.path.join(w, "chal_proj")
    base_dir = os.path.join(w, "base_proj")
    base_code = "def baseVal : Nat := 7\n"
    mid_code_ok = "import BaseMod\ntheorem midLem (n : Nat) : n + 0 = n := Nat.add_zero n\n"
    tgt_code_chal = (
        "import MidMod\ndef holeDef : Nat := sorry\ndef unsorriedDef : Nat := 42\n"
        "theorem target1 (n : Nat) : n + 0 = n := by sorry\ntheorem target2 : baseVal = 7 := by sorry\n"
    )
    tgt_code_base = (
        "import MidMod\ndef holeDef : Nat := 123\ndef unsorriedDef : Nat := 42\n"
        "theorem target1 (n : Nat) : n + 0 = n := midLem n\ntheorem target2 : baseVal = 7 := rfl\n"
    )
    build_437_proj(tc, chal_dir, {"BaseMod": base_code, "MidMod": mid_code_ok, "TargetMod": tgt_code_chal})
    build_437_proj(tc, base_dir, {"BaseMod": base_code, "MidMod": mid_code_ok, "TargetMod": tgt_code_base})

    prim = [
        "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
        "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
        "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk",
        "Char", "optParam", "autoParam", "semiOutParam", "outParam",
    ]
    chal_exp = os.path.join(w, "chal.export")
    base_exp = os.path.join(w, "base.export")
    official_export_437(tc, chal_dir, "TargetMod", ["target1", "target2", "holeDef", "unsorriedDef", "propext"] + prim, chal_exp)
    official_export_437(tc, base_dir, "TargetMod", ["target1", "target2", "holeDef", "unsorriedDef", "propext"] + prim, base_exp)

    manifest = os.path.join(w, "base_consts.txt")
    subprocess.run([EXTRACT, "manifest", base_exp, manifest], check=True)

    cfg = os.path.join(w, "cfg.json")
    json.dump({
        "challenge_module": "TargetMod", "solution_module": "TargetMod",
        "theorem_names": ["target1", "target2"], "definition_names": ["holeDef"], "permitted_axioms": ["propext"],
    }, open(cfg, "w"))

    def export_delta(proj, mods, out_p, exclude=None):
        mfile = out_p + ".mods"
        open(mfile, "w").write("\n".join(mods) + "\n")
        cmd = [export_delta_sh, proj, "@" + mfile, out_p, "--toolchain", tc]
        if exclude:
            cmd += ["--exclude", exclude]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        assert p.returncode == 0 and os.path.getsize(out_p) > 0, f"export-delta failed: {p.stdout} {p.stderr}"

    st_main = os.path.join(w, "st_main")
    p_main, lf_main = start_warm(fvcheckd, st_main, chal_exp, base_exp, cfg, pins)
    try:
        # C1+C7: Tier-1 leaf edit + sorried def hole filled
        p_c1 = os.path.join(w, "proj_c1"); shutil.copytree(base_dir, p_c1)
        build_437_proj(tc, p_c1, {"TargetMod": (
            "import MidMod\ndef holeDef : Nat := 999\ndef unsorriedDef : Nat := 42\n"
            "theorem target1 (n : Nat) : n + 0 = n := midLem n\ntheorem target2 : baseVal = 7 := Eq.refl 7\n"
        )})
        d_c1 = os.path.join(w, "d_c1.ndjson"); export_delta(p_c1, ["TargetMod"], d_c1)
        rc, j = query_warm(fvcheckd, st_main, d_c1)
        rec("C1+C7", "4.37 Tier-1 leaf edit + sorried definition_names hole filled -> ACCEPTED",
            rc == 0 and j["verdict"] == "ACCEPTED" and j["trust"] == "sound" and "4.37.0-rc1" in j["reason"],
            f"ms={j['wall_ms']}")

        # C2: Tier-2 --exclude captures newly-used Init lemma
        p_c2 = os.path.join(w, "proj_c2"); shutil.copytree(base_dir, p_c2)
        build_437_proj(tc, p_c2, {"TargetMod": (
            "import MidMod\ndef holeDef : Nat := 123\ndef unsorriedDef : Nat := 42\n"
            "theorem target1 (n : Nat) : n + 0 = n := by\n  have _h := @List.reverse_reverse Nat [n]\n  exact midLem n\n"
            "theorem target2 : baseVal = 7 := rfl\n"
        )})
        d_t1 = os.path.join(w, "d_c2_t1.ndjson"); d_t2 = os.path.join(w, "d_c2_t2.ndjson")
        export_delta(p_c2, ["TargetMod"], d_t1); rc1, j1 = query_warm(fvcheckd, st_main, d_t1)
        export_delta(p_c2, ["TargetMod"], d_t2, exclude=manifest); rc2, j2 = query_warm(fvcheckd, st_main, d_t2)
        rec("C2", "4.37 Tier-2 --exclude captures newly-used Init lemma -> ACCEPTED",
            rc1 == 1 and rc2 == 0 and j2["verdict"] == "ACCEPTED", f"T1={j1['verdict']} -> T2={j2['verdict']}")

        # C3: Mid-DAG proof-body edit (clean TargetMod un-rebuilt)
        p_c3 = os.path.join(w, "proj_c3"); shutil.copytree(base_dir, p_c3)
        build_437_proj(tc, p_c3, {"MidMod": "import BaseMod\ntheorem midLem (n : Nat) : n + 0 = n := by cases n <;> rfl\n"})
        d_c3 = os.path.join(w, "d_c3.ndjson"); export_delta(p_c3, ["MidMod", "TargetMod"], d_c3, exclude=manifest)
        rc, j = query_warm(fvcheckd, st_main, d_c3)
        rec("C3", "4.37 Mid-DAG proof-body edit (clean importer un-rebuilt) -> ACCEPTED",
            rc == 0 and j["verdict"] == "ACCEPTED", f"ms={j['wall_ms']}")

        # C4: Mid-DAG signature drift -> dual-kernel REJECTED
        p_c4 = os.path.join(w, "proj_c4"); shutil.copytree(base_dir, p_c4)
        build_437_proj(tc, p_c4, {"MidMod": "import BaseMod\ntheorem midLem (n : Nat) (_extra : True) : n + 0 = n := Nat.add_zero n\n"})
        d_c4 = os.path.join(w, "d_c4.ndjson"); export_delta(p_c4, ["MidMod", "TargetMod"], d_c4, exclude=manifest)
        rc, j = query_warm(fvcheckd, st_main, d_c4)
        l4 = j.get("legs", {}).get("lean4", {}).get("status"); gz = j.get("legs", {}).get("gruszka", {}).get("status")
        rec("C4", "4.37 Mid-DAG drift -> REJECTED by BOTH pleanchecker-warm-437 & gruszka-warm",
            rc == 1 and j["verdict"] == "REJECTED" and l4 == "reject" and gz == "reject", f"lean4={l4} gruszka={gz}")

        # C5: sorry cheat
        p_c5 = os.path.join(w, "proj_c5"); shutil.copytree(base_dir, p_c5)
        build_437_proj(tc, p_c5, {"TargetMod": (
            "import MidMod\ndef holeDef : Nat := 123\ndef unsorriedDef : Nat := 42\n"
            "theorem target1 (n : Nat) : n + 0 = n := by sorry\ntheorem target2 : baseVal = 7 := rfl\n"
        )})
        d_c5 = os.path.join(w, "d_c5.ndjson"); export_delta(p_c5, ["TargetMod"], d_c5, exclude=manifest)
        rc, j = query_warm(fvcheckd, st_main, d_c5)
        rec("C5", "4.37 sorry cheat -> REJECTED (sorryAx)",
            rc == 1 and j["verdict"] == "REJECTED" and "sorryAx" in j.get("reason", ""))

        # C8: Lean #15101 FakeQuot rejected by pleanchecker-warm-437 itself
        d_c8 = os.path.join(w, "d_c8.ndjson")
        open(d_c8, "w").write(
            '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.37.0-rc1"}}}\n'
            '{"in":1,"str":{"pre":0,"str":"FakeQuot437"}}\n{"ie":0,"sort":0}\n'
            '{"quot":{"kind":"type","levelParams":[],"name":1,"type":0}}\n'
        )
        rc, j = query_warm(fvcheckd, st_main, d_c8)
        l4_st = j.get("legs", {}).get("lean4", {}).get("status")
        l4_msg = j.get("legs", {}).get("lean4", {}).get("msg", "")
        rec("C8", "4.37 Lean #15101 FakeQuot -> fail-closed & REJECTED by pleanchecker-warm-437",
            rc != 0 and j["verdict"] != "ACCEPTED" and l4_st == "reject" and "Unexpected quotient" in l4_msg)
    finally:
        stop_warm(fvcheckd, st_main, p_main, lf_main)

    # C6: 4.37 unsorried definition_names rule
    cfg_u = os.path.join(w, "cfg_u.json")
    json.dump({"challenge_module": "TargetMod", "solution_module": "TargetMod",
               "theorem_names": ["target1"], "definition_names": ["unsorriedDef"], "permitted_axioms": ["propext"]}, open(cfg_u, "w"))
    st_c6 = os.path.join(w, "st_c6")
    empty_d = os.path.join(w, "empty.ndjson"); open(empty_d, "w").write('{"meta":{}}\n')   # also used by C10
    try:
        p_c6, lf_c6 = start_warm(fvcheckd, st_c6, chal_exp, base_exp, cfg_u, pins)
    except RuntimeError as e:   # combined patch: fvcheckd's own cross-version gate refuses to start (fail closed)
        rec("C6", "4.37 unsorried definition_names -> daemon refuses to start (xversion: 'Challenge definition is not sorried')",
            "not sorried" in str(e))
    else:
        try:
            rc, j = query_warm(fvcheckd, st_c6, empty_d)
            rec("C6", "4.37 unsorried definition_names -> REJECTED ('Challenge definition is not sorried')",
                rc == 1 and j["verdict"] == "REJECTED" and "not sorried" in j.get("reason", ""))
        finally:
            stop_warm(fvcheckd, st_c6, p_c6, lf_c6)

    # C9: B4 --pins confinement
    evil_p = os.path.join(w, "pins-evil.env"); shutil.copyfile(pins, evil_p)
    sym_p = os.path.join(w, "pins-sym.env"); os.symlink(pins, sym_p)
    b4_ok = True
    for bad_p in (evil_p, sym_p, os.path.join(os.path.dirname(pins), "..", "sound", "pins-437.env")):
        cp = subprocess.run(
            ["/usr/bin/python3", "-I", fvcheckd, "serve", "--state", os.path.join(w, "st_b4"),
             "--challenge", chal_exp, "--challenge-sha256", sha256(chal_exp),
             "--config", cfg, "--base", base_exp, "--pins", bad_p, "--pkgroot", args.pkgroot],
            capture_output=True, text=True, timeout=30,
        )
        if cp.returncode == 0:
            b4_ok = False
    rec("C9", "B4 --pins confinement: external / symlink / traversal --pins ALL refused", b4_ok)

    # C10: 4.37 --conditional-mode (Check A via check-sound.sh --pins pins-437.env)
    cp_dir = os.path.join(w, "cp_proj"); bp_dir = os.path.join(w, "bp_proj")
    build_437_proj(tc, cp_dir, {"BaseMod": base_code, "MidMod": mid_code_ok, "TargetMod": (
        "import MidMod\naxiom openHelper : ∀ n : Nat, n + 0 = n\ndef holeDef : Nat := sorry\n"
        "def unsorriedDef : Nat := 42\ntheorem target1 (n : Nat) : n + 0 = n := by sorry\ntheorem target2 : baseVal = 7 := by sorry\n"
    )})
    build_437_proj(tc, bp_dir, {"BaseMod": base_code, "MidMod": mid_code_ok, "TargetMod": (
        "import MidMod\naxiom openHelper : ∀ n : Nat, n + 0 = n\ndef holeDef : Nat := 77\n"
        "def unsorriedDef : Nat := 42\ntheorem target1 (n : Nat) : n + 0 = n := openHelper n\ntheorem target2 : baseVal = 7 := rfl\n"
    )})
    cp_exp = os.path.join(w, "cp.export"); bp_exp = os.path.join(w, "bp.export")
    official_export_437(tc, cp_dir, "TargetMod", ["target1", "target2", "holeDef", "openHelper", "propext"] + prim, cp_exp)
    official_export_437(tc, bp_dir, "TargetMod", ["target1", "target2", "holeDef", "openHelper", "propext"] + prim, bp_exp)
    fr_f = os.path.join(w, "frontier.txt"); open(fr_f, "w").write("openHelper\n")
    st_c10 = os.path.join(w, "st_c10")
    p_c10, lf_c10 = start_warm(
        fvcheckd, st_c10, cp_exp, bp_exp, cfg, pins,
        extra=["--conditional-mode", "--official-challenge", chal_exp, "--official-challenge-sha256", sha256(chal_exp), "--frontier", fr_f],
    )
    try:
        rc, j = query_warm(fvcheckd, st_c10, os.path.join(w, "empty.ndjson"))
        rec("C10", "4.37 --conditional-mode (Check A via check-sound.sh --pins pins-437.env) -> CONDITIONAL exit 3",
            rc == 3 and j["verdict"] == "CONDITIONAL" and j["trust"] == "sound-conditional" and j.get("frontier") == ["openHelper"])
    finally:
        stop_warm(fvcheckd, st_c10, p_c10, lf_c10)

    # C11: --hide FILE E2E (encapsulated replay + hide_sha256 + Case-2 + adversarial refusal)
    hide_f = os.path.join(w, "hide.txt")
    open(hide_f, "w").write("baseVal\nholeDef\n")
    hide_sha = sha256(hide_f)
    st_c11 = os.path.join(w, "st_c11")
    p_c11, lf_c11 = start_warm(fvcheckd, st_c11, chal_exp, base_exp, cfg, pins, extra=["--hide", hide_f])
    try:
        rdy = json.load(open(os.path.join(st_c11, "ready.json")))
        rc1, j1 = query_warm(fvcheckd, st_c11, d_c1)
        rc2, j2 = query_warm(fvcheckd, st_c11, d_c5)
        c11_e2e = (
            rdy.get("hide_sha256") == hide_sha
            and rc1 == 0 and j1["verdict"] == "ACCEPTED" and j1.get("hide_sha256") == hide_sha
            and rc2 == 1 and j2["verdict"] == "REJECTED" and j2.get("hide_sha256") == hide_sha
        )
    finally:
        stop_warm(fvcheckd, st_c11, p_c11, lf_c11)
    # Adversarial --hide refusals: >16 MiB symlink, FIFO, missing file, directory
    big_f = os.path.join(w, "big17m.txt")
    with open(big_f, "wb") as bf:
        bf.seek(17 * 1024 * 1024 - 1); bf.write(b"\n")
    big_sym = os.path.join(w, "big_sym.txt"); os.symlink(big_f, big_sym)
    fifo_p = os.path.join(w, "hide.fifo"); os.mkfifo(fifo_p)
    c11_adv = True
    for bad_h in (big_sym, fifo_p, os.path.join(w, "no_such_hide.txt"), w):
        cp = subprocess.run(
            ["/usr/bin/python3", "-I", fvcheckd, "serve", "--state", os.path.join(w, "st_c11_bad"),
             "--challenge", chal_exp, "--challenge-sha256", sha256(chal_exp),
             "--config", cfg, "--base", base_exp, "--pins", pins, "--hide", bad_h, "--pkgroot", args.pkgroot],
            capture_output=True, text=True, timeout=30,
        )
        if cp.returncode == 0:
            c11_adv = False
    rec("C11", "4.37 --hide E2E (hide_sha256 + ACCEPTED/REJECTED) & 17 MiB symlink/FIFO/dir refusal",
        c11_e2e and c11_adv, f"e2e={c11_e2e} adv={c11_adv}")

    print(f"\n=== 4.37 WARM E2E SUMMARY: {passed} PASS, {failed} FAIL ===")
    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()

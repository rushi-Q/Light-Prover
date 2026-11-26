#!/usr/bin/python3 -I
"""Conditional delta lifecycle benchmark for the persistent warm delta judge (check/warm/fvcheckd.py).

Runs a decomposition lifecycle (stage 0 -> intermediate closures -> final graduation) under
zero-new-TCB frontier semantics (frontier redirect construction + persistent warm delta):
  - Official challenge C pins MainThm : d5 = d0 (:= sorryAx).
  - Stage 0: an architect decomposes MainThm into 5 open lemmas L1..L5 via redirect
    frontier axioms `L1._fv_frontier_axiom .. L5._fv_frontier_axiom` in minted frontier
    challenge C'. Starting `fvcheckd serve --conditional-mode --official-challenge C
    --official-challenge-sha256 H --config official_cfg.json --frontier F` runs
    **Check A via the unchanged check-sound.sh AT STARTUP** (verifying C' agrees with
    official C on MainThm) and validates F (disjoint from targets, sorryAx, trust axioms).
  - Closures: provers close L1, L2, L3, L4 one by one via tiny delta overrides (theorem L_i
    replaces `L_i._fv_frontier_axiom` with a real kernel-checked proof). ONE persistent
    `fvcheckd --conditional-mode` verifies each closure in <10 ms -> CONDITIONAL (exit 3,
    trust="sound-conditional") — NEVER exit 0!
  - Cheats:
      * sorryAx in L5 -> REJECTED (exit 1)
      * Goalpost drift (MainThm statement altered) -> REJECTED (exit 1)
      * Custom axiom in L5 -> REJECTED (exit 1)
      * Per-query config injecting sorryAx -> DECLINED (exit 2)
  - All closed: even when all 5 lemmas are closed honestly, `--conditional-mode` NEVER returns
    ACCEPTED (exit 0); it still returns CONDITIONAL (exit 3).
  - Graduation: the final proof verified against official pinned C (without
    `--conditional-mode`, pinned official config) -> ACCEPTED (exit 0, trust="sound")!
"""
import argparse, json, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.realpath(__file__))
SRC_DIR = os.path.realpath(os.path.join(HERE, "..", "..", "check", "warm"))
TESTS_DIR = os.path.realpath(os.path.join(HERE, "..", "..", "tests", "warm-delta"))
sys.path.insert(0, SRC_DIR)
sys.path.insert(0, TESTS_DIR)
import fvcheckd  # noqa: E402
from run_adversarial import ExportBuilder, INIT_PREFIX, add_mybool  # noqa: E402


def build_lifecycle_repo(work: str):
    """Build official C, redirect frontier challenge C', stage-1 base B', official config, and F."""
    def setup_defs(b: ExportBuilder):
        add_mybool(b)
        mb = b.const("MyBool")
        ff = b.const("MyBool.ff")
        eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
        refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        b.add_def("d0", mb, ff)
        for i in range(1, 6):
            b.add_def(f"d{i}", mb, b.const(f"d{i-1}"))
        l_tys = {f"L{i}": b.app(b.app(b.app(eq1, mb), b.const(f"d{i}")), b.const(f"d{i-1}")) for i in range(1, 6)}
        main_ty = b.app(b.app(b.app(eq1, mb), b.const("d5")), b.const("d0"))
        return mb, ff, eq1, refl1, l_tys, main_ty

    def add_sorry_ax(b: ExportBuilder):
        u = b.lvl_param("u")
        sorry_ty = b.forall("α", b.sort(u), b.forall("synthetic", b.const("Bool"), b.bvar(1)))
        b.add_axiom("sorryAx", sorry_ty, lparams=["u"])

    def sorry_of(b: ExportBuilder, ty: int) -> int:
        return b.app(b.app(b.const("sorryAx", [b.lvl_zero()]), ty), b.const("Bool.false"))

    def make_main_proof(b: ExportBuilder, mb, ff, refl1, l_tys):
        body = b.app(b.app(refl1, mb), ff)
        for i in range(5, 0, -1):
            body = b.lam(f"h{i}", l_tys[f"L{i}"], body)
        for i in range(1, 6):
            body = b.app(body, b.const(f"L{i}"))
        return body

    # 1. Official Challenge C: MainThm := sorryAx
    bc = ExportBuilder(INIT_PREFIX)
    mb, ff, eq1, refl1, l_tys, main_ty = setup_defs(bc)
    add_sorry_ax(bc)
    bc.add_thm("MainThm", main_ty, sorry_of(bc, main_ty))
    chal_official = os.path.join(work, "official_C.export")
    bc.write(chal_official)

    # 2. Frontier Challenge C': official C + frontier axioms L1._fv_frontier_axiom .. L5._fv_frontier_axiom
    #    (MainThm remains identical to official C so Check A: check-sound.sh(C' vs C, A+sorryAx) ACCEPTS!)
    bcp = ExportBuilder(INIT_PREFIX)
    mb, ff, eq1, refl1, l_tys, main_ty = setup_defs(bcp)
    add_sorry_ax(bcp)
    for i in range(1, 6):
        bcp.add_axiom(f"L{i}._fv_frontier_axiom", l_tys[f"L{i}"])
    bcp.add_thm("MainThm", main_ty, sorry_of(bcp, main_ty))
    chal_frontier = os.path.join(work, "frontier_C_prime.export")
    bcp.write(chal_frontier)

    # 3. Stage-1 rewritten base B' (frontier redirect construction: theorem L_i := L_i._fv_frontier_axiom, MainThm proved from L1..L5, NO sorryAx!)
    bbp = ExportBuilder(INIT_PREFIX)
    mb, ff, eq1, refl1, l_tys, main_ty = setup_defs(bbp)
    for i in range(1, 6):
        ax_nm = f"L{i}._fv_frontier_axiom"
        bbp.add_axiom(ax_nm, l_tys[f"L{i}"])
        bbp.add_thm(f"L{i}", l_tys[f"L{i}"], bbp.const(ax_nm))
    bbp.add_thm("MainThm", main_ty, make_main_proof(bbp, mb, ff, refl1, l_tys))
    base_frontier = os.path.join(work, "base_S_prime.export")
    bbp.write(base_frontier)

    # 4. Official comparator.json + Frontier file F
    cfg_official = os.path.join(work, "official_comparator.json")
    json.dump({"challenge_module": "Challenge", "solution_module": "Solution",
               "theorem_names": ["MainThm"], "definition_names": [], "permitted_axioms": []}, open(cfg_official, "w"))
    frontier_file = os.path.join(work, "frontier_F.txt")
    open(frontier_file, "w").write("\n".join(f"L{i}._fv_frontier_axiom" for i in range(1, 6)) + "\n")
    return chal_official, chal_frontier, base_frontier, cfg_official, frontier_file


def make_honest_closures_delta(path: str, closed_indices):
    """Delta proving L_i honestly for all i in closed_indices (replaces redirect axiom with real proof!)."""
    b = ExportBuilder()
    mb = b.const("MyBool")
    ff = b.const("MyBool.ff")
    eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())])
    refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
    l_tys = {}
    for i in range(1, 6):
        l_tys[f"L{i}"] = b.app(b.app(b.app(eq1, mb), b.const(f"d{i}")), b.const(f"d{i-1}"))
    for i in closed_indices:
        b.add_thm(f"L{i}", l_tys[f"L{i}"], b.app(b.app(refl1, mb), ff))
    # Re-supply MainThm (dirtied because it references overridden L_i)
    main_ty = b.app(b.app(b.app(eq1, mb), b.const("d5")), b.const("d0"))
    body = b.app(b.app(refl1, mb), ff)
    for i in range(5, 0, -1):
        body = b.lam(f"h{i}", l_tys[f"L{i}"], body)
    for i in range(1, 6):
        body = b.app(body, b.const(f"L{i}"))
    b.add_thm("MainThm", main_ty, body)
    b.write(path)


def start_d(fvcheckd_py, sdir, chal, base, cfg, bins_dir, pkgroot, cond=False, official_chal=None, frontier=None):
    shutil.rmtree(sdir, ignore_errors=True)
    cmd = [
        "/usr/bin/python3", "-I", fvcheckd_py, "serve",
        "--state", sdir, "--challenge", chal, "--challenge-sha256", fvcheckd.sha256_file(chal),
        "--config", cfg,
        "--base", base, "--threads", "4", "--bins-dir", bins_dir, "--pkgroot", pkgroot,
    ]
    if cond:
        cmd += ["--conditional-mode", "--official-challenge", official_chal,
                "--official-challenge-sha256", fvcheckd.sha256_file(official_chal),
                "--frontier", frontier]
    lf = open(sdir + ".log", "w")
    p = subprocess.Popen(cmd, stdout=lf, stderr=subprocess.STDOUT)
    sock = os.path.join(sdir, "sock")
    for _ in range(600):
        if os.path.exists(sock):
            return p, lf
        if p.poll() is not None:
            lf.close()
            raise RuntimeError(open(sdir + ".log").read())
        time.sleep(0.05)
    p.kill(); lf.close()
    raise RuntimeError("timeout")


def stop_d(sdir, p, lf):
    try:
        fvcheckd.send_req(sdir, {"op": "stop"}, 10.0)
        p.wait(timeout=5)
    except Exception:
        p.kill(); p.wait()
    lf.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--bins-dir", default="/scratch/fastverify-next/warm/v1")
    ap.add_argument("--pkgroot", default="$LIGHT_LEAN/fastverify")
    ap.add_argument("--fvcheckd", default=None)
    args = ap.parse_args()
    os.makedirs(args.work, exist_ok=True)
    os.makedirs(args.out, exist_ok=True)
    fvcheckd_py = args.fvcheckd or (os.path.join(args.pkgroot, "check", "warm", "fvcheckd.py")
                                    if os.path.isfile(os.path.join(args.pkgroot, "check", "warm", "fvcheckd.py"))
                                    else os.path.join(SRC_DIR, "fvcheckd.py"))

    chal_off, chal_fr, base_fr, cfg_off, frontier_f = build_lifecycle_repo(args.work)
    events = []
    fails = 0

    # --- STEP 1 (stage 0 to all closed): Start ONE fvcheckd --conditional-mode!
    #     Check A (unchanged check-sound.sh on C' vs official C) & frontier validation run AUTOMATICALLY at startup!
    s_cond = os.path.join(args.work, "d_lifecycle")
    t_st = time.time()
    pC, lfC = start_d(fvcheckd_py, s_cond, chal_fr, base_fr, cfg_off, args.bins_dir, args.pkgroot,
                      cond=True, official_chal=chal_off, frontier=frontier_f)
    startup_ms = round((time.time() - t_st) * 1000.0, 2)
    try:
        # Stage 0: empty delta on the stage-1 base -> CONDITIONAL exit 3 (Check A already passed at startup!)
        d0 = os.path.join(args.work, "step0_empty.ndjson")
        ExportBuilder().write(d0)
        r0 = fvcheckd.send_req(s_cond, {"op": "check_delta", "delta": d0})
        ok0 = (r0.get("verdict") == "CONDITIONAL" and r0.get("exit") == 3 and r0.get("trust") == "sound-conditional"
               and len(r0.get("frontier", [])) == 5)
        if not ok0: fails += 1
        events.append({"step": "step0_checkA_and_baseline", "verdict": r0.get("verdict"), "exit": r0.get("exit"),
                       "trust": r0.get("trust"), "startup_with_checkA_ms": startup_ms, "wall_ms": r0.get("wall_ms"), "pass": ok0})
        print(f"[{'PASS' if ok0 else 'FAIL'}] Step 0 (startup Check A {startup_ms}ms + baseline): {r0.get('verdict')} exit={r0.get('exit')} ({r0.get('wall_ms')}ms)")

        # Closures: honest cumulative closures of L1..L4 -> CONDITIONAL exit 3!
        for i in range(1, 5):
            dp = os.path.join(args.work, f"close_L1_L{i}.ndjson")
            make_honest_closures_delta(dp, list(range(1, i + 1)))
            r = fvcheckd.send_req(s_cond, {"op": "check_delta", "delta": dp})
            ok = (r.get("verdict") == "CONDITIONAL" and r.get("exit") == 3 and r.get("trust") == "sound-conditional")
            if not ok: fails += 1
            events.append({"step": f"step{i}_close_L{i}_honest", "open_remaining": 5 - i, "verdict": r.get("verdict"),
                           "exit": r.get("exit"), "wall_ms": r.get("wall_ms"), "pass": ok})
            print(f"[{'PASS' if ok else 'FAIL'}] Step {i} close L{i} honestly ({5-i} open left): {r.get('verdict')} exit={r.get('exit')} ({r.get('wall_ms')}ms)")

        # Cheat 1: an agent closes L5 using sorryAx -> REJECTED!
        d_sorry = os.path.join(args.work, "cheat_L5_sorry.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool"); ff = b.const("MyBool.ff"); eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())]); refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        u = b.lvl_param("u")
        b.add_axiom("sorryAx", b.forall("α", b.sort(u), b.forall("synthetic", b.const("Bool"), b.bvar(1))), lparams=["u"])
        l_tys = {f"L{k}": b.app(b.app(b.app(eq1, mb), b.const(f"d{k}")), b.const(f"d{k-1}")) for k in range(1, 6)}
        b.add_thm("L5", l_tys["L5"], b.app(b.app(b.const("sorryAx", [b.lvl_zero()]), l_tys["L5"]), b.const("Bool.false")))
        main_ty = b.app(b.app(b.app(eq1, mb), b.const("d5")), b.const("d0"))
        body = b.app(b.app(refl1, mb), ff)
        for k in range(5, 0, -1): body = b.lam(f"h{k}", l_tys[f"L{k}"], body)
        for k in range(1, 6): body = b.app(body, b.const(f"L{k}"))
        b.add_thm("MainThm", main_ty, body)
        b.write(d_sorry)
        r = fvcheckd.send_req(s_cond, {"op": "check_delta", "delta": d_sorry})
        ok = (r.get("verdict") == "REJECTED" and r.get("exit") == 1)
        if not ok: fails += 1
        events.append({"step": "cheat_sorry_L5", "verdict": r.get("verdict"), "exit": r.get("exit"), "wall_ms": r.get("wall_ms"), "pass": ok, "reason": str(r.get("reason", ""))[:100]})
        print(f"[{'PASS' if ok else 'FAIL'}] Cheat (sorry in L5): {r.get('verdict')} ({r.get('wall_ms')}ms) :: {str(r.get('reason',''))[:70]}")

        # Cheat 2: an agent tries to move goalposts on MainThm (changes statement to d0 = d0!) -> REJECTED!
        d_drift = os.path.join(args.work, "cheat_MainThm_drift.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool"); ff = b.const("MyBool.ff"); eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())]); refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        bad_ty = b.app(b.app(b.app(eq1, mb), b.const("d0")), b.const("d0"))
        b.add_thm("MainThm", bad_ty, b.app(b.app(refl1, mb), ff))
        b.write(d_drift)
        r = fvcheckd.send_req(s_cond, {"op": "check_delta", "delta": d_drift})
        ok = (r.get("verdict") == "REJECTED" and r.get("exit") == 1)
        if not ok: fails += 1
        events.append({"step": "cheat_goalpost_drift_MainThm", "verdict": r.get("verdict"), "exit": r.get("exit"), "wall_ms": r.get("wall_ms"), "pass": ok, "reason": str(r.get("reason", ""))[:100]})
        print(f"[{'PASS' if ok else 'FAIL'}] Cheat (goalpost drift MainThm): {r.get('verdict')} ({r.get('wall_ms')}ms) :: {str(r.get('reason',''))[:70]}")

        # Cheat 3: an agent injects custom cheatAx into L5 -> REJECTED!
        d_ax = os.path.join(args.work, "cheat_L5_ax.ndjson")
        b = ExportBuilder()
        mb = b.const("MyBool"); ff = b.const("MyBool.ff"); eq1 = b.const("Eq", [b.lvl_succ(b.lvl_zero())]); refl1 = b.const("Eq.refl", [b.lvl_succ(b.lvl_zero())])
        l_tys = {f"L{k}": b.app(b.app(b.app(eq1, mb), b.const(f"d{k}")), b.const(f"d{k-1}")) for k in range(1, 6)}
        b.add_axiom("cheatAx", l_tys["L5"])
        b.add_thm("L5", l_tys["L5"], b.const("cheatAx"))
        main_ty = b.app(b.app(b.app(eq1, mb), b.const("d5")), b.const("d0"))
        body = b.app(b.app(refl1, mb), ff)
        for k in range(5, 0, -1): body = b.lam(f"h{k}", l_tys[f"L{k}"], body)
        for k in range(1, 6): body = b.app(body, b.const(f"L{k}"))
        b.add_thm("MainThm", main_ty, body)
        b.write(d_ax)
        r = fvcheckd.send_req(s_cond, {"op": "check_delta", "delta": d_ax})
        ok = (r.get("verdict") == "REJECTED" and r.get("exit") == 1)
        if not ok: fails += 1
        events.append({"step": "cheat_custom_axiom_L5", "verdict": r.get("verdict"), "exit": r.get("exit"), "wall_ms": r.get("wall_ms"), "pass": ok, "reason": str(r.get("reason", ""))[:100]})
        print(f"[{'PASS' if ok else 'FAIL'}] Cheat (custom cheatAx): {r.get('verdict')} ({r.get('wall_ms')}ms) :: {str(r.get('reason',''))[:70]}")

        # All closed: even with ALL 5 lemmas closed honestly, conditional daemon NEVER exits 0!
        d_all = os.path.join(args.work, "all_closed.ndjson")
        make_honest_closures_delta(d_all, [1, 2, 3, 4, 5])
        r = fvcheckd.send_req(s_cond, {"op": "check_delta", "delta": d_all})
        ok = (r.get("verdict") == "CONDITIONAL" and r.get("exit") == 3)
        if not ok: fails += 1
        events.append({"step": "conditional_never_exits_0", "verdict": r.get("verdict"), "exit": r.get("exit"), "wall_ms": r.get("wall_ms"), "pass": ok})
        print(f"[{'PASS' if ok else 'FAIL'}] Conditional safety (never exit 0): {r.get('verdict')} exit={r.get('exit')} ({r.get('wall_ms')}ms)")
    finally:
        stop_d(s_cond, pC, lfC)

    # --- STEP 2 (graduation): Final sound daemon pinned to OFFICIAL challenge C (NO --conditional-mode) -> ACCEPTED exit 0!
    s_grad = os.path.join(args.work, "d_graduation")
    pG, lfG = start_d(fvcheckd_py, s_grad, chal_off, chal_off, cfg_off, args.bins_dir, args.pkgroot, cond=False)
    try:
        rG = fvcheckd.send_req(s_grad, {"op": "check_delta", "delta": d_all})
        okG = (rG.get("verdict") == "ACCEPTED" and rG.get("exit") == 0 and rG.get("trust") == "sound")
        if not okG: fails += 1
        events.append({"step": "graduation_official_C", "verdict": rG.get("verdict"), "exit": rG.get("exit"),
                       "trust": rG.get("trust"), "wall_ms": rG.get("wall_ms"), "pass": okG})
        print(f"[{'PASS' if okG else 'FAIL'}] Graduation (official C, no sorries): {rG.get('verdict')} exit={rG.get('exit')} trust={rG.get('trust')} ({rG.get('wall_ms')}ms)")
    finally:
        stop_d(s_grad, pG, lfG)

    summary = {"total": len(events), "pass": sum(1 for e in events if e["pass"]), "fail": fails,
               "status": "PASS" if fails == 0 else "FAIL", "events": events}
    json.dump(summary, open(os.path.join(args.out, "conditional-lifecycle.json"), "w"), indent=2)
    print(f"\n=== CONDITIONAL LIFECYCLE: {summary['pass']}/{summary['total']} PASS (status={summary['status']}) ===")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()

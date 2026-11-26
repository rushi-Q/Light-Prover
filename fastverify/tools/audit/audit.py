#!/usr/bin/python3 -I
"""audit.py — Unified Statement Fidelity & Challenge Anti-Gaming Auditor for `fastverify`.

Additive, zero-TCB-change statement auditor combining:
  1. `expaudit` (fast std-only Rust kernel-AST analyzer):
     - Computes the exact Minimal Non-Mathlib Statement Reading Set (`statement_closure \\ base`) in topological order;
     - Audits kernel ASTs for `definition_names` holes, un-sorried / unparameterized answer holes, extra/opaque/sorry-in-def
       traps, `autoImplicit` / unused statement parameters, `∃ x, P → Q` existential-implication traps, uninhabited custom
       inductives/classes, base-library modification/shadowing, and unguarded partial/junk-value operations (`Nat.sub`,
       truncating `Nat.div`/`Nat.sqrt` in bounds, `/ 0`, unguarded variable division, `sInf`/`sSup` junk values).
  2. Source-level hygiene checks (when `.lean` source is available):
     - `set_option autoImplicit true`, custom `notation`/`infix`/`prefix` overriding standard operators, `local instance`.
  3. `vacuity_probe.py` (sandboxed `bwrap --unshare-all` dynamic prober using the official Lean kernel `Lean.addDecl`):
     - 100% kernel-certified detection of contradictory premises (`premises ⊢ False`), false statements (`⊢ ¬ statement`),
       and conclusions provable via degenerate witnesses (`0`, `∅`, `{0},{1}`) or after dropping explicit hypotheses.

Usage:
  audit.py TARGET [--config COMPARATOR.json] [--targets T1,T2] [--base-index BASE.baseidx | --base BASE.export]
                  [--packages WS] [--toolchain TC] [--probe | --no-probe] [--conjecture-mode]
                  [--reading-set OUT.lean] [--json OUT.json] [--human] [--fail-on WARN|HIGH|CRITICAL]

`TARGET` may be:
  * a challenge directory (containing `comparator.json`, `challenge.export`, and/or `Challenge.lean`),
  * a `.export` file (`challenge.export`), or
  * a standalone `.lean` file (automatically compiled and exported inside `bwrap` without network!).
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.realpath(__file__))
FV_ROOT = os.path.realpath(os.environ.get("FASTVERIFY_ROOT") or os.path.dirname(os.path.dirname(HERE)))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import vacuity_probe as vp

SEV_RANK = {"CRITICAL": 4, "HIGH": 3, "WARN": 2, "INFO": 1, "CLEAN": 0}


def default_components():
    cfg_p = os.path.join(FV_ROOT, "config", "components.json")
    if os.path.isfile(cfg_p):
        try:
            return json.load(open(cfg_p, encoding="utf-8"))
        except Exception:
            pass
    return {}


_TC_SPEC = re.compile(r"^[A-Za-z0-9_-]+/[A-Za-z0-9_-]+:[A-Za-z0-9_.+-]+$")


def _read_toolchain_spec(hint_dir):
    """the client's lean-toolchain: a single-link regular file opened O_NOFOLLOW|
    O_NONBLOCK, at most 256 bytes, of the form ORG/REPO:VERSION (no '/', '..', control character beyond that); else None"""
    try:
        fd = os.open(os.path.join(hint_dir, "lean-toolchain"), os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError:
        return None
    try:
        import stat as _st
        st = os.fstat(fd)
        if not _st.S_ISREG(st.st_mode) or st.st_nlink != 1:
            return None
        spec = os.read(fd, 257).decode("utf-8", "replace").strip()
    finally:
        os.close(fd)
    if len(spec) > 256 or not _TC_SPEC.match(spec) or ".." in spec:
        return None
    return spec


def resolve_toolchain(comp, explicit_tc=None, hint_dir=None):
    if explicit_tc:
        return os.path.realpath(explicit_tc)
    tcs = comp.get("lean_toolchains", {})
    if hint_dir:
        spec = _read_toolchain_spec(hint_dir)   # never '..' (-> ~/.elan/toolchains/..) or a link / FIFO
        if spec is None and os.path.lexists(os.path.join(hint_dir, "lean-toolchain")):
            return None   # present but refused (link / special / malformed): no toolchain, never a fallback guess
        if spec:
            if spec in tcs and os.path.isdir(tcs[spec]["prefix"]):
                return tcs[spec]["prefix"]
            elan = os.path.realpath(os.path.expanduser("~/.elan/toolchains"))
            slug = spec.replace("/", "--").replace(":", "---")
            cand = os.path.join(elan, slug)
            # an elan toolchain: a direct child of ~/.elan/toolchains that is a Lean toolchain prefix
            if os.path.dirname(os.path.normpath(cand)) == elan and vp.is_toolchain_dir(cand):
                return cand
    for k in ("leanprover/lean4:v4.33.1", "leanprover/lean4:v4.36.0"):
        if k in tcs and os.path.isdir(tcs[k]["prefix"]):
            return tcs[k]["prefix"]
    for cand in (
        os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1"),
        os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.36.0"),
    ):
        if os.path.isdir(cand):
            return cand
    return None


def resolve_packages_ws(explicit_ws=None, hint_dir=None, src_lean=None, tc=None):
    if explicit_ws:
        if explicit_ws.lower() == "none":
            return None
        if os.path.isdir(explicit_ws):
            return os.path.realpath(explicit_ws)
    if hint_dir:
        pk = os.path.join(hint_dir, ".lake", "packages")
        if os.path.isdir(pk):
            return os.path.realpath(hint_dir)
    # If standalone .lean file has zero external package imports, keep it Init-only!
    if src_lean and os.path.isfile(src_lean):
        raw = open(src_lean, encoding="utf-8", errors="replace").read()
        has_imp = any(re.match(r"^\s*(?:public\s+)?import\s+\S+", ln) for ln in raw.splitlines())
        if not has_imp:
            return None
    default_ws = os.path.join(os.path.dirname(FV_ROOT), "verify", "challenge")
    if os.path.isdir(os.path.join(default_ws, ".lake", "packages")):
        ws_tc_f = os.path.join(default_ws, "lean-toolchain")
        if tc and os.path.isfile(ws_tc_f):
            ws_spec = open(ws_tc_f, encoding="utf-8").read().strip()
            ver = ws_spec.split(":")[-1]
            if ver and ver not in os.path.basename(tc):
                return None
        return os.path.realpath(default_ws)
    return None


def ensure_expaudit_bin(threads=8):
    env_bin = os.environ.get("EXPAUDIT_BIN") or os.environ.get("FASTVERIFY_EXPAUDIT_BIN")
    if env_bin and os.path.isfile(env_bin) and os.access(env_bin, os.X_OK):
        return env_bin
    src_mtime = max(
        os.path.getmtime(os.path.join(HERE, "expaudit", "src", "main.rs")),
        os.path.getmtime(os.path.join(HERE, "expaudit", "src", "base.rs")),
    )
    for td in (
        os.path.join(HERE, "bin", "expaudit"),
        os.path.join(os.environ.get("FV_SCRATCH") or tempfile.gettempdir(),
                     f"{os.environ.get('USER', 'u')}-expaudit-target", "release", "expaudit"),
        f"/tmp/{os.environ.get('USER', 'u')}-expaudit-target/release/expaudit",
    ):
        if os.path.isfile(td) and os.access(td, os.X_OK) and os.path.getmtime(td) >= src_mtime:
            return td
    build_sh = os.path.join(HERE, "expaudit", "build.sh")
    p = subprocess.run([build_sh], capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"failed to build expaudit: {p.stderr}")
    return p.stdout.strip().splitlines()[-1]


def default_base_index_or_export(tc=None):
    # Match precomputed Mathlib base index to the Lean release (`4.37` -> Mathlib `31ce06ea`, `4.33` -> Mathlib `0df444a`).
    # Indexes are looked up in $EXPAUDIT_BASEIDX_DIR (built with `expaudit index-base`), the Mathlib export in
    # $FV_BENCH_INPUTS/mathlib/export/mathlib.export; unset variables are skipped.
    idx_dir = os.environ.get("EXPAUDIT_BASEIDX_DIR")
    if tc and ("4.37" in os.path.basename(tc)):
        p437 = os.path.join(idx_dir, "mathlib-31ce06ea-437.baseidx") if idx_dir else None
        if p437 and os.path.isfile(p437):
            return ("index", p437)
        return (None, None)
    if tc and ("4.33" not in os.path.basename(tc)):
        return (None, None)
    for name in ("mathlib-0df444a.baseidx", "mathlib.baseidx"):
        p = os.path.join(idx_dir, name) if idx_dir else None
        if p and os.path.isfile(p):
            return ("index", p)
    bi = os.environ.get("FV_BENCH_INPUTS")
    ml_exp = os.path.join(bi, "mathlib", "export", "mathlib.export") if bi else None
    if ml_exp and os.path.isfile(ml_exp):
        return ("export", ml_exp)
    return (None, None)


def scan_source_lints(lean_files):
    findings = []
    std_ops = r"(\+|-|\*|/|≤|<|≥|>|=|≠|↔|∧|∨|¬|∈|⊆|∑|∏)"
    for lf in lean_files:
        if not os.path.isfile(lf):
            continue
        txt = open(lf, encoding="utf-8", errors="replace").read()
        # Strip line comments for cleaner matching
        clean_lines = []
        for idx, ln in enumerate(txt.splitlines(), 1):
            code = ln.split("--", 1)[0]
            clean_lines.append((idx, code))
            if re.search(r"\bset_option\s+autoImplicit\s+true\b", code):
                findings.append({
                    "id": "S01_AUTO_IMPLICIT_ENABLED",
                    "severity": "WARN",
                    "source": "source_lint",
                    "decl": f"{os.path.basename(lf)}:{idx}",
                    "summary": "`set_option autoImplicit true` enabled in challenge source (risk of silent typo quantification)",
                    "detail": code.strip(),
                })
            if re.search(rf"\b(local\s+|scoped\s+)?(notation|infix|infixl|infixr|prefix|postfix)\b.*\"\s*{std_ops}\s*\"", code):
                findings.append({
                    "id": "S02_OPERATOR_NOTATION_OVERRIDE",
                    "severity": "HIGH",
                    "source": "source_lint",
                    "decl": f"{os.path.basename(lf)}:{idx}",
                    "summary": "Challenge source overrides standard mathematical operator notation",
                    "detail": code.strip(),
                })
            if re.search(r"\blocal\s+instance\b", code):
                findings.append({
                    "id": "S03_LOCAL_INSTANCE_OVERRIDE",
                    "severity": "WARN",
                    "source": "source_lint",
                    "decl": f"{os.path.basename(lf)}:{idx}",
                    "summary": "`local instance` in challenge source may alter typeclass meaning vs standard Mathlib",
                    "detail": code.strip(),
                })
    return findings


def discover_theorems_in_lean(lean_path):
    """Fallback theorem-name extractor for standalone `.lean` files without a `comparator.json`."""
    txt = open(lean_path, encoding="utf-8", errors="replace").read()
    ns_stack = []
    thms = []
    for ln in txt.splitlines():
        code = ln.split("--", 1)[0].strip()
        m_ns = re.match(r"^namespace\s+([A-Za-z0-9_.']+)\s*$", code)
        if m_ns:
            ns_stack.extend(m_ns.group(1).split("."))
            continue
        m_end = re.match(r"^end\s+([A-Za-z0-9_.']+)\s*$", code)
        if m_end:
            parts = m_end.group(1).split(".")
            if len(ns_stack) >= len(parts) and ns_stack[-len(parts):] == parts:
                ns_stack = ns_stack[:-len(parts)]
            continue
        m_th = re.match(r"^(?:@\[[^\]]*\]\s*)*(?:public\s+|protected\s+)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.']*)", code)
        if m_th:
            nm = m_th.group(1)
            full = ".".join(ns_stack + [nm]) if ns_stack else nm
            thms.append(full)
    return thms


def export_standalone_lean(lean_file, tc, ws, threads=8, targets=None):
    """Compiles a standalone `.lean` challenge file inside `bwrap --unshare-all` and exports it with E1 (fallback E0)."""
    fs = os.environ.get("FV_SCRATCH")
    tmp_base = fs if fs and os.path.isdir(fs) and os.access(fs, os.W_OK) else "/tmp"
    work = tempfile.mkdtemp(prefix="fvaudit-exp-", dir=tmp_base)
    src_real = os.path.realpath(lean_file)
    mod_name = os.path.splitext(os.path.basename(src_real))[0]
    if not re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", mod_name):
        mod_name = "ChallengeAudit"
    dst_lean = os.path.join(work, mod_name + ".lean")
    shutil.copy2(src_real, dst_lean)
    # Copy any sibling .lean files in the same folder if imported
    raw = open(src_real, encoding="utf-8", errors="replace").read()
    cdir = os.path.dirname(src_real)
    local_mods = []
    for ln in raw.splitlines():
        m = re.match(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$", ln)
        if m:
            imp = m.group(1)
            parts = vp.module_rel_parts(imp)   # never a path outside cdir / work
            if parts is None:
                shutil.rmtree(work, ignore_errors=True)
                raise RuntimeError(f"invalid import module name {imp!r} in the challenge file (refused)")
            cand = module_lean_path(cdir, imp)
            if cand and _copy_plain(cand, os.path.join(work, *parts) + ".lean"):
                local_mods.append(imp)

    lp_ws, ro_ws = vp.workspace_lean_path(ws)
    lib_dir = os.path.join(work, "lib")
    os.makedirs(lib_dir, exist_ok=True)
    tc_lib = os.path.join(tc, "lib", "lean")
    # Put `lib_dir` FIRST so a standalone `Challenge.lean` is never shadowed by a workspace's `Challenge.olean`!
    lp = ":".join(x for x in (lib_dir, lp_ws, tc_lib) if x)
    lean_bin = os.path.join(tc, "bin", "lean")

    for imp in local_mods:
        ol = os.path.join(lib_dir, *imp.split(".")) + ".olean"
        os.makedirs(os.path.dirname(ol), exist_ok=True)
        cmd = vp.bwrap_cmd(tc, ro_ws, [work], {"LEAN_PATH": lp}, work) + [
            lean_bin, "-Dlinter.all=false", "-o", ol, os.path.join(work, *imp.split(".")) + ".lean"
        ]
        r = subprocess.run(cmd, capture_output=True, text=True, env={}, timeout=120)
        if r.returncode != 0:
            shutil.rmtree(work, ignore_errors=True)
            raise RuntimeError(f"failed to compile dependency {imp}: {r.stderr or r.stdout}")

    main_ol = os.path.join(lib_dir, mod_name + ".olean")
    cmd = vp.bwrap_cmd(tc, ro_ws, [work], {"LEAN_PATH": lp}, work) + [
        lean_bin, "-Dlinter.all=false", "-o", main_ol, dst_lean
    ]
    r = subprocess.run(cmd, capture_output=True, text=True, env={}, timeout=120)
    if r.returncode != 0:
        err_lines = [ln for ln in (r.stdout + "\n" + r.stderr).splitlines() if ": error" in ln]
        err = "\n".join(err_lines[:15]) if err_lines else (r.stderr or r.stdout)[-800:]
        shutil.rmtree(work, ignore_errors=True)
        raise RuntimeError(f"challenge file failed to compile in sandbox: {err}")

    exp_out = os.path.join(work, "challenge.export")
    tlist = list(targets) if targets else discover_theorems_in_lean(src_real)
    # Try fast native exporter E1 first, fallback to official lean4export / leanexport
    e1_sh = os.path.join(FV_ROOT, "export", "export.sh")
    tfile = os.path.join(work, "targets.txt")
    # Include standard primitives so E1 closure guard is happy
    prims = [
        "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble",
        "String.ofList", "Char.ofNat", "List", "Nat", "String", "String.mk", "Char", "propext", "Quot.sound",
        "Classical.choice",
    ]
    with open(tfile, "w", encoding="utf-8") as f:
        for t in list(dict.fromkeys(list(tlist) + prims)):
            f.write(t + "\n")

    lp_file = os.path.join(work, "lean_path.txt")
    with open(lp_file, "w", encoding="utf-8") as f:
        f.write(lp)

    exported = False
    if os.path.isfile(e1_sh) and "v4.33.1" in tc:
        p_e1 = subprocess.run(
            [e1_sh, lp_file, mod_name, tfile, exp_out, "--threads", str(min(threads, 16)), "--log", work],
            capture_output=True,
            text=True,
            timeout=120,
        )
        if p_e1.returncode == 0 and os.path.isfile(exp_out) and os.path.getsize(exp_out) > 0:
            exported = True

    if not exported:
        comp = default_components()
        l4e = os.path.join(tc, "bin", "leanexport")
        if not os.path.isfile(l4e):
            l4e = comp.get("official_lean4export", {}).get("bin", "")
        if not l4e or not os.path.isfile(l4e):
            l4e = os.path.join(os.path.dirname(FV_ROOT), "env", "tools", "lean4export", ".lake", "build", "bin", "lean4export")
        ro_exp = list(ro_ws) + [ os.path.dirname(os.path.realpath(l4e)) ]
        cmd_e0 = vp.bwrap_cmd(tc, ro_exp, [work], {"LEAN_PATH": lp, "LEAN_ABORT_ON_PANIC": "1"}, work) + [
            os.path.realpath(l4e), mod_name, "--", *tlist
        ]
        with open(exp_out, "wb") as out_f:
            p_e0 = subprocess.run(cmd_e0, stdout=out_f, stderr=subprocess.PIPE, env={}, timeout=180)
        if p_e0.returncode != 0 or os.path.getsize(exp_out) == 0:
            err = p_e0.stderr.decode("utf-8", "replace")[-400:]
            shutil.rmtree(work, ignore_errors=True)
            raise RuntimeError(f"failed to export standalone lean file: {err}")

    cfg_path = os.path.join(work, "comparator.json")
    with open(cfg_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "challenge_module": mod_name,
                "solution_module": mod_name,
                "theorem_names": tlist,
                "definition_names": [],
                "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            },
            f,
        )
    return work, exp_out, cfg_path, tlist


def run_audit(
    target,
    config_path=None,
    targets_spec=None,
    base_export=None,
    base_index=None,
    packages_ws=None,
    toolchain=None,
    run_dynamic=None,
    conjecture_mode=False,
    solution_mode=False,
    reading_set_out=None,
    threads=8,
    probe_timeout=45,
    fail_on=None,
):
    t0 = time.time()
    comp = default_components()
    temp_export_dir = None
    challenge_lean = None
    hint_dir = None
    tc = toolchain

    try:
        if os.path.isdir(target):
            hint_dir = os.path.realpath(target)
            if not config_path:
                cand_cfg = os.path.join(hint_dir, "comparator.json")
                if os.path.isfile(cand_cfg):
                    config_path = cand_cfg
            cand_exp = os.path.join(hint_dir, "challenge.export")
            # Locate Challenge.lean if present
            cmod = "Challenge"
            if config_path and os.path.isfile(config_path):
                try:
                    cmod = json.load(open(config_path, encoding="utf-8")).get("challenge_module", "Challenge")
                except Exception:
                    pass
            cand_lean = module_lean_path(hint_dir, cmod)   # contained in the target directory
            if cand_lean and os.path.isfile(cand_lean):
                challenge_lean = cand_lean
            else:
                # Search top-level .lean file
                lfs = [os.path.join(hint_dir, f) for f in sorted(os.listdir(hint_dir)) if f.endswith(".lean") and f != "lakefile.lean"]
                if len(lfs) == 1:
                    challenge_lean = lfs[0]

            if os.path.isfile(cand_exp):
                export_path = cand_exp
            elif challenge_lean:
                tc = resolve_toolchain(comp, toolchain, hint_dir)
                ws = resolve_packages_ws(packages_ws, hint_dir, challenge_lean, tc)
                tlist = None
                if targets_spec:
                    tlist = open(targets_spec).read().split() if os.path.isfile(targets_spec) else targets_spec.replace(",", " ").split()
                elif config_path and os.path.isfile(config_path):
                    tlist = json.load(open(config_path, encoding="utf-8")).get("theorem_names")
                temp_export_dir, export_path, gen_cfg, _ = export_standalone_lean(challenge_lean, tc, ws, threads=threads, targets=tlist)
                if not config_path:
                    config_path = gen_cfg
            else:
                raise RuntimeError(f"directory {target} contains neither challenge.export nor a Challenge.lean")
        elif target.endswith(".lean") and os.path.isfile(target):
            challenge_lean = os.path.realpath(target)
            hint_dir = os.path.dirname(challenge_lean)
            tc = resolve_toolchain(comp, toolchain, hint_dir)
            ws = resolve_packages_ws(packages_ws, hint_dir, challenge_lean, tc)
            tlist = None
            if targets_spec:
                tlist = open(targets_spec).read().split() if os.path.isfile(targets_spec) else targets_spec.replace(",", " ").split()
            elif config_path and os.path.isfile(config_path):
                tlist = json.load(open(config_path, encoding="utf-8")).get("theorem_names")
            temp_export_dir, export_path, gen_cfg, _ = export_standalone_lean(challenge_lean, tc, ws, threads=threads, targets=tlist)
            if not config_path:
                config_path = gen_cfg
        elif os.path.isfile(target):
            export_path = os.path.realpath(target)
            hint_dir = os.path.dirname(export_path)
            if not config_path:
                cand_cfg = os.path.join(hint_dir, "comparator.json")
                if os.path.isfile(cand_cfg):
                    config_path = cand_cfg
            if config_path and os.path.isfile(config_path):
                try:
                    cmod = json.load(open(config_path, encoding="utf-8")).get("challenge_module", "Challenge")
                    cand_lean = module_lean_path(os.path.dirname(os.path.realpath(config_path)), cmod)
                    if cand_lean and os.path.isfile(cand_lean):
                        challenge_lean = cand_lean
                except Exception:
                    pass
        else:
            raise RuntimeError(f"target does not exist: {target}")

        expaudit_bin = ensure_expaudit_bin(threads=threads)
        cmd = [expaudit_bin, "audit", "-j", str(max(1, threads))]
        if solution_mode:
            cmd.append("--solution-mode")
        if config_path:
            cmd += ["--config", os.path.realpath(config_path)]
        if targets_spec:
            cmd += ["--targets", targets_spec]
        if base_index:
            cmd += ["--base-index", os.path.realpath(base_index)]
        elif base_export:
            cmd += ["--base", os.path.realpath(base_export)]
        else:
            bkind, bpath = default_base_index_or_export(tc)
            if bkind == "index":
                cmd += ["--base-index", bpath]
            elif bkind == "export":
                cmd += ["--base", bpath]
        if reading_set_out:   # a private path: main() writes it out without following links
            os.makedirs(os.path.dirname(os.path.abspath(reading_set_out)), exist_ok=True)
            cmd += ["--reading-set", os.path.abspath(reading_set_out)]
        cmd.append(export_path)

        p = subprocess.run(cmd, capture_output=True, text=True)
        if p.returncode not in (0, 1):
            raise RuntimeError(f"expaudit failed (rc={p.returncode}): {p.stderr.strip()}")
        static_res = json.loads(p.stdout)

        # Source-level lints if .lean source is available
        lean_sources = []
        if challenge_lean and os.path.isfile(challenge_lean):
            cdir = os.path.dirname(challenge_lean)
            for fn in sorted(os.listdir(cdir)):
                if fn.endswith(".lean") and fn != "lakefile.lean":
                    lean_sources.append(os.path.join(cdir, fn))
        src_findings = scan_source_lints(lean_sources)

        # Dynamic vacuity/counterexample probes
        do_probe = (challenge_lean is not None) if run_dynamic is None else run_dynamic
        dyn_res = {"ran": False, "wall_s": 0.0, "findings": []}
        if do_probe and challenge_lean and os.path.isfile(challenge_lean):
            tc = resolve_toolchain(comp, toolchain, hint_dir)
            ws = resolve_packages_ws(packages_ws, hint_dir)
            tlist = static_res.get("targets", {}).get("theorem_names", [])
            if tc and tlist:
                dyn_res = vp.run_probes(
                    challenge_lean,
                    tlist,
                    tc,
                    packages_ws=ws,
                    timeout_s=probe_timeout,
                    conjecture_mode=conjecture_mode,
                )

        # Combine and deduplicate findings per (decl, category)
        all_findings = []
        for raw_f in list(static_res.get("findings", [])) + src_findings + list(dyn_res.get("findings", [])):
            f = dict(raw_f)
            f.setdefault("code", f.get("id", "AUDIT"))
            f.setdefault("message", f.get("summary", ""))
            all_findings.append(f)
        all_findings.sort(
            key=lambda f: (-SEV_RANK.get(f.get("severity", "INFO"), 1), f.get("id", ""), f.get("decl", ""))
        )

        counts = {"CRITICAL": 0, "HIGH": 0, "WARN": 0, "INFO": 0}
        for f in all_findings:
            sev = f.get("severity", "INFO")
            counts[sev] = counts.get(sev, 0) + 1

        if counts["CRITICAL"] > 0:
            status = "CRITICAL"
        elif counts["HIGH"] > 0:
            status = "FLAGGED"
        elif counts["WARN"] > 0:
            status = "WARN"
        else:
            status = "CLEAN"

        exit_code = 0
        if fail_on:
            min_r = SEV_RANK.get(fail_on.upper(), 3)
            if any(SEV_RANK.get(f.get("severity", "INFO"), 1) >= min_r for f in all_findings):
                exit_code = 1

        rs_out = dict(static_res.get("reading_set", {}))
        if "statement_closure_decls" in rs_out:
            rs_out.setdefault("total_decls", rs_out["statement_closure_decls"])
            rs_out.setdefault("non_mathlib_decls", rs_out.get("custom_non_target_user_decls", 0))

        result = {
            "tool": "fastverify-audit",
            "version": "1.1",
            "role": "advisor",
            "advisory": True,
            "status": status,
            "exit": exit_code,
            "wall_s": round(time.time() - t0, 4),
            "target": os.path.realpath(target) if os.path.exists(target) else target,
            "challenge_lean": challenge_lean,
            "challenge_export": export_path if not temp_export_dir else "<ephemeral_sandbox_export>",
            "comparator_config": config_path if not temp_export_dir else "<ephemeral_config>",
            "base_mode": static_res.get("base_mode", "unknown"),
            "targets": static_res.get("targets", {}),
            "reading_set": rs_out,
            "proof_support": static_res.get("proof_support", {}),
            "static_lints": {
                "wall_s": static_res.get("wall_s", 0.0),
                "counts": static_res.get("counts", {}),
                "findings": static_res.get("findings", []),
            },
            "source_lints": {
                "files_scanned": len(lean_sources),
                "findings": src_findings,
            },
            "dynamic_probes": dyn_res,
            "counts": counts,
            "findings": all_findings,
        }
        return result
    finally:
        if temp_export_dir:
            shutil.rmtree(temp_export_dir, ignore_errors=True)


def format_human(res):
    rs = res.get("reading_set", {})
    c = res.get("counts", {})
    lines = [
        f"=== fastverify Statement Fidelity Audit [ADVISORY — never changes CS verdicts]: {res['status']} ({res['wall_s']} s) ===",
        f"Target: {res['target']} (base comparison: {res['base_mode']})",
        f"Targets ({len(res.get('targets', {}).get('theorem_names', []))}): {', '.join(res.get('targets', {}).get('theorem_names', [])[:8])}",
        f"Reading Set: {rs.get('statement_closure_decls', 0)} statement-closure decls -> "
        f"{rs.get('base_decls', 0)} unmodified base + "
        f"{rs.get('custom_non_target_user_decls', 0)} custom non-target decls to inspect "
        f"(pure Mathlib statements: {rs.get('pure_mathlib_statements', False)})",
        f"Findings: CRITICAL={c.get('CRITICAL',0)} HIGH={c.get('HIGH',0)} WARN={c.get('WARN',0)} "
        f"(dynamic probes ran: {res.get('dynamic_probes', {}).get('ran', False)})",
    ]
    for f in res.get("findings", []):
        lines.append(f"  [{f['severity']}] {f['id']} @ {f['decl']}: {f['summary']}")
        if f.get("detail"):
            lines.append(f"      {f['detail'][:160]}")
    return "\n".join(lines)


_MOD_COMP = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")


def module_lean_path(base_dir, cmod):
    """the .lean file of the comparator's challenge_module INSIDE base_dir, or None: the module name
    (client data) must be dotted Lean identifier components (no '/', no absolute path, no '..'); the resulting path must
    resolve inside base_dir and must not be a symlink"""
    if not isinstance(cmod, str) or not cmod or not all(_MOD_COMP.match(c) for c in cmod.split(".")):
        return None
    base = os.path.realpath(base_dir)
    cand = os.path.join(base, *cmod.split(".")) + ".lean"
    if os.path.islink(cand) or not os.path.realpath(cand).startswith(base + os.sep):
        return None
    return cand


def _copy_plain(src, dst):
    """copy src to dst iff it is a single-link regular file opened without following a link (O_NOFOLLOW|
    O_NONBLOCK); False (nothing copied) otherwise"""
    import stat as _st
    try:
        fd = os.open(src, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError:
        return False
    try:
        st = os.fstat(fd)
        if not _st.S_ISREG(st.st_mode) or st.st_nlink != 1:
            return False
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with os.fdopen(os.dup(fd), "rb") as fi, open(dst, "xb") as fo:
            shutil.copyfileobj(fi, fo)
        return True
    finally:
        os.close(fd)


def refuse_link_file(path, what):
    """an auxiliary input file of the CLI (--config / --targets file / --base / --base-index): not a symlink, a
    regular file with one link (nothing is followed)"""
    import stat as _st
    if path is None or not os.path.lexists(path):
        return
    st = os.lstat(path)
    if _st.S_ISLNK(st.st_mode):
        raise ValueError("%s %s is a symlink" % (what, path))
    if _st.S_ISREG(st.st_mode) and st.st_nlink != 1:
        raise ValueError("%s %s is a hard-linked file" % (what, path))
    if not (_st.S_ISREG(st.st_mode) or _st.S_ISDIR(st.st_mode)):
        raise ValueError("%s %s is a special file" % (what, path))


def write_nofollow(path, text):
    """write an output file without following a symlink planted at its name (temp file + rename)"""
    d = os.path.dirname(os.path.abspath(path)) or "."
    os.makedirs(d, exist_ok=True)
    tmp = os.path.join(d, ".fv-audit-tmp.%d.%s" % (os.getpid(), os.urandom(4).hex()))
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(text)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def refuse_links(target, max_entries=200000):
    """raise ValueError if `target` (a directory, or the directory holding a target file) contains a symlink,
    a special file or a hard-linked regular file outside .lake/.git (nothing is followed while walking)"""
    import stat as _st
    t = os.path.abspath(target)
    if os.path.islink(t):
        raise ValueError("target %s is a symlink" % target)
    root = t if os.path.isdir(t) else os.path.dirname(t)
    n = 0
    for d, dns, fns in os.walk(root):
        for x in (".lake", ".git"):   # skipped only if it really is a directory
            if x in dns + fns and not _st.S_ISDIR(os.lstat(os.path.join(d, x)).st_mode):
                raise ValueError("%s must be a real directory" % os.path.relpath(os.path.join(d, x), root))
        dns[:] = [x for x in dns if x not in (".lake", ".git")]
        for x in dns + fns:
            if x in (".lake", ".git"):
                continue
            n += 1
            if n > max_entries:
                raise ValueError("more than %d entries" % max_entries)
            p = os.path.join(d, x)
            st = os.lstat(p)
            if _st.S_ISLNK(st.st_mode):
                raise ValueError("symlink %s" % os.path.relpath(p, root))
            if _st.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    raise ValueError("hard-linked file %s" % os.path.relpath(p, root))
            elif not _st.S_ISDIR(st.st_mode):
                raise ValueError("special file %s" % os.path.relpath(p, root))


def main():
    ap = argparse.ArgumentParser(description="fastverify Statement Fidelity & Challenge Anti-Gaming Auditor")
    ap.add_argument("target", help="Challenge directory, .export file, or standalone .lean file")
    ap.add_argument("--config", default=None, help="comparator.json path")
    ap.add_argument("--targets", default=None, help="Target theorem names (comma-separated or file)")
    ap.add_argument("--base", default=None, help="Base library export (e.g. mathlib.export)")
    ap.add_argument("--base-index", default=None, help="Precomputed base index (.baseidx)")
    ap.add_argument("--packages", default=None, help="Trusted Lake workspace holding .lake/packages")
    ap.add_argument("--toolchain", default=None, help="Official Lean toolchain prefix")
    grp = ap.add_mutually_exclusive_group()
    grp.add_argument("--probe", dest="probe", action="store_true", default=None, help="Run sandboxed dynamic vacuity/counterexample probes")
    grp.add_argument("--no-probe", dest="probe", action="store_false", help="Skip dynamic probes (static kernel-AST + reading set only)")
    ap.add_argument("--conjecture-mode", action="store_true", help="Flag elementary tautologies as HIGH severity")
    ap.add_argument("--solution-mode", action="store_true", help="Audit completed/conditional solution export for zero-project-lemma degenerate proofs (F11)")
    ap.add_argument("--probe-timeout", type=int, default=45, help="Dynamic probe wall timeout (seconds)")
    ap.add_argument("--threads", "-j", type=int, default=8, help="Threads for export loading / indexing")
    ap.add_argument("--reading-set", default=None, help="Write minimal human reading set (.lean) to path")
    ap.add_argument("--json", default=None, help="Write full audit JSON report to path")
    ap.add_argument("--human", action="store_true", help="Print human-readable summary instead of JSON on stdout")
    ap.add_argument("--fail-on", default=None, choices=["WARN", "HIGH", "CRITICAL"], help="Exit 1 if findings >= severity exist")
    args = ap.parse_args()

    # the audit never reads, copies, probes or writes a caller's path directly: every path
    # is checked WITHOUT resolving it (bin/fv's local policy: mapped onto mcp_server.cli_roots(), every component walked
    # with O_NOFOLLOW, so a symlinked target, an intermediate directory symlink or a link inside the tree is refused, never
    # followed); the target (a directory: its tree; a file: it and its directory's .lean / comparator.json /
    # lean-toolchain files) and --config / a --targets file are audited as PRIVATE copies made from the opened fds; --json
    # and --reading-set are created inside their directory opened without following links (a planted link is replaced).
    # refuse_links / refuse_link_file / write_nofollow lstat'ed only the leaf.
    mp = vp.fv_paths()
    roots = mp.cli_roots()
    itmp = tempfile.mkdtemp(prefix="fvaudit-in.")

    def refused(msg):
        print(json.dumps({"tool": "fastverify-audit", "status": "ERROR", "exit": 2, "error": "refused: %s" % msg}),
              file=sys.stderr)
        sys.exit(2)

    def write_out(canon, text):
        dfd = mp.open_nofollow_under(os.path.dirname(canon), roots, want_dir=True, create=True)
        try:
            mp.write_file_at(dfd, os.path.basename(canon), text)
        finally:
            os.close(dfd)

    try:
        try:
            tgt = mp.client_abspath(args.target, roots, must_exist=True, allow_dotdot=True)
            priv_root = os.path.join(itmp, "t")
            if os.path.isdir(tgt):
                orig_root, priv_target, keep = tgt, priv_root, None
            else:
                bn = os.path.basename(tgt)
                orig_root, priv_target = os.path.dirname(tgt), os.path.join(priv_root, bn)
                keep = lambda n, bn=bn: n == bn or n.endswith(".lean") or n in ("comparator.json", "lean-toolchain")  # noqa: E731
            dfd = mp.open_nofollow_under(orig_root, roots, want_dir=True)
            try:
                mp.copy_client_tree(dfd, priv_root, file_filter=keep)
            finally:
                os.close(dfd)
            cfg_priv = None
            if args.config:
                cfg_priv = os.path.join(itmp, "config.json")
                mp.copy_client_file(mp.local_path_under(args.config, roots), cfg_priv, roots)
            targets_spec = args.targets
            if args.targets and (os.sep in args.targets or os.path.lexists(args.targets)):
                tc_ = mp.client_abspath(args.targets, roots, must_exist=False, expect_dir=False, allow_dotdot=True)
                if os.path.lexists(tc_):
                    targets_spec = os.path.join(itmp, "targets.txt")
                    mp.copy_client_file(tc_, targets_spec, roots)
            aux = {}
            for flag, val in (("--base", args.base), ("--base-index", args.base_index)):
                if val:   # large operator libraries: checked in place (no link at any component, one link)
                    c = mp.client_abspath(val, roots, must_exist=True, expect_dir=False, allow_dotdot=True)
                    if os.lstat(c).st_nlink != 1:
                        raise mp.ClientPathError("%s %s is a hard-linked file" % (flag, val))
                    aux[flag] = c
            pk = args.packages
            if pk and pk.lower() != "none":
                pk = mp.client_abspath(pk, roots, must_exist=True, expect_dir=True, allow_dotdot=True)
            tcx = mp.client_abspath(args.toolchain, roots, must_exist=True, expect_dir=True, allow_dotdot=True) \
                if args.toolchain else None   # an explicit toolchain dir: no link at any component
            json_out = mp.client_abspath(args.json, roots, must_exist=False, expect_dir=False, allow_dotdot=True) \
                if args.json else None
            rs_out = mp.client_abspath(args.reading_set, roots, must_exist=False, expect_dir=False, allow_dotdot=True) \
                if args.reading_set else None
        except (mp.ClientPathError, OSError, ValueError) as e:
            refused(e)
        rs_priv = os.path.join(itmp, "reading_set.lean") if rs_out else None

        def relocate(text):
            return text.replace(json.dumps(priv_root)[1:-1], json.dumps(orig_root)[1:-1]).replace(priv_root, orig_root)

        try:
            res = run_audit(
                priv_target,
                config_path=cfg_priv,
                targets_spec=targets_spec,
                base_export=aux.get("--base"),
                base_index=aux.get("--base-index"),
                packages_ws=pk,
                toolchain=tcx,
                run_dynamic=args.probe,
                conjecture_mode=args.conjecture_mode,
                solution_mode=args.solution_mode,
                reading_set_out=rs_priv,
                threads=args.threads,
                probe_timeout=args.probe_timeout,
                fail_on=args.fail_on,
            )
        except Exception as e:
            err_obj = {"tool": "fastverify-audit", "status": "ERROR", "exit": 2, "error": relocate(str(e))}
            if json_out:
                try:
                    write_out(json_out, json.dumps(err_obj, indent=2))
                except (mp.ClientPathError, OSError):
                    pass
            print(json.dumps(err_obj), file=sys.stderr)
            sys.exit(2)

        js = relocate(json.dumps(res, indent=2, ensure_ascii=False))
        try:
            if json_out:
                write_out(json_out, js + "\n")
            if rs_out and os.path.isfile(rs_priv):
                with open(rs_priv, encoding="utf-8") as f:
                    write_out(rs_out, relocate(f.read()))
        except (mp.ClientPathError, OSError) as e:
            refused("output not written without following links: %s" % e)
        if args.human:
            print(format_human(json.loads(js)))
        else:
            print(js)
        sys.exit(res["exit"])
    finally:
        shutil.rmtree(itmp, ignore_errors=True)


if __name__ == "__main__":
    main()

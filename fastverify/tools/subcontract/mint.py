#!/usr/bin/python3 -I
"""mint.py — Zero-trust Sub-Challenge Minter for multi-agent collaboration.

Given a sorry-laden Lean 4 project and its clean parent challenge:
  1. Verifies the parent repo conditionally modulo its sorry frontier using
     `check/frontier/check-frontier.sh` (or accepts an already-verified conditional run).
  2. For every open frontier lemma L_i in F, mints a standalone, SHA-256-pinned
     Sub-Challenge Package under OUT/subchallenges/<safe_Li>/:
       - subchallenge.export       (minimal closure of L_i + permitted_axioms + primitives + Quot.*)
       - subchallenge.export.sha256
       - comparator.json           (theorem_names: [L_i], strict permitted_axioms without sorryAx)
       - task.json                 (exact source span, statement, prompt_code, hashes)
  3. Writes OUT/manifest.json and OUT/ledger.json (progress ledger tracking open/closed/rejected).

Trust note (zero new TCB):
  - Minting is dispatcher-side untrusted tooling. Each minted sub-challenge export is produced
    from the dispatcher's verified base build tree using the package's exporter (E1 with E0
    fallback, or --exporter E0 for official lean4export), and checked to match the exact statement
    type_sha256 reported by check-frontier.sh.
  - Untrusted proving agents NEVER have write access to subchallenge.export or its SHA-256 pin,
    so they cannot weaken L_i, alter shared definitions, or smuggle axioms/sorry.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
import common as C


def export_targets_for(theorem_names, permitted_axioms):
    targets = []
    if "Quot.sound" in permitted_axioms:
        targets += ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
    targets += list(theorem_names)
    targets += list(permitted_axioms)
    targets += list(C.PRIMITIVES)
    # preserve order, dedupe
    out, seen = [], set()
    for t in targets:
        if t not in seen:
            out.append(t)
            seen.add(t)
    return out


def run_exporter(build_tree, module_name, targets, out_export, packages_ws, tc_prefix,
                 fv_root, threads=8, prefer_official=False):
    """Export `targets` from `build_tree` (already compiled .oleans) into `out_export`."""
    lean_path = C.collect_lean_path(build_tree, packages_ws)
    os.makedirs(os.path.dirname(os.path.realpath(out_export)), exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="fv-mint-exp-") as td:
        tfile = os.path.join(td, "targets.txt")
        with open(tfile, "w", encoding="utf-8") as f:
            for t in targets:
                f.write(t + "\n")
        if not prefer_official:
            # Try E1 fast native exporter (export/export.sh)
            exp_sh = os.path.join(fv_root, "export", "export.sh")
            jfile = os.path.join(td, "exp.json")
            cmd = [
                exp_sh,
                "--lean-path", lean_path,
                "--module", module_name,
                "--targets-nl", tfile,
                "--toolchain", tc_prefix,
                "--project", build_tree,
                "--out", out_export,
                "--threads", str(min(threads, 32)),
                "--json", jfile,
            ]
            t0 = time.monotonic()
            p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if p.returncode == 0 and os.path.isfile(out_export) and os.path.getsize(out_export) > 0:
                return "E1", round(time.monotonic() - t0, 3)

        # Fallback / explicit E0: official lean4export inside bwrap
        tc_file = os.path.join(build_tree, "lean-toolchain")
        tc_spec = open(tc_file, encoding="utf-8").read().strip() if os.path.exists(tc_file) else "leanprover/lean4:v4.33.1"
        e0_bin = C.resolve_official_exporter(tc_spec, tc_prefix, fv_root)
        ro = [build_tree, packages_ws, tc_prefix, os.path.dirname(e0_bin)]
        argv = [e0_bin, module_name, "--"] + list(targets)
        env_extra = {
            "PATH": f"{tc_prefix}/bin:/usr/bin:/bin",
            "LEAN_PATH": lean_path,
            "HOME": "/tmp",
            "TMPDIR": "/tmp",
        }
        rc, out, err, wall = C.run_bwrap(argv, ro_binds=ro, rw_binds=[], env_extra=env_extra, cwd=build_tree, timeout=600)
        if rc != 0 or not out:
            raise RuntimeError(f"E0 export failed (rc={rc}): {err[:400]}")
        with open(out_export, "w", encoding="utf-8") as f:
            f.write(out)
        return "E0", wall


def build_base_repo(project_dir, challenge_dir, packages_ws, tc_prefix, work_out, fv_root, threads, preset="sound",
                    challenge_sha256=None):
    """Build project_dir and export its closure for conditional verification.
    Uses build/official-build.sh (sandboxed) keeping the build tree with .oleans.
    """
    proj_copy = os.path.join(work_out, "base_proj")
    if os.path.exists(proj_copy):
        shutil.rmtree(proj_copy)
    shutil.copytree(
        project_dir, proj_copy, symlinks=True,
        ignore=lambda d, names: [".lake"] if os.path.realpath(d) == os.path.realpath(project_dir) else [],
    )
    b0 = os.path.join(fv_root, "build", "official-build.sh")
    jfile = os.path.join(work_out, "build.json")
    t0 = time.monotonic()
    cmd = [b0, proj_copy, packages_ws, tc_prefix, "--threads", str(threads), "--json", jfile]
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    wall = round(time.monotonic() - t0, 3)
    if p.returncode != 0:
        raise RuntimeError(f"base build failed (rc={p.returncode}): {p.stdout.decode('utf-8', 'replace')[-400:]} {p.stderr.decode('utf-8', 'replace')[-600:]}")
    return proj_copy, wall


def mint(args):
    t_start = time.monotonic()
    fv_root = os.path.realpath(args.fv or C.FASTVERIFY_ROOT)
    project_dir = os.path.realpath(args.project)
    challenge_dir = os.path.realpath(args.challenge)
    packages_ws = os.path.realpath(args.packages or challenge_dir)
    out_dir = os.path.realpath(args.out)
    os.makedirs(out_dir, exist_ok=True)

    chal_export = os.path.join(challenge_dir, "challenge.export")
    comp_json_path = args.comparator_config or os.path.join(challenge_dir, "comparator.json")
    if not os.path.isfile(chal_export):
        raise RuntimeError(f"challenge.export missing at {chal_export}")
    if not os.path.isfile(comp_json_path):
        raise RuntimeError(f"comparator.json missing at {comp_json_path}")

    # GOAL S1(1): the parent challenge export must be THE official one - the caller's own pin
    # is required (as bin/fastverify --preset sound); a self-hash of a given file has no provenance
    if not args.challenge_sha256 or not re.fullmatch(r"[0-9a-f]{64}", args.challenge_sha256):
        raise RuntimeError("--challenge-sha256 HEX (64 lowercase hex: the sha256 of the official parent challenge export, "
                           "GOAL S1(1)) is required")
    chal_sha = C.sha256_file(chal_export)
    if chal_sha != args.challenge_sha256:
        raise RuntimeError(f"challenge.export sha256 mismatch: got {chal_sha}, expected {args.challenge_sha256}")
    if args.frontier_json:
        # a cached check-frontier.sh receipt has no authenticated binding to THIS run's base
        # export, parent challenge and parent comparator, so it is never used (copying its verdict into a manifest that
        # records the current pins would bind it to inputs it never saw); refused before anything is built (no caller in the package passes it)
        raise RuntimeError("--frontier-json is not accepted: a cached receipt is not bound to the current base export "
                           "and pins; mint always runs the parent check itself")
    # the caller's pin of comparator.json is required alongside the challenge pin
    if not args.comparator_sha256 or not re.fullmatch(r"[0-9a-f]{64}", args.comparator_sha256):
        raise RuntimeError("--comparator-sha256 HEX (64 lowercase hex: the sha256 of the parent comparator.json) is required "
                           "together with --challenge-sha256")
    with open(comp_json_path, "rb") as f:   # read ONCE: the pinned bytes are the ones parsed
        comp_bytes = f.read()
    comp_cfg_sha = hashlib.sha256(comp_bytes).hexdigest()
    if comp_cfg_sha != args.comparator_sha256:
        raise RuntimeError(f"comparator.json sha256 mismatch: got {comp_cfg_sha}, expected {args.comparator_sha256}")

    comp_cfg = json.loads(comp_bytes.decode("utf-8"))
    sol_module = comp_cfg["solution_module"]
    chal_module = comp_cfg["challenge_module"]
    parent_theorems = comp_cfg["theorem_names"]
    permitted_axioms = comp_cfg["permitted_axioms"]
    tc_prefix, tc_spec = C.resolve_toolchain_for_project(project_dir, fv_root)

    # Step 1: Build base tree (or reuse --base-build-tree)
    work_dir = os.path.join(out_dir, "base")
    # nothing of an earlier mint in the same OUT is ever read: OUT/base (its build tree,
    # base.export, the parent receipt frontier.json, fr_keep), OUT/manifest.json and OUT/subchallenges are removed first,
    # so a parent check that writes nothing gives no verdict - never the earlier receipt
    for _given in (args.base_build_tree, args.base_export):
        if _given and (os.path.realpath(_given) + os.sep).startswith(os.path.realpath(work_dir) + os.sep):
            raise RuntimeError(f"{_given} is inside {work_dir}, which mint clears before it runs: give it outside OUT/base")
    for _stale in (work_dir, os.path.join(out_dir, "manifest.json"), os.path.join(out_dir, "subchallenges")):
        if os.path.islink(_stale) or (os.path.lexists(_stale) and not os.path.isdir(_stale)):
            os.unlink(_stale)
        elif os.path.isdir(_stale):
            shutil.rmtree(_stale)
        if os.path.lexists(_stale):
            raise RuntimeError(f"cannot remove the earlier mint output {_stale}")
    os.makedirs(work_dir, exist_ok=True)
    if args.base_build_tree:
        base_tree = os.path.realpath(args.base_build_tree)
        build_s = 0.0
    else:
        base_tree, build_s = build_base_repo(project_dir, challenge_dir, packages_ws, tc_prefix, work_dir, fv_root, args.threads)

    # Step 2: Export base closure (or reuse --base-export)
    base_export = os.path.join(work_dir, "base.export")
    if args.base_export:
        shutil.copy2(args.base_export, base_export)
        exp_mode, exp_s = "given", 0.0
    else:
        parent_targets = export_targets_for(parent_theorems + comp_cfg.get("definition_names", []), permitted_axioms)
        try:
            exp_mode, exp_s = run_exporter(
                base_tree, sol_module, parent_targets, base_export, packages_ws, tc_prefix,
                fv_root, threads=args.threads, prefer_official=(args.exporter == "E0"),
            )
        except RuntimeError as e:
            msg = str(e)
            # Missing target theorem/definition (e.g. planner typo'd main theorem name) -> clean REJECTED (exit 1),
            # matching the official comparator instead of NO_VERDICT.
            if any(tok in msg.lower() for tok in ("not found", "unknown constant", "missing constant")):
                out_err = {
                    "ok": False,
                    "verdict": "REJECTED",
                    "exit": 1,
                    "category": "TARGET_MISSING",
                    "reason": msg,
                }
                C.atomic_write_json(os.path.join(out_dir, "manifest.json"), out_err)
                print(json.dumps(out_err, ensure_ascii=False))
                return 1
            raise
    base_export_sha = C.sha256_file(base_export)

    # Step 3: Run D06's check/frontier/check-frontier.sh (with --keep so sketch S' is preserved!)
    frontier_json_path = os.path.join(work_dir, "frontier.json")
    fr_keep_dir = os.path.join(work_dir, "fr_keep")
    if os.path.lexists(frontier_json_path) or os.path.lexists(fr_keep_dir):   # OUT/base was cleared in step 1
        raise RuntimeError("an earlier parent receipt is present in OUT/base: refused")
    if True:   # always: the parent check of THIS run (a cached --frontier-json receipt is refused up front)
        cf_sh = os.path.join(fv_root, "check", "frontier", "check-frontier.sh")
        if not os.path.isfile(cf_sh):
            raise RuntimeError(f"missing {cf_sh}")
        cf_cmd = [
            cf_sh, base_export, chal_export, comp_json_path,
            "--threads", str(args.threads),
            "--json", frontier_json_path,
            "--keep", fr_keep_dir,
            "--challenge-sha256", chal_sha, "--comparator-sha256", comp_cfg_sha,   # the judge verifies the pins on its own private copies
        ]
        if args.integrity_cache:
            cf_cmd += ["--integrity-cache", args.integrity_cache]
        t0 = time.monotonic()
        p = subprocess.run(cf_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        frontier_s = round(time.monotonic() - t0, 3)
        if not os.path.isfile(frontier_json_path):
            raise RuntimeError(f"check-frontier.sh produced no JSON (rc={p.returncode}): {p.stderr.decode('utf-8','replace')[-400:]}")
        frontier_res = json.load(open(frontier_json_path, encoding="utf-8"))
        # the receipt counts only with the exit code that goes with its verdict (check-frontier.sh: ACCEPTED 0,
        # REJECTED 1, CONDITIONAL 3); anything else is no verdict (exit 2)
        _want = {"ACCEPTED": 0, "REJECTED": 1, "CONDITIONAL": 3}.get(frontier_res.get("verdict") if isinstance(frontier_res, dict) else None)
        if _want is None or p.returncode != _want:
            raise RuntimeError(f"check-frontier.sh exit {p.returncode} does not match its verdict "
                               f"{frontier_res.get('verdict') if isinstance(frontier_res, dict) else None!r}: no verdict")
    fr_s_prime = os.path.join(fr_keep_dir, "fr", "solution.frontier.export")

    verdict = frontier_res.get("verdict")
    if verdict not in ("CONDITIONAL", "ACCEPTED"):
        out_err = {
            "ok": False,
            "verdict": verdict,
            "reason": frontier_res.get("reason"),
            "frontier_result": frontier_res,
        }
        C.atomic_write_json(os.path.join(out_dir, "manifest.json"), out_err)
        print(json.dumps(out_err, ensure_ascii=False))
        return 1 if verdict == "REJECTED" else 2

    frontier_entries = frontier_res.get("frontier") or []
    sub_dir = os.path.join(out_dir, "subchallenges")
    os.makedirs(sub_dir, exist_ok=True)

    # Step 4: Mint one standalone, SHA-256-pinned sub-challenge per open frontier lemma
    # Supports BOTH top-level sorried theorems AND inline proof-sketch subgoals (`in_declaration` / `._fv_sorry_k`).
    # parallelize independent read-only sub-challenge exports across `--jobs` workers (default min(8, threads)).
    minted = []
    mint_t0 = time.monotonic()
    jobs = args.jobs if args.jobs and args.jobs > 0 else min(8, max(1, args.threads))
    per_exp_threads = max(1, min(16, args.threads // max(1, min(jobs, max(1, len(frontier_entries))))))

    # Pre-resolve locations & prepare directories deterministically
    prepared = []
    for idx, entry in enumerate(frontier_entries):
        lname = entry["name"] if isinstance(entry, dict) else str(entry)
        ltype = entry.get("type", "") if isinstance(entry, dict) else ""
        ltype_sha = entry.get("type_sha256", C.sha256_str(ltype)) if isinstance(entry, dict) else C.sha256_str("")
        in_decl = entry.get("in_declaration") if isinstance(entry, dict) else None
        is_sketch = bool(in_decl)
        sorry_idx = None
        if is_sketch:
            m_si = re.search(r"\._fv_sorry_(\d+)$", lname)
            sorry_idx = int(m_si.group(1)) if m_si else 1
        sid = C.safe_id(lname)
        sdir = os.path.join(sub_dir, sid)
        os.makedirs(sdir, exist_ok=True)
        loc = C.locate_lemma_in_project(project_dir, in_decl if is_sketch else lname)
        sub_mod = loc["module"] if loc else sol_module
        sub_exp_path = os.path.join(sdir, "subchallenge.export")
        prepared.append((idx, lname, ltype, ltype_sha, in_decl, is_sketch, sorry_idx, sid, sdir, loc, sub_mod, sub_exp_path))

    def _export_one(item):
        idx, lname, _ltype, _ltype_sha, _in_decl, is_sketch, _sorry_idx, _sid, _sdir, loc, sub_mod, sub_exp_path = item
        if is_sketch and os.path.isfile(fr_s_prime):
            # Inline sketch subgoal: D06's rewritten S' ALREADY contains `lname` as a first-class `thm`
            # record with the authoritative kernel-abstracted type! Copy (reflink) directly -> zero extra export!
            t_sk = time.monotonic()
            p_cp = subprocess.run(["cp", "--reflink=auto", fr_s_prime, sub_exp_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if p_cp.returncode != 0:
                shutil.copy2(fr_s_prime, sub_exp_path)
            smode, swall = "frontier-S'", round(time.monotonic() - t_sk, 3)
        else:
            # Top-level open theorem: export minimal standalone sub-challenge directly from verified base build tree
            sub_targets = export_targets_for([lname], permitted_axioms)
            smode, swall = run_exporter(
                base_tree, sub_mod if loc else sol_module, sub_targets, sub_exp_path, packages_ws, tc_prefix,
                fv_root, threads=per_exp_threads, prefer_official=(args.exporter == "E0"),
            )
        sub_exp_sha = C.sha256_file(sub_exp_path)
        with open(sub_exp_path + ".sha256", "w", encoding="utf-8") as f:
            f.write(f"{sub_exp_sha}  subchallenge.export\n")
        return idx, smode, swall, sub_exp_sha

    export_results = {}
    if jobs > 1 and len(prepared) > 1:
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(jobs, len(prepared))) as ex:
            for idx, smode, swall, sub_exp_sha in ex.map(_export_one, prepared):
                export_results[idx] = (smode, swall, sub_exp_sha)
    else:
        for item in prepared:
            idx, smode, swall, sub_exp_sha = _export_one(item)
            export_results[idx] = (smode, swall, sub_exp_sha)

    sketch_pp_cache = {}
    sketch_pp_used = {}
    for idx, lname, ltype, ltype_sha, in_decl, is_sketch, sorry_idx, sid, sdir, loc, sub_mod, sub_exp_path in prepared:
        smode, swall, sub_exp_sha = export_results[idx]

        # Strict comparator.json: ONLY L_i, ZERO definition holes, ZERO sorryAx!
        sub_comp = {
            "challenge_module": sub_mod,
            "solution_module": sub_mod,
            "theorem_names": [lname],
            "definition_names": [],
            "permitted_axioms": [a for a in permitted_axioms if a != "sorryAx"],
            "enable_nanoda": False,
        }
        sub_comp_path = os.path.join(sdir, "comparator.json")
        C.atomic_write_json(sub_comp_path, sub_comp)
        sub_comp_sha = C.sha256_file(sub_comp_path)

        header_text = None
        prompt_code = None
        source_sorry_idx = sorry_idx
        sketch_binders = []
        if is_sketch and loc:
            if in_decl not in sketch_pp_cache:
                full_file_src = open(loc["abs_file"], encoding="utf-8").read()
                sketch_pp_cache[in_decl] = C.extract_sketch_subgoals_via_lean(
                    full_file_src, loc, base_tree, packages_ws, tc_prefix,
                )
                sketch_pp_used[in_decl] = set()
            pp_info = C.match_sketch_subgoal_pp(sketch_pp_cache[in_decl], ltype, sorry_idx, sketch_pp_used[in_decl])
            if pp_info and pp_info.get("goal"):
                source_sorry_idx = pp_info.get("source_index", sorry_idx)
                sketch_binders = list(pp_info.get("binders") or [])
                bs = (" " + " ".join(sketch_binders)) if sketch_binders else ""
                header_text = f"theorem _root_.{lname}{bs} : {pp_info['goal']}"
            elif ltype:
                header_text = f"theorem _root_.{lname} : {ltype}"
            if header_text:
                prompt_code = loc["context_before"] + header_text + " := by\n  sorry\n"
        elif loc:
            header_text, _ = C.split_theorem_header_and_proof(loc["source_text"])
            if header_text:
                prompt_code = loc["context_before"] + header_text + " := by\n  sorry\n"

        task = {
            "id": sid,
            "index": idx,
            "lemma": lname,
            "sketch_subgoal": is_sketch,
            "in_declaration": in_decl,
            "sorry_index": sorry_idx,
            "source_sorry_index": source_sorry_idx,
            "sketch_binders": sketch_binders,
            "module": sub_mod,
            "rel_file": loc["rel_file"] if loc else None,
            "start_line": loc["start_line"] if loc else None,
            "end_line": loc["end_line"] if loc else None,
            "statement_header": header_text,
            "source_text": loc["source_text"] if loc else None,
            "type_pretty": ltype,
            "type_sha256": ltype_sha,
            "subchallenge_export": sub_exp_path,
            "subchallenge_sha256": sub_exp_sha,
            "subchallenge_size_bytes": os.path.getsize(sub_exp_path),
            "comparator_json": sub_comp_path,
            "comparator_sha256": sub_comp_sha,
            "export_mode": smode,
            "export_s": swall,
            "parent_challenge_sha256": chal_sha,
            "prompt_code": prompt_code,
        }
        C.atomic_write_json(os.path.join(sdir, "task.json"), task)
        minted.append({
            "id": sid,
            "lemma": lname,
            "sketch_subgoal": is_sketch,
            "in_declaration": in_decl,
            "sorry_index": sorry_idx,
            "source_sorry_index": source_sorry_idx,
            "module": sub_mod,
            "rel_file": task["rel_file"],
            "start_line": task["start_line"],
            "end_line": task["end_line"],
            "type_sha256": ltype_sha,
            "subchallenge_sha256": sub_exp_sha,
            "comparator_sha256": sub_comp_sha,
            "subchallenge_size_bytes": task["subchallenge_size_bytes"],
            "task_json": os.path.join(sdir, "task.json"),
            "export_s": swall,
        })

    mint_s = round(time.monotonic() - mint_t0, 3)

    # Step 5: Write manifest.json and initial ledger.json
    manifest = {
        "schema": "fv-subcontract-manifest-v1",
        "created_at": C.now_iso(),
        "project": project_dir,
        "base_build_tree": base_tree,
        "challenge": challenge_dir,
        "challenge_export": chal_export,
        "challenge_sha256": chal_sha,
        "challenge_sha256_pinned_by_caller": True,   # mint refuses to run without the caller's pin
        "comparator_config": comp_json_path,
        "comparator_sha256": comp_cfg_sha,
        "comparator_sha256_pinned_by_caller": True,   # mint refuses to run without the caller's comparator pin
        "packages_workspace": packages_ws,
        "toolchain": tc_spec,
        "toolchain_prefix": tc_prefix,
        "solution_module": sol_module,
        "parent_theorems": parent_theorems,
        "permitted_axioms": permitted_axioms,
        "base_export": base_export,
        "base_export_sha256": base_export_sha,
        "base_verdict": verdict,
        "frontier_size": len(minted),
        "subchallenges": minted,
        "timing_s": {
            "base_build": build_s,
            "base_export": exp_s,
            "frontier_check": frontier_s,
            "mint_subchallenges": mint_s,
            "total": round(time.monotonic() - t_start, 3),
        },
    }
    C.atomic_write_json(os.path.join(out_dir, "manifest.json"), manifest)

    ledger = {
        "schema": "fv-progress-ledger-v1",
        "created_at": C.now_iso(),
        "updated_at": C.now_iso(),
        "parent_challenge_sha256": chal_sha,
        "parent_verdict": verdict,
        "initial_frontier_size": len(minted),
        "remaining_count": len(minted),
        "closed_count": 0,
        "lemmas": {
            m["lemma"]: {
                "id": m["id"],
                "status": "open",
                "sketch_subgoal": bool(m.get("sketch_subgoal")),
                "in_declaration": m.get("in_declaration"),
                "sorry_index": m.get("sorry_index"),
                "source_sorry_index": m.get("source_sorry_index"),
                "type_sha256": m["type_sha256"],
                "subchallenge_sha256": m["subchallenge_sha256"],
                "rel_file": m["rel_file"],
                "closed_by": None,
                "closed_at": None,
                "triage": None,
                "rejected_attempts": [],
            }
            for m in minted
        },
        "history": [
            {
                "event": "mint",
                "at": C.now_iso(),
                "verdict": verdict,
                "frontier_size": len(minted),
                "base_export_sha256": base_export_sha,
            }
        ],
    }
    C.atomic_write_json(os.path.join(out_dir, "ledger.json"), ledger)

    summary = {
        "ok": True,
        "verdict": verdict,
        "frontier_size": len(minted),
        "out": out_dir,
        "manifest": os.path.join(out_dir, "manifest.json"),
        "ledger": os.path.join(out_dir, "ledger.json"),
        "timing_s": manifest["timing_s"],
    }
    print(json.dumps(summary, ensure_ascii=False))
    return 0


def main():
    ap = argparse.ArgumentParser(description="Mint SHA-256-pinned sub-challenges from a sorry-laden project's verified frontier.")
    ap.add_argument("project", help="Path to the sorry-laden Lean 4 project")
    ap.add_argument("challenge", help="Path to the clean parent challenge directory (challenge.export + comparator.json)")
    ap.add_argument("out", help="Output directory for minted sub-challenges, manifest.json, and ledger.json")
    ap.add_argument("--challenge-sha256", default=None, help="Expected SHA-256 of parent challenge.export (required)")
    ap.add_argument("--comparator-sha256", default=None, help="Expected SHA-256 of the parent comparator.json (required "
                    "together with --challenge-sha256; recorded in manifest.json)")
    ap.add_argument("--comparator-config", default=None, help="Override comparator.json path")
    ap.add_argument("--packages", default=None, help="Trusted packages workspace (default: challenge)")
    ap.add_argument("--fv", default=None, help="fastverify root")
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--jobs", type=int, default=0, help="Parallel sub-challenge export workers (default: min(8, threads))")
    ap.add_argument("--exporter", choices=["E1", "E0"], default="E1")
    ap.add_argument("--base-build-tree", default=None, help="Reuse an already-built project tree")
    ap.add_argument("--base-export", default=None, help="Reuse an already-exported base.export")
    ap.add_argument("--frontier-json", default=None, help="REFUSED (a cached receipt is not bound to the current "
                    "inputs and pins); kept only to give that refusal")
    ap.add_argument("--integrity-cache", default=None, help="Integrity cache dir for check-frontier.sh")
    ap.add_argument("--experimental", action="store_true", help="REQUIRED in v0.1: the subcontract engine (mint / subverify / "
                    "merge) ships EXPERIMENTAL; without this flag the command is refused (exit 2)")
    args = ap.parse_args()
    if not args.experimental:   # subcontract ships EXPERIMENTAL, opt-in only
        print(json.dumps({"ok": False, "verdict": "NO_VERDICT", "exit": 2,
                          "error": "mint.py is EXPERIMENTAL in v0.1 (subcontract engine): pass --experimental to run it"}))
        sys.exit(2)
    C.install_interrupt_handler("mint.py")   # a signal is no verdict: exit 2, children killed
    try:
        sys.exit(mint(args))
    except Exception as e:
        print(json.dumps({"ok": False, "error": str(e)}))
        sys.exit(2)


if __name__ == "__main__":
    main()

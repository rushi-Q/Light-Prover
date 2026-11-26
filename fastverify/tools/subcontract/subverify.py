#!/usr/bin/python3 -I
"""subverify.py — Zero-Trust Sub-Proof Verification Gate.

Judges an untrusted agent's proof submission for a single minted frontier lemma L_i
against its SHA-256-pinned sub-challenge (subchallenge.export + comparator.json).

Trust model (zero new TCB):
  - Untrusted submission code is compiled ONLY inside a network-less bwrap sandbox
    against a private copy of the base .olean build tree.
  - The final verdict comes EXCLUSIVELY from the unchanged trusted sound check
    (`check/sound/check-sound.sh`, or `check-sound-svc.sh --integrity-cache`).
  - Because `subchallenge.export` and its SHA-256 pin are immutable and verifier-owned,
    an untrusted agent CANNOT move the goalposts:
      * weakening L_i's statement or modifying a shared `def` -> STATEMENT_DRIFT (REJECTED)
      * smuggling `sorry`, `native_decide`, custom `axiom`   -> ILLEGAL_AXIOM (REJECTED)
      * `set_option debug.skipKernelTC true in decide +kernel` -> KERNEL_REJECT (REJECTED)
      * timeout / crash / decline                            -> NO_VERDICT (never accepted!)
"""
import argparse
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
import common as C
import mint as M


def classify_rejection(reason, ccmp_log=""):
    txt = (reason or "") + "\n" + (ccmp_log or "")
    if re.search(r"statement do not match|Const does not match|Const not found in solution|constant kind don't match", txt, re.I):
        if "theorem statement do not match" in txt:
            return "STATEMENT_DRIFT"
        if "Const does not match between challenge and target" in txt:
            return "DEF_OR_STATEMENT_DRIFT"
        return "STATEMENT_DRIFT"
    if re.search(r"Illegal axiom|Axiom .* is not permitted|sorryAx|native_decide\.ax_|Lean\.ofReduceBool|Lean\.trustCompiler", txt, re.I):
        return "ILLEGAL_AXIOM"
    if re.search(r"Lean default exited with 1|gruszka.*exited with 1|while replaying|kernel rejects", txt, re.I):
        return "KERNEL_REJECT"
    return "REJECTED"


def apply_submission_to_file(orig_file_text, task, submission_text, mode="auto"):
    """Apply an agent's submission to `orig_file_text`, returning (new_file_text, spliced_decl_text, mode_used).

    Supported modes:
      - 'full-file': submission_text replaces the entire module file (still checked by compareAt against pinned subchallenge!).
      - 'splice-decl': extract the declaration for `task['lemma']` from submission_text and splice into orig span.
      - 'splice-body': keep the original statement header verbatim and splice ONLY the proof body after `:=`.
      - 'auto': if submission_text contains `import ` at top -> 'full-file' ONLY when --allow-full-file, else
                extract the declaration block for `task['lemma']` and splice into its exact original span!
    """
    full_name = task["lemma"]
    short_name = full_name.split(".")[-1]
    decls = C.scan_lean_declarations(orig_file_text)
    target_decl = None
    for d in decls:
        if d["full_name"] == full_name:
            target_decl = d
            break
    if target_decl is None:
        # fallback: short name
        for d in decls:
            if d["short_name"] == short_name:
                target_decl = d
                break

    if mode == "full-file":
        return submission_text, submission_text, "full-file"

    # Inline proof-sketch subgoal (D06 `in_declaration` / `._fv_sorry_k`): insert the standalone theorem
    # right BEFORE the enclosing declaration (`in_declaration`) under `_root_.<full_name>` so it compiles
    # with all prior defs/imports and exports under the exact name pinned in S'!
    if task.get("sketch_subgoal"):
        if re.search(r"^\s*import\s+", submission_text, re.M):
            return submission_text, submission_text, "full-file"
        in_decl = task.get("in_declaration") or ""
        anchor = next((d for d in decls if d["full_name"] == in_decl), None)
        if anchor is None and in_decl:
            in_short = in_decl.split(".")[-1]
            anchor = next((d for d in decls if d["short_name"] == in_short), None)
        ext = C.extract_lemma_proof_from_submission(submission_text, full_name, short_name)
        if not ext:
            ext = C.extract_lemma_proof_from_submission(submission_text, "_root_." + full_name, full_name)
        stmt_hdr = task.get("statement_header") or f"theorem _root_.{full_name}"
        if ext and ext["kind"] == "decl":
            decl_blk = ext.get("block_text") or ext["decl_text"]
            # Ensure the theorem name is `_root_.<full_name>` so namespaces don't double-prefix it
            decl_blk = re.sub(
                rf"\b(theorem|lemma)\s+(?:_root_\.)?(?:{re.escape(full_name)}|{re.escape(short_name)})\b",
                rf"\1 _root_.{full_name}",
                decl_blk, count=1,
            )
        elif ext and ext.get("proof"):
            decl_blk = f"{stmt_hdr} :=\n{ext['proof']}"
        else:
            decl_blk = submission_text.strip()
        ins_pos = anchor["start_idx"] if anchor is not None else len(orig_file_text)
        new_file = orig_file_text[:ins_pos] + decl_blk + "\n\n" + orig_file_text[ins_pos:]
        return new_file, decl_blk, "splice-sketch"

    if target_decl is None:
        return submission_text, submission_text, "full-file-fallback"

    orig_decl_text = orig_file_text[target_decl["start_idx"]:target_decl["end_idx"]]
    orig_hdr, _ = C.split_theorem_header_and_proof(orig_decl_text)

    if mode == "splice-body":
        ext = C.extract_lemma_proof_from_submission(submission_text, full_name, short_name)
        if not ext or not ext.get("proof"):
            raise ValueError(f"could not extract proof body for {full_name}")
        new_decl = f"{orig_hdr} :=\n{ext['proof']}"
        new_file = orig_file_text[:target_decl["start_idx"]] + new_decl + orig_file_text[target_decl["end_idx"]:]
        return new_file, new_decl, "splice-body"

    if mode == "splice-decl":
        ext = C.extract_lemma_proof_from_submission(submission_text, full_name, short_name)
        if not ext:
            raise ValueError(f"could not extract declaration for {full_name}")
        new_decl = (ext.get("block_text") or ext["decl_text"]) if ext["kind"] == "decl" else f"{orig_hdr} :=\n{ext['proof']}"
        new_file = orig_file_text[:target_decl["start_idx"]] + new_decl + orig_file_text[target_decl["end_idx"]:]
        return new_file, new_decl, "splice-decl"

    # auto mode: if submission looks like a complete Lean file (starts with `import` or sets imports),
    # compile it directly as the module file (subverify only exports `task["lemma"]`, and merge.py
    # later extracts the lemma + any helper decls to splice cleanly without clobbering sibling lemmas).
    if re.search(r"^\s*import\s+", submission_text, re.M):
        return submission_text, submission_text, "full-file"

    ext = C.extract_lemma_proof_from_submission(submission_text, full_name, short_name)
    if ext:
        new_decl = (ext.get("block_text") or ext["decl_text"]) if ext["kind"] == "decl" else f"{orig_hdr} :=\n{ext['proof']}"
        new_file = orig_file_text[:target_decl["start_idx"]] + new_decl + orig_file_text[target_decl["end_idx"]:]
        return new_file, new_decl, "splice-" + ext["kind"]

    return submission_text, submission_text, "full-file-raw"


def compile_single_module_sandboxed(work_tree, rel_file, module_name, packages_ws, tc_prefix, timeout_s=60):
    """Compile ONE modified Lean module inside a network-less bwrap sandbox on top of work_tree's .oleans.
    rel_file must be a confined module path whose module IS module_name; every host-side file operation (the
    source check, the output directories, removing stale outputs, the result check) stays below work_tree without
    following a symlink. A refused path is a failed compile (rc 2), nothing outside work_tree is touched."""
    lean_bin = os.path.join(tc_prefix, "bin", "lean")
    try:
        if C.module_of_relpath(rel_file) != module_name:
            raise C.PathRefused(f"module {module_name!r} is not the module of {rel_file!r}")
        C.read_text_under(work_tree, rel_file)   # a regular file reached without a symlink
        mod_comps = module_name.split(".")
        # .lake/build/lib/lean if it exists (a real directory, never a symlink), else .lake/build/lib (made if missing)
        lib_dfd = C.open_dir_nofollow(work_tree, [".lake", "build", "lib"], create=True)
        try:
            try:
                st = os.stat("lean", dir_fd=lib_dfd, follow_symlinks=False)
                if not stat.S_ISDIR(st.st_mode):
                    raise C.PathRefused(".lake/build/lib/lean is not a real directory")
                lib_comps = [".lake", "build", "lib", "lean"]
            except FileNotFoundError:
                lib_comps = [".lake", "build", "lib"]
        finally:
            os.close(lib_dfd)
        out_dfd = C.open_dir_nofollow(work_tree, lib_comps + mod_comps[:-1], create=True)
        try:
            # Remove old olean so a failed compile can never leave a stale olean behind (entries of this directory only)
            for suf in (".olean", ".ilean", ".olean.private", ".olean.server"):
                try:
                    os.unlink(mod_comps[-1] + suf, dir_fd=out_dfd)
                except FileNotFoundError:
                    pass
        finally:
            os.close(out_dfd)
    except (C.PathRefused, OSError) as e:
        return False, 2, f"compile refused: {e}", 0.0
    lean_path = C.collect_lean_path(work_tree, packages_ws)
    src_abs = os.path.join(work_tree, rel_file)
    lib_root = os.path.join(work_tree, *lib_comps)
    olean_out = os.path.join(lib_root, *mod_comps[:-1], mod_comps[-1] + ".olean")
    ilean_out = os.path.join(lib_root, *mod_comps[:-1], mod_comps[-1] + ".ilean")
    argv = [
        lean_bin, "-o", olean_out, "-i", ilean_out,
        "--root=" + work_tree,
        src_abs,
    ]
    ro = [packages_ws, tc_prefix]
    rw = [work_tree]
    env_extra = {
        "PATH": f"{tc_prefix}/bin:/usr/bin:/bin",
        "LEAN_PATH": lean_path,
        "HOME": "/tmp",
        "TMPDIR": "/tmp",
    }
    rc, out, err, wall = C.run_bwrap(argv, ro_binds=ro, rw_binds=rw, env_extra=env_extra, cwd=work_tree, timeout=timeout_s)
    diag = (out + "\n" + err).strip()
    ok = False
    if rc == 0:
        try:   # the olean itself, not a symlink the sandboxed compile may have put there
            dfd = C.open_dir_nofollow(work_tree, lib_comps + mod_comps[:-1])
            try:
                st = os.stat(mod_comps[-1] + ".olean", dir_fd=dfd, follow_symlinks=False)
                ok = stat.S_ISREG(st.st_mode) and st.st_size > 0
            finally:
                os.close(dfd)
        except (C.PathRefused, OSError):
            ok = False
    return ok, rc, diag, wall


def verify_subproof(manifest, task, submission_text, agent_id="agent", mode="auto",
                    threads=4, timeout_build=60, timeout_check=120,
                    integrity_cache=None, fv_root=None, exporter="E1",
                    save_verified_dir=None, extra_file_patches=None):
    """Verify an untrusted submission for `task` against its SHA-256-pinned sub-challenge.
    Returns structured result dict.
    """
    t_total = time.monotonic()
    fv_root = os.path.realpath(fv_root or C.FASTVERIFY_ROOT)
    # an incomplete manifest / task is no verdict (exit 2), never a KeyError (exit 1)
    miss = [k for k in ("base_build_tree", "packages_workspace", "toolchain_prefix")
            if not isinstance(manifest.get(k), str) or not manifest.get(k)] if isinstance(manifest, dict) else ["manifest"]
    if not isinstance(task, dict):
        miss.append("task")
    else:
        miss += [k for k in ("subchallenge_export", "subchallenge_sha256", "comparator_json", "module")
                 if not isinstance(task.get(k), str) or not task.get(k)]   # (a missing comparator PIN: SUBCHALLENGE_UNPINNED below)
    if miss:
        return {"verdict": "NO_VERDICT", "category": "TASK_INCOMPLETE", "reason": "manifest / task lacks %s" % ", ".join(miss)}
    base_tree = manifest["base_build_tree"]
    packages_ws = manifest["packages_workspace"]
    tc_prefix = manifest["toolchain_prefix"]

    sub_exp_path = task["subchallenge_export"]
    sub_exp_pin = task["subchallenge_sha256"]
    sub_comp_path = task["comparator_json"]
    sub_comp_pin = task.get("comparator_sha256")

    # Always verify BOTH sub-challenge export AND comparator.json pins BEFORE judging!
    if not os.path.isfile(sub_exp_path):
        return {"verdict": "NO_VERDICT", "category": "MISSING_SUBCHALLENGE", "reason": "subchallenge.export missing"}
    actual_sha = C.sha256_file(sub_exp_path)
    if actual_sha != sub_exp_pin:
        return {"verdict": "NO_VERDICT", "category": "SUBCHALLENGE_TAMPERED", "reason": f"sha256 mismatch: {actual_sha} != {sub_exp_pin}"}
    if not sub_comp_pin:   # mint.py always records it; without it there is no verdict
        return {"verdict": "NO_VERDICT", "category": "SUBCHALLENGE_UNPINNED", "reason": "task has no comparator_sha256 pin"}
    if not os.path.isfile(sub_comp_path) or C.sha256_file(sub_comp_path) != sub_comp_pin:
        return {"verdict": "NO_VERDICT", "category": "SUBCHALLENGE_TAMPERED", "reason": "comparator.json sha256 mismatch"}

    rel_file = task.get("rel_file")
    mod_name = task["module"]
    if not rel_file:
        return {"verdict": "NO_VERDICT", "category": "NO_SOURCE_FILE", "reason": "task has no rel_file"}
    # the task's source path: a confined module file path whose module is the task's module
    try:
        if C.module_of_relpath(rel_file) != mod_name:
            raise C.PathRefused(f"module {mod_name!r} is not the module of {rel_file!r}")
    except C.PathRefused as e:
        return {"verdict": "NO_VERDICT", "category": "BAD_SOURCE_PATH", "reason": str(e)}

    with tempfile.TemporaryDirectory(prefix="fv-subver-") as td:
        work_tree = os.path.join(td, "proj")
        # Copy base build tree cleanly (reflink when on XFS, else fast copy)
        p_cp = subprocess.run(["cp", "-a", "--reflink=auto", base_tree, work_tree], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if p_cp.returncode != 0:
            shutil.copytree(base_tree, work_tree, symlinks=True)

        try:
            orig_text = C.read_text_under(work_tree, rel_file)
        except C.PathRefused as e:
            return {"verdict": "NO_VERDICT", "category": "BAD_SOURCE_PATH", "lemma": task["lemma"], "agent": agent_id,
                    "reason": str(e), "wall_s": round(time.monotonic() - t_total, 3)}
        try:
            new_text, spliced_decl, mode_used = apply_submission_to_file(orig_text, task, submission_text, mode=mode)
        except Exception as e:
            return {
                "verdict": "REJECTED",
                "category": "PARSE_SUBMISSION_ERROR",
                "lemma": task["lemma"],
                "agent": agent_id,
                "reason": str(e),
                "wall_s": round(time.monotonic() - t_total, 3),
            }

        C.write_text_under(work_tree, rel_file, new_text)

        # Optional extra file patches (e.g. for testing hostile shared-def edits)
        # confined like the task's own file: relative, no '..', no symlink followed, atomic replace
        extra_modules = []
        if extra_file_patches:
            for erel, econtent in extra_file_patches.items():
                try:
                    emod = C.module_of_relpath(erel) if isinstance(erel, str) and erel.endswith(".lean") else None
                    C.write_text_under(work_tree, erel, econtent)
                except (C.PathRefused, OSError) as e:
                    return {
                        "verdict": "REJECTED",
                        "category": "SCOPE_VIOLATION",
                        "lemma": task["lemma"],
                        "agent": agent_id,
                        "reason": f"path traversal outside project / refused path: {erel!r} ({e})",
                        "wall_s": round(time.monotonic() - t_total, 3),
                    }
                if emod is not None and erel != rel_file:
                    extra_modules.append((erel, emod))

        # Step 1: Compile extra modified modules first (if any), then target module
        build_s = 0.0
        for erel, emod in extra_modules:
            ok, rc, diag, w = compile_single_module_sandboxed(work_tree, erel, emod, packages_ws, tc_prefix, timeout_s=timeout_build)
            build_s += w
            if not ok:
                return {
                    "verdict": "REJECTED",
                    "category": "COMPILE_ERROR",
                    "lemma": task["lemma"],
                    "agent": agent_id,
                    "mode_used": mode_used,
                    "compiler_output": diag[-2000:],
                    "reason": f"dependency module {emod} failed to compile (rc={rc})",
                    "stage_s": {"build": round(build_s, 3)},
                    "wall_s": round(time.monotonic() - t_total, 3),
                }

        ok, rc, diag, w = compile_single_module_sandboxed(work_tree, rel_file, mod_name, packages_ws, tc_prefix, timeout_s=timeout_build)
        build_s += w
        if not ok:
            cat = "TIMEOUT" if rc == 124 else "COMPILE_ERROR"
            return {
                "verdict": "NO_VERDICT" if rc == 124 else "REJECTED",
                "category": cat,
                "lemma": task["lemma"],
                "agent": agent_id,
                "mode_used": mode_used,
                "compiler_output": diag[-2500:],
                "reason": f"module {mod_name} failed to compile (rc={rc})",
                "stage_s": {"build": round(build_s, 3)},
                "wall_s": round(time.monotonic() - t_total, 3),
            }

        # Step 2: Export L_i closure
        sol_export = os.path.join(td, "solution.export")
        sub_comp = json.load(open(sub_comp_path, encoding="utf-8"))
        targets = M.export_targets_for(sub_comp["theorem_names"], sub_comp["permitted_axioms"])
        try:
            exp_mode, exp_s = M.run_exporter(
                work_tree, mod_name, targets, sol_export, packages_ws, tc_prefix,
                fv_root, threads=min(threads, 16), prefer_official=(exporter == "E0"),
            )
        except Exception as e:
            return {
                "verdict": "REJECTED",
                "category": "EXPORT_ERROR",
                "lemma": task["lemma"],
                "agent": agent_id,
                "mode_used": mode_used,
                "compiler_output": diag[-1000:],
                "reason": f"export failed: {e}",
                "stage_s": {"build": round(build_s, 3)},
                "wall_s": round(time.monotonic() - t_total, 3),
            }

        # Step 3: Judge with UNCHANGED trusted sound check against pinned subchallenge.export!
        chk_script = (
            os.path.join(fv_root, "check", "sound", "check-sound-svc.sh")
            if integrity_cache
            else os.path.join(fv_root, "check", "sound", "check-sound.sh")
        )
        chk_json = os.path.join(td, "check.json")
        chk_log = os.path.join(td, "check.log")
        chk_cmd = [
            chk_script, sol_export, sub_exp_path, sub_comp_path,
            "--threads", str(threads),
            "--timeout", str(timeout_check),
            "--hints", "none",
            "--json", chk_json,
            "--log", chk_log,
            "--challenge-sha256", sub_exp_pin,   # the judge verifies the pins on its own private copies
        ]
        if sub_comp_pin:
            chk_cmd += ["--comparator-sha256", sub_comp_pin]
        if integrity_cache:
            chk_cmd += ["--integrity-cache", integrity_cache]
        t_chk = time.monotonic()
        p_chk = subprocess.run(chk_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        chk_s = round(time.monotonic() - t_chk, 3)

        chk_res = {}
        if os.path.isfile(chk_json):
            try:
                chk_res = json.load(open(chk_json, encoding="utf-8"))
            except Exception:
                pass
        chk_log_txt = open(chk_log, encoding="utf-8", errors="replace").read() if os.path.isfile(chk_log) else ""
        verdict = chk_res.get("verdict") or ("ACCEPTED" if p_chk.returncode == 0 else ("REJECTED" if p_chk.returncode == 1 else "NO_VERDICT"))
        reason = chk_res.get("reason", "")

        saved_path = None
        if p_chk.returncode == 0 and verdict == "ACCEPTED":
            final_verdict = "SUBPROOF_ACCEPTED"
            cat = "ACCEPTED"
            if save_verified_dir:
                os.makedirs(save_verified_dir, exist_ok=True)
                saved_path = os.path.join(save_verified_dir, f"{task['id']}.verified.json")
                C.atomic_write_json(saved_path, {
                    "schema": "fv-verified-subproof-v1",
                    "verified_at": C.now_iso(),
                    "lemma": task["lemma"],
                    "id": task["id"],
                    "sketch_subgoal": bool(task.get("sketch_subgoal")),
                    "in_declaration": task.get("in_declaration"),
                    "sorry_index": task.get("sorry_index"),
                    "source_sorry_index": task.get("source_sorry_index", task.get("sorry_index")),
                    "sketch_binders": task.get("sketch_binders") or [],
                    "agent": agent_id,
                    "rel_file": rel_file,
                    "module": mod_name,
                    "subchallenge_sha256": sub_exp_pin,
                    "mode_used": mode_used,
                    "spliced_decl": spliced_decl,
                    "full_module_text": new_text,
                    "proof_sha256": C.sha256_str(new_text),
                    "check_result": chk_res,
                })
        elif p_chk.returncode == 1 and verdict == "REJECTED":
            final_verdict = "REJECTED"
            cat = classify_rejection(reason, chk_log_txt)
        else:
            final_verdict = "NO_VERDICT"
            cat = "DECLINED"

        return {
            "verdict": final_verdict,
            "category": cat,
            "lemma": task["lemma"],
            "id": task["id"],
            "agent": agent_id,
            "mode_used": mode_used,
            "subchallenge_sha256": sub_exp_pin,
            "reason": reason,
            "compiler_output": diag[-1500:],
            "saved_subproof": saved_path,
            "stage_s": {
                "build": round(build_s, 3),
                "export": exp_s,
                "export_mode": exp_mode,
                "check": chk_s,
            },
            "wall_s": round(time.monotonic() - t_total, 3),
            "check_result": chk_res,
        }


def main():
    ap = argparse.ArgumentParser(description="Verify an untrusted agent proof submission against a minted sub-challenge.")
    ap.add_argument("manifest", help="Path to manifest.json from mint.py")
    ap.add_argument("lemma", help="Full Lean name of the frontier lemma")
    ap.add_argument("submission", help="Path to agent submission .lean file (or proof snippet)")
    ap.add_argument("--agent", default="agent")
    ap.add_argument("--mode", choices=["auto", "full-file", "splice-decl", "splice-body"], default="auto")
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--timeout-build", type=int, default=60)
    ap.add_argument("--timeout-check", type=int, default=120)
    ap.add_argument("--integrity-cache", default=None)
    ap.add_argument("--save-dir", default=None, help="Directory to save verified subproof JSON if ACCEPTED")
    ap.add_argument("--fv", default=None)
    ap.add_argument("--exporter", choices=["E1", "E0"], default="E1")
    ap.add_argument("--out", default=None, help="Write verdict JSON to file")
    ap.add_argument("--experimental", action="store_true", help="REQUIRED in v0.1: the subcontract engine (mint / subverify / "
                    "merge) ships EXPERIMENTAL; without this flag the command is refused (exit 2)")
    args = ap.parse_args()
    if not args.experimental:   # subcontract ships EXPERIMENTAL, opt-in only
        print(json.dumps({"ok": False, "verdict": "NO_VERDICT", "exit": 2,
                          "error": "subverify.py is EXPERIMENTAL in v0.1 (subcontract engine): pass --experimental to run it"}))
        sys.exit(2)
    C.install_interrupt_handler("subverify.py")   # a signal is no verdict: exit 2, children killed

    try:   # any failure before / outside a judged verdict is NO_VERDICT, exit 2
        manifest = json.load(open(args.manifest, encoding="utf-8"))
        sc = next((x for x in manifest.get("subchallenges", []) if isinstance(x, dict) and
                   (x.get("lemma") == args.lemma or x.get("id") == args.lemma)), None)
        if not sc:
            print(json.dumps({"verdict": "NO_VERDICT", "category": "UNKNOWN_LEMMA", "reason": f"lemma {args.lemma} not in manifest"}))
            sys.exit(2)
        task = json.load(open(sc["task_json"], encoding="utf-8"))
        sub_text = open(args.submission, encoding="utf-8").read()
        save_dir = args.save_dir or os.path.join(os.path.dirname(os.path.realpath(args.manifest)), "verified_subproofs")
        res = verify_subproof(
            manifest, task, sub_text, agent_id=args.agent, mode=args.mode,
            threads=args.threads, timeout_build=args.timeout_build, timeout_check=args.timeout_check,
            integrity_cache=args.integrity_cache, fv_root=args.fv, exporter=args.exporter,
            save_verified_dir=save_dir,
        )
    except Exception as e:   # noqa: BLE001
        res = {"verdict": "NO_VERDICT", "category": "INPUT_ERROR", "reason": "%s: %s" % (type(e).__name__, e)}
    if args.out:
        C.atomic_write_json(args.out, res)
    print(json.dumps(res, ensure_ascii=False))
    if res["verdict"] == "SUBPROOF_ACCEPTED":
        sys.exit(0)
    elif res["verdict"] == "REJECTED":
        sys.exit(1)
    else:
        sys.exit(2)


if __name__ == "__main__":
    main()

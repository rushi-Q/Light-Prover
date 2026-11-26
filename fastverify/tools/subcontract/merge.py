#!/usr/bin/python3 -I
"""merge.py — Safe Multi-Agent Proof Splicer & Parent Frontier Closure Engine.

Takes one or more verified sub-proofs (produced by subverify.py) for disjoint open frontier
lemmas {L_i1, ..., L_im}, splices them cleanly into the evolving parent repository (even when
multiple concurrent agents proved different lemmas in the SAME file!), rebuilds affected modules,
re-exports the parent closure, and re-verifies the parent repo against the ORIGINAL clean parent
challenge via `check/frontier/check-frontier.sh`.

Guarantees:
  - Enforces strict frontier monotonicity: no new sorries introduced (F_new ⊆ F_old \\ closed).
  - Updates `ledger.json` atomically with closed lemmas, remaining count, and audit history.
  - When F_new == ∅, `check-frontier.sh` automatically executes the unchanged `check/sound/check-sound.sh`
    with the original challenge config (NO sorryAx) and emits the final Day-100 ACCEPTED verdict (exit 0)!
"""
import argparse
import fcntl
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
import mint as M
import subverify as SV


def _rewrite_sketch_helper_decl(decl_blk, helper_name):
    """Rename the target theorem inside a verified sketch subgoal block to `private theorem <helper_name>`."""
    # Find the LAST theorem/lemma declaration (after any private helpers the agent wrote)
    decls = C.scan_lean_declarations(decl_blk)
    if decls:
        last = decls[-1]
        sub = decl_blk[last["start_idx"]:last["end_idx"]]
        sub2 = re.sub(
            rf"^((?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*)(?:theorem|lemma)\s+(?:_root_\.)?{C.LEAN_IDENT_RE_STR}",
            f"private theorem {helper_name}",
            sub, count=1,
        )
        return decl_blk[:last["start_idx"]] + sub2 + decl_blk[last["end_idx"]:]
    return re.sub(
        rf"\b(?:theorem|lemma)\s+(?:_root_\.)?{C.LEAN_IDENT_RE_STR}",
        f"private theorem {helper_name}",
        decl_blk, count=1,
    )


def _sketch_binder_arg_names(binders):
    """Extract explicit local variable names from trace_state binder list like
    `['(a b c : ℝ)', '(h1 : 2 * a * b ≤ a ^ 2 + b ^ 2)']` -> `['a', 'b', 'c', 'h1']`.
    Returns None if any binder is a synthetic inaccessible `_h<n>` placeholder.
    """
    names = []
    for b in binders or []:
        m = re.match(r"^\(([^:]+):", b.strip())
        if not m:
            return None
        for nm in m.group(1).strip().split():
            if re.match(r"^_h\d+$", nm):
                return None
            names.append(nm)
    return names


def splice_proofs_into_tree(work_tree, subproofs, ledger=None):
    """Apply a batch of verified subproofs into `work_tree`.
    Groups proofs by `rel_file` and splices bottom-to-top by byte offset so multiple concurrent
    lemmas in the same file never collide or shift each other's line offsets!
    Handles BOTH top-level sorried lemmas AND D06 inline proof-sketch subgoals (`sketch_subgoal=True`).
    """
    by_file = {}
    for sp in subproofs:
        # sp["rel_file"] here is the MANIFEST's path (merge_subproofs replaced it); it is confined again here:
        # a module file path below work_tree, read and written without following any symlink
        C.module_of_relpath(sp["rel_file"])
        by_file.setdefault(sp["rel_file"], []).append(sp)

    modified_files = []
    ledger_lemmas = (ledger or {}).get("lemmas") or {}
    for rel_file, sps in sorted(by_file.items()):
        text = C.read_text_under(work_tree, rel_file)

        sketch_sps = [sp for sp in sps if sp.get("sketch_subgoal")]
        normal_sps = [sp for sp in sps if not sp.get("sketch_subgoal")]

        # A. Apply normal top-level lemma splices first
        if len(normal_sps) == 1 and normal_sps[0].get("mode_used", "").startswith("full-file") and normal_sps[0].get("full_module_text") and not sketch_sps:
            sp = normal_sps[0]
            ext = C.extract_lemma_proof_from_submission(sp["full_module_text"], sp["lemma"])
            decls = C.scan_lean_declarations(text)
            target = next((d for d in decls if d["full_name"] == sp["lemma"]), None)
            spliced_decl = sp.get("spliced_decl") or ""
            if target is not None and spliced_decl and not re.search(r"^\s*import\s+", spliced_decl, re.M) and sp.get("mode_used", "").startswith("splice-"):
                text = text[:target["start_idx"]] + spliced_decl + text[target["end_idx"]:]
            elif ext and ext["kind"] == "decl" and target is not None:
                new_text = text[:target["start_idx"]] + ext["decl_text"] + text[target["end_idx"]:]
                sub_decls = C.scan_lean_declarations(sp["full_module_text"])
                orig_names = {d["full_name"] for d in decls}
                extra_decls = [d for d in sub_decls if d["full_name"] not in orig_names]
                if extra_decls:
                    helpers = "\n\n".join(sp["full_module_text"][d["start_idx"]:d["end_idx"]] for d in extra_decls)
                    new_text = text[:target["start_idx"]] + helpers + "\n\n" + ext["decl_text"] + text[target["end_idx"]:]
                text = new_text
            else:
                text = sp["full_module_text"]
        elif normal_sps:
            decls = C.scan_lean_declarations(text)
            orig_names = {d["full_name"] for d in decls}
            replacements = []
            for sp in normal_sps:
                target = next((d for d in decls if d["full_name"] == sp["lemma"]), None)
                if target is None:
                    raise RuntimeError(f"cannot locate {sp['lemma']} in {rel_file} during merge")
                spliced_decl = sp.get("spliced_decl") or ""
                if spliced_decl and not re.search(r"^\s*import\s+", spliced_decl, re.M) and sp.get("mode_used", "").startswith("splice-"):
                    replacements.append((target["start_idx"], target["end_idx"], spliced_decl))
                    continue
                src_blob = sp.get("full_module_text") or spliced_decl or ""
                ext = C.extract_lemma_proof_from_submission(src_blob, sp["lemma"])
                if not ext:
                    raise RuntimeError(f"cannot extract proof of {sp['lemma']} for multi-splice")
                orig_decl = text[target["start_idx"]:target["end_idx"]]
                orig_hdr, _ = C.split_theorem_header_and_proof(orig_decl)
                rep_text = (ext.get("block_text") or ext["decl_text"]) if ext["kind"] == "decl" else f"{orig_hdr} :=\n{ext['proof']}"
                sub_decls = C.scan_lean_declarations(src_blob)
                extra = [d for d in sub_decls if d["full_name"] not in orig_names]
                if extra:
                    helpers = "\n\n".join(src_blob[d["start_idx"]:d["end_idx"]] for d in extra)
                    rep_text = helpers + "\n\n" + rep_text
                replacements.append((target["start_idx"], target["end_idx"], rep_text))
            replacements.sort(key=lambda x: x[0], reverse=True)
            for s_idx, e_idx, rep in replacements:
                text = text[:s_idx] + rep + text[e_idx:]

        # B. Apply inline proof-sketch subgoal splices (grouped by enclosing `in_declaration`)
        if sketch_sps:
            by_decl = {}
            for sp in sketch_sps:
                by_decl.setdefault(sp.get("in_declaration") or "", []).append(sp)
            decls = C.scan_lean_declarations(text)
            decl_repls = []
            for in_decl, dsps in by_decl.items():
                anchor = next((d for d in decls if d["full_name"] == in_decl), None)
                if anchor is None and in_decl:
                    anchor = next((d for d in decls if d["short_name"] == in_decl.split(".")[-1]), None)
                if anchor is None:
                    raise RuntimeError(f"cannot locate enclosing declaration {in_decl!r} in {rel_file} for sketch merge")
                decl_text = text[anchor["start_idx"]:anchor["end_idx"]]
                spans = C.find_sorry_spans_in_decl(decl_text)
                # Account for earlier inline sorries in the same declaration already closed by prior merges!
                closed_indices = sorted(
                    int(v.get("source_sorry_index") or v["sorry_index"])
                    for v in ledger_lemmas.values()
                    if v.get("sketch_subgoal") and v.get("in_declaration") == in_decl
                    and v.get("status") == "closed" and (v.get("source_sorry_index") or v.get("sorry_index")) is not None
                )
                helper_blocks = []
                sorry_edits = []
                for sp in sorted(dsps, key=lambda x: int(x.get("source_sorry_index") or x.get("sorry_index") or 1)):
                    orig_k = int(sp.get("source_sorry_index") or sp.get("sorry_index") or 1)
                    closed_before = sum(1 for c in closed_indices if c < orig_k)
                    cur_slot = orig_k - closed_before  # 1-based index into current remaining sorries
                    if cur_slot < 1 or cur_slot > len(spans):
                        raise RuntimeError(f"sketch sorry_index {orig_k} (slot {cur_slot}) out of range ({len(spans)} remaining sorries in {in_decl})")
                    span = spans[cur_slot - 1]
                    hname = f"_fv_sketch_{orig_k}_{C.sha256_str(sp['lemma'])[:8]}"
                    src_blk = sp.get("spliced_decl") or sp.get("full_module_text") or ""
                    helper_blocks.append(_rewrite_sketch_helper_decl(src_blk, hname))
                    arg_names = _sketch_binder_arg_names(sp.get("sketch_binders"))
                    if arg_names:
                        args_str = " ".join(arg_names)
                        call = f"(first | exact {hname} {args_str} | apply {hname} <;> assumption)"
                    else:
                        call = f"apply {hname} <;> assumption"
                    rep = call if span["is_tactic_mode"] else f"(by {call})"
                    sorry_edits.append((span["start_idx"], span["end_idx"], rep))
                # Replace sorry spans bottom-to-top inside decl_text
                new_decl_text = decl_text
                for s_i, e_i, rep in sorted(sorry_edits, key=lambda x: x[0], reverse=True):
                    new_decl_text = new_decl_text[:s_i] + rep + new_decl_text[e_i:]
                combined_block = "\n\n".join(helper_blocks) + "\n\n" + new_decl_text
                decl_repls.append((anchor["start_idx"], anchor["end_idx"], combined_block))
            for s_idx, e_idx, rep in sorted(decl_repls, key=lambda x: x[0], reverse=True):
                text = text[:s_idx] + rep + text[e_idx:]

        C.write_text_under(work_tree, rel_file, text)
        modified_files.append((rel_file, C.module_of_relpath(rel_file)))
    return modified_files


def merge_subproofs(manifest_path, subproof_paths, threads=8, integrity_cache=None, fv_root=None, challenge_sha256=None,
                    exporter="E1", dry_run=False, comparator_sha256=None):
    out_dir = os.path.dirname(os.path.realpath(manifest_path))
    lock_path = os.path.join(out_dir, ".merge.lock")
    os.makedirs(out_dir, exist_ok=True)
    with open(lock_path, "a+", encoding="utf-8") as lock_f:
        fcntl.flock(lock_f.fileno(), fcntl.LOCK_EX)
        try:
            return _merge_subproofs_locked(
                manifest_path, subproof_paths, threads=threads,
                integrity_cache=integrity_cache, fv_root=fv_root,
                exporter=exporter, dry_run=dry_run, challenge_sha256=challenge_sha256,
                comparator_sha256=comparator_sha256,
            )
        finally:
            fcntl.flock(lock_f.fileno(), fcntl.LOCK_UN)


def _merge_subproofs_locked(manifest_path, subproof_paths, threads=8, integrity_cache=None, fv_root=None,
                            exporter="E1", dry_run=False, challenge_sha256=None, comparator_sha256=None):
    t_total = time.monotonic()
    fv_root = os.path.realpath(fv_root or C.FASTVERIFY_ROOT)
    manifest = json.load(open(manifest_path, encoding="utf-8"))
    # the parent pin must come from the caller: --challenge-sha256 (equal to the manifest's), or
    # a manifest written by a mint.py that required the caller's pin
    if challenge_sha256 is not None:
        if not re.fullmatch(r"[0-9a-f]{64}", challenge_sha256) or challenge_sha256 != manifest.get("challenge_sha256"):
            raise RuntimeError(f"--challenge-sha256 {challenge_sha256} != the manifest's parent challenge sha256 "
                               f"{manifest.get('challenge_sha256')}")
    elif manifest.get("challenge_sha256_pinned_by_caller") is not True:
        raise RuntimeError("the manifest's parent challenge sha256 was not pinned by the caller (old mint.py): pass "
                           "--challenge-sha256 HEX (GOAL S1(1))")
    # likewise the comparator.json pin: --comparator-sha256 (equal to the manifest's)
    # or a manifest written by a mint.py that required the caller's comparator pin
    if comparator_sha256 is not None:
        if not re.fullmatch(r"[0-9a-f]{64}", comparator_sha256) or comparator_sha256 != manifest.get("comparator_sha256"):
            raise RuntimeError(f"--comparator-sha256 {comparator_sha256} != the manifest's parent comparator sha256 "
                               f"{manifest.get('comparator_sha256')}")
    elif manifest.get("comparator_sha256_pinned_by_caller") is not True:
        raise RuntimeError("the manifest's parent comparator sha256 was not pinned by the caller (mint.py before the "
                           "comparator pin): pass --comparator-sha256 HEX")
    if not re.fullmatch(r"[0-9a-f]{64}", str(manifest.get("comparator_sha256") or "")):
        raise RuntimeError("the manifest records no comparator sha256")
    out_dir = os.path.dirname(os.path.realpath(manifest_path))
    ledger_path = os.path.join(out_dir, "ledger.json")
    ledger = json.load(open(ledger_path, encoding="utf-8"))

    subproofs = [json.load(open(p, encoding="utf-8")) for p in subproof_paths]
    if not subproofs:
        raise RuntimeError("no subproofs provided to merge")

    # Verify every subproof against the manifest BEFORE anything is written: its lemma is a manifest lemma
    # (once), its subchallenge_sha256 is that lemma's, and the source file is the MANIFEST's rel_file - a confined module
    # path; a subproof naming another path is refused, and the subproof's own path is never used.
    sc_by_lemma = {x["lemma"]: x for x in manifest["subchallenges"]}
    seen_lemmas = set()
    pinned = []
    for sp in subproofs:
        if not isinstance(sp, dict) or not isinstance(sp.get("lemma"), str):
            raise RuntimeError("a subproof is not a JSON object with a 'lemma' name")
        ln = sp["lemma"]
        if ln not in sc_by_lemma:
            raise RuntimeError(f"lemma {ln} is not in manifest")
        if ln in seen_lemmas:
            raise RuntimeError(f"two subproofs for lemma {ln}")
        seen_lemmas.add(ln)
        if sp.get("subchallenge_sha256") != sc_by_lemma[ln]["subchallenge_sha256"]:
            raise RuntimeError(f"subproof {ln} was checked against a different subchallenge sha256!")
        rel = sc_by_lemma[ln].get("rel_file")
        if not rel:
            raise RuntimeError(f"lemma {ln} has no source file in the manifest: nothing to splice")
        try:
            C.module_of_relpath(rel)
        except C.PathRefused as e:
            raise RuntimeError(f"the manifest's source path of {ln} is refused: {e}")
        if "rel_file" in sp and sp["rel_file"] != rel:
            raise RuntimeError(f"subproof {ln} names source file {sp['rel_file']!r}, the manifest {rel!r}: refused")
        pinned.append(dict(sp, rel_file=rel))
    subproofs = pinned

    base_tree = manifest["base_build_tree"]
    packages_ws = manifest["packages_workspace"]
    tc_prefix = manifest["toolchain_prefix"]
    chal_export = manifest["challenge_export"]
    chal_sha = manifest["challenge_sha256"]
    comp_cfg_path = manifest["comparator_config"]
    sol_module = manifest["solution_module"]

    if C.sha256_file(chal_export) != chal_sha:
        raise RuntimeError("parent challenge.export sha256 mismatch!")
    comp_cfg_pin = manifest.get("comparator_sha256")
    # the caller's comparator.json is read ONCE: these bytes are hashed against the pin and
    # parsed below (the judge, check-frontier.sh, re-verifies its own private copy against the same pin)
    with open(comp_cfg_path, "rb") as _f:
        comp_cfg_bytes = _f.read()
    if hashlib.sha256(comp_cfg_bytes).hexdigest() != comp_cfg_pin:   # always pinned
        raise RuntimeError("parent comparator.json sha256 mismatch!")

    # Work on a fresh candidate copy of the current evolving base_tree (atomic commit only on PASS!)
    cand_parent = os.path.join(out_dir, "merge_tmp")
    os.makedirs(cand_parent, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cand-", dir=cand_parent) as td:
        cand_tree = os.path.join(td, "proj")
        p_cp = subprocess.run(["cp", "-a", "--reflink=auto", base_tree, cand_tree], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if p_cp.returncode != 0:
            shutil.copytree(base_tree, cand_tree, symlinks=True)

        # 1. Splice verified proofs (into the private candidate copy only; manifest-pinned, confined paths)
        try:
            modified = splice_proofs_into_tree(cand_tree, subproofs, ledger=ledger)
        except C.PathRefused as e:
            raise RuntimeError(f"splice refused: {e}")

        # 2. Rebuild modified modules (and solution_module if different) in sandbox!
        # Use B0 official-build.sh incrementally on the candidate tree? Note official-build.sh ignores .lake;
        # we rebuild modified modules directly in topological order (or compile modified + solution_module, and
        # if export/check needs downstream importers rebuilt, rebuild all .lean modules via sandboxed lake build
        # with existing .lake preserved!).
        t_b = time.monotonic()
        compiled_ok = True
        build_diag = ""
        # First try optimistic single-module recompile of modified modules (proof edits leave public interfaces intact!)
        for rel_file, mod_name in modified:
            ok, rc, diag, _ = SV.compile_single_module_sandboxed(cand_tree, rel_file, mod_name, packages_ws, tc_prefix, timeout_s=120)
            if not ok:
                compiled_ok = False
                build_diag = f"failed compiling {mod_name}: {diag[-1500:]}"
                break
        if compiled_ok:
            # Also recompile solution_module if it is a .lean file and wasn't already compiled
            sol_rel = sol_module.replace(".", os.sep) + ".lean"
            if os.path.isfile(os.path.join(cand_tree, sol_rel)) and all(m != sol_module for _, m in modified):
                ok, rc, diag, _ = SV.compile_single_module_sandboxed(cand_tree, sol_rel, sol_module, packages_ws, tc_prefix, timeout_s=120)
                if not ok:
                    compiled_ok = False
                    build_diag = f"failed compiling solution module {sol_module}: {diag[-1500:]}"
        build_s = round(time.monotonic() - t_b, 3)

        if not compiled_ok:
            return {
                "ok": False,
                "verdict": "MERGE_BUILD_FAILED",
                "reason": build_diag,
                "attempted_lemmas": [sp["lemma"] for sp in subproofs],
                "wall_s": round(time.monotonic() - t_total, 3),
            }

        # 3. Export parent closure
        comp_cfg = json.loads(comp_cfg_bytes.decode("utf-8"))   # the pinned bytes, not a re-read of the caller path
        parent_targets = M.export_targets_for(
            comp_cfg["theorem_names"] + comp_cfg.get("definition_names", []),
            comp_cfg["permitted_axioms"],
        )
        cand_export = os.path.join(td, "parent.export")
        exp_mode, exp_s = M.run_exporter(
            cand_tree, sol_module, parent_targets, cand_export, packages_ws, tc_prefix,
            fv_root, threads=threads, prefer_official=(exporter == "E0"),
        )
        cand_exp_sha = C.sha256_file(cand_export)

        # 4. Verify parent repo via D06's check-frontier.sh against ORIGINAL parent challenge!
        cf_sh = os.path.join(fv_root, "check", "frontier", "check-frontier.sh")
        cf_json = os.path.join(td, "frontier.json")
        cf_cmd = [
            cf_sh, cand_export, chal_export, comp_cfg_path,
            "--threads", str(threads),
            "--json", cf_json,
            "--challenge-sha256", chal_sha,   # the judge verifies the pins on its own private copies
        ]
        if comp_cfg_pin:
            cf_cmd += ["--comparator-sha256", comp_cfg_pin]
        if integrity_cache:
            cf_cmd += ["--integrity-cache", integrity_cache]
        t_cf = time.monotonic()
        p_cf = subprocess.run(cf_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        cf_s = round(time.monotonic() - t_cf, 3)
        cf_res = json.load(open(cf_json, encoding="utf-8")) if os.path.isfile(cf_json) else {}
        verdict = cf_res.get("verdict", "DECLINED")
        # the parent receipt counts only with its own exit code (ACCEPTED 0 / REJECTED 1 / CONDITIONAL 3)
        if {"ACCEPTED": 0, "REJECTED": 1, "CONDITIONAL": 3}.get(verdict) != p_cf.returncode:
            cf_res = dict(cf_res, reason="check-frontier.sh exit %s does not match its verdict %r: no verdict" % (p_cf.returncode, verdict))
            verdict = "DECLINED"

        if verdict not in ("CONDITIONAL", "ACCEPTED"):
            return {
                "ok": False,
                "verdict": verdict,
                "reason": cf_res.get("reason", f"check-frontier rc={p_cf.returncode}"),
                "attempted_lemmas": [sp["lemma"] for sp in subproofs],
                "frontier_result": cf_res,
                "stage_s": {"build": build_s, "export": exp_s, "frontier_check": cf_s},
                "wall_s": round(time.monotonic() - t_total, 3),
            }

        # 5. Enforce strict frontier monotonicity (no new sorries, and merged lemmas are closed!)
        # Top-level lemmas are matched by name; D06 inline sketch subgoals (`_fv_sorry_k`) are renumbered
        # starting at 1 after partial closes, so match them by `(in_declaration, type_sha256)` + count!
        new_frontier_list = cf_res.get("frontier") or []
        merged_names = {sp["lemma"] for sp in subproofs}
        merged_sketch = [sp for sp in subproofs if sp.get("sketch_subgoal")]
        merged_normal = {sp["lemma"] for sp in subproofs if not sp.get("sketch_subgoal")}

        prev_normal = {k for k, v in ledger["lemmas"].items() if v["status"] in ("open", "triaged_bad") and not v.get("sketch_subgoal")}
        prev_sketch_entries = {k: v for k, v in ledger["lemmas"].items() if v["status"] in ("open", "triaged_bad") and v.get("sketch_subgoal")}

        new_normal = set()
        new_sketch_sigs = []  # multiset of (in_declaration, type_sha256)
        for e in new_frontier_list:
            if isinstance(e, dict) and e.get("in_declaration"):
                new_sketch_sigs.append((e["in_declaration"], e.get("type_sha256")))
            else:
                new_normal.add(e["name"] if isinstance(e, dict) else str(e))

        unexpected_new = sorted(new_normal - prev_normal)
        still_open = sorted(merged_normal & new_normal)

        # Check sketch monotonicity:
        #   - Untouched declarations: strict `(in_declaration, type_sha256)` multiset non-increase.
        #   - Declarations where inline sorries were merged: strict per-declaration count decrease
        #     (`new_cnt(D) <= prev_cnt(D) - merged_cnt(D)`), because closing an earlier `have` can
        #     replace a `sorry`-abstracted hypothesis with its `let`-bound proof term inside later
        #     open subgoals' types.
        from collections import Counter
        touched_sketch_decls = {
            ledger["lemmas"][sp["lemma"]].get("in_declaration")
            for sp in merged_sketch if sp["lemma"] in ledger["lemmas"]
        }
        prev_sk_by_decl = Counter(v.get("in_declaration") for v in prev_sketch_entries.values())
        merged_sk_by_decl = Counter(
            ledger["lemmas"][sp["lemma"]].get("in_declaration")
            for sp in merged_sketch if sp["lemma"] in ledger["lemmas"]
        )
        new_sk_by_decl = Counter(sig[0] for sig in new_sketch_sigs)

        prev_sk_cnt = Counter((v.get("in_declaration"), v.get("type_sha256")) for v in prev_sketch_entries.values())
        new_sk_cnt = Counter(new_sketch_sigs)

        for dname, ncnt in new_sk_by_decl.items():
            if dname in touched_sketch_decls:
                allowed = prev_sk_by_decl.get(dname, 0) - merged_sk_by_decl.get(dname, 0)
                if ncnt > allowed:
                    still_open.append(f"{dname}(remaining={ncnt}>allowed={allowed})")
        for sig, cnt in new_sk_cnt.items():
            if sig[0] in touched_sketch_decls:
                continue
            if prev_sk_cnt.get(sig, 0) == 0:
                unexpected_new.append(f"{sig[0]}:{(sig[1] or '')[:12]}")
            elif cnt > prev_sk_cnt.get(sig, 0):
                still_open.append(f"{sig[0]}:{(sig[1] or '')[:12]}")

        new_open = set(new_normal)
        # Reconstruct remaining logical names from ledger for sketch subgoals (preserving original `_fv_sorry_k` identity!)
        rem_sk_by_decl = Counter(new_sk_by_decl)
        for k, v in sorted(prev_sketch_entries.items()):
            if k in merged_names:
                continue
            dname = v.get("in_declaration")
            if rem_sk_by_decl[dname] > 0:
                new_open.add(k)
                rem_sk_by_decl[dname] -= 1

        if unexpected_new or still_open:
            return {
                "ok": False,
                "verdict": "MERGE_FRONTIER_REGRESSION",
                "reason": f"unexpected_new={unexpected_new}, still_open={still_open}",
                "unexpected_new": unexpected_new,
                "still_open": still_open,
                "wall_s": round(time.monotonic() - t_total, 3),
            }

        # 6. Commit updated build tree & source files + update ledger atomically!
        if not dry_run:
            # Replace base_tree atomically via sibling rename
            next_tree = base_tree + f".next.{os.getpid()}"
            old_tree = base_tree + f".old.{os.getpid()}"
            if os.path.exists(next_tree):
                shutil.rmtree(next_tree)
            shutil.move(cand_tree, next_tree)
            os.rename(base_tree, old_tree)
            os.rename(next_tree, base_tree)
            shutil.rmtree(old_tree, ignore_errors=True)
            shutil.copy2(cand_export, manifest["base_export"])

            # Update ledger
            closed_now = []
            for sp in subproofs:
                ln = sp["lemma"]
                entry = ledger["lemmas"].get(ln)
                if entry is not None:
                    entry["status"] = "closed"
                    entry["closed_by"] = sp.get("agent", "agent")
                    entry["closed_at"] = C.now_iso()
                    entry["proof_sha256"] = sp.get("proof_sha256")
                    closed_now.append(ln)
            # Also mark any lemmas that became transitively unneeded as closed_transitive
            for ln, entry in ledger["lemmas"].items():
                if entry["status"] in ("open", "triaged_bad") and ln not in new_open:
                    entry["status"] = "closed"
                    entry["closed_by"] = "transitive"
                    entry["closed_at"] = C.now_iso()

            ledger["updated_at"] = C.now_iso()
            ledger["parent_verdict"] = verdict
            ledger["remaining_count"] = len(new_open)
            ledger["closed_count"] = sum(1 for v in ledger["lemmas"].values() if v["status"] == "closed")
            ledger["history"].append({
                "event": "merge",
                "at": C.now_iso(),
                "merged": sorted(merged_names),
                "agents": sorted({sp.get("agent", "agent") for sp in subproofs}),
                "parent_verdict": verdict,
                "remaining_count": len(new_open),
                "export_sha256": cand_exp_sha,
                "wall_s": round(time.monotonic() - t_total, 3),
            })
            C.atomic_write_json(ledger_path, ledger)

        return {
            "ok": True,
            "parent_verdict": verdict,
            "day100_complete": (verdict == "ACCEPTED" and len(new_open) == 0),
            "merged_lemmas": sorted(merged_names),
            "remaining_count": len(new_open),
            "remaining_lemmas": sorted(new_open),
            "closed_count": ledger["closed_count"],
            "initial_frontier_size": ledger["initial_frontier_size"],
            "export_sha256": cand_exp_sha,
            "stage_s": {"build": build_s, "export": exp_s, "export_mode": exp_mode, "frontier_check": cf_s},
            "wall_s": round(time.monotonic() - t_total, 3),
        }


def main():
    ap = argparse.ArgumentParser(description="Splice verified sub-proofs into parent repo and advance frontier ledger.")
    ap.add_argument("manifest", help="Path to manifest.json")
    ap.add_argument("subproofs", nargs="+", help="One or more *.verified.json files from subverify.py")
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--integrity-cache", default=None)
    ap.add_argument("--fv", default=None)
    ap.add_argument("--exporter", choices=["E1", "E0"], default="E1")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--challenge-sha256", default=None, help="the caller's pin of the official parent challenge export "
                    "(required unless the manifest was written by a mint.py that required it)")
    ap.add_argument("--comparator-sha256", default=None, help="the caller's pin of the parent comparator.json (required "
                    "unless the manifest was written by a mint.py that required it)")
    ap.add_argument("--experimental", action="store_true", help="REQUIRED in v0.1: the subcontract engine (mint / subverify / "
                    "merge) ships EXPERIMENTAL; without this flag the command is refused (exit 2)")
    args = ap.parse_args()
    if not args.experimental:   # subcontract ships EXPERIMENTAL, opt-in only
        print(json.dumps({"ok": False, "verdict": "NO_VERDICT", "exit": 2,
                          "error": "merge.py is EXPERIMENTAL in v0.1 (subcontract engine): pass --experimental to run it"}))
        sys.exit(2)
    C.install_interrupt_handler("merge.py")   # a signal is no verdict: exit 2, children killed
    try:
        res = merge_subproofs(
            args.manifest, args.subproofs, threads=args.threads,
            integrity_cache=args.integrity_cache, fv_root=args.fv, challenge_sha256=args.challenge_sha256,
            exporter=args.exporter, dry_run=args.dry_run, comparator_sha256=args.comparator_sha256,
        )
        print(json.dumps(res, ensure_ascii=False))
        if res.get("ok"):
            sys.exit(0 if res.get("day100_complete") else 3)
        # exit 1 only for a JUDGED rejection (the parent check REJECTED the merged tree, the
        # merged tree does not build, or the frontier regressed); a declined / refused / missing check is no verdict: exit 2
        sys.exit(1 if res.get("verdict") in ("REJECTED", "MERGE_BUILD_FAILED", "MERGE_FRONTIER_REGRESSION") else 2)
    except Exception as e:
        print(json.dumps({"ok": False, "error": str(e)}))
        sys.exit(2)


if __name__ == "__main__":
    main()

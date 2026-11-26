#!/usr/bin/python3 -I
"""fv_schema.py — Stable API v1 normalization, validation, diagnostic parsing, LSP & SARIF 2.1.0 emitters,
and shared input-security validators for all fastverify production interfaces.

Zero external dependencies (Python 3.10+ stdlib only). Never alters any verdict or weakens soundness:
  * accepted is True IFF verdict == "ACCEPTED" AND trust is in the sound family ACCEPTING_TRUST
    (sound, sound-conditional, notary): an ACCEPTED of an UNSAFE / exact-by-design (unofficial) / official /
    conditional / none run is reported as such but NEVER counts (accepted=false, reward=0.0, exit_code=2, warning added)
  * reward is 1.0 IFF accepted, else strictly 0.0 (NO-VERDICT/ERROR/CONDITIONAL -> 0.0)
"""
import hashlib
import json
import os
import re
import time

API_VERSION = "1.0"

VALID_MODES = frozenset({
    "project", "project_incremental", "attempt", "batch_attempt",
    "export_in", "frontier", "audit", "doctor",
})
VALID_VERDICTS = frozenset({
    "ACCEPTED", "REJECTED", "CONDITIONAL", "ACCEPTED_MODULO_FRONTIER",
    "DECLINED", "NO-VERDICT", "ERROR", "PENDING",
})
VALID_TRUST = frozenset({
    "sound", "sound-conditional", "notary", "official", "exact-by-design (unofficial)",
    "conditional", "UNSAFE", "none",
})
# the only trust labels under which an ACCEPTED verdict counts (accepted=true, reward=1.0, exit 0). sound-conditional:
# an ACCEPTED from the conditional machinery means an EMPTY frontier = the plain sound check (CONDITIONAL itself never counts).
# Not here: UNSAFE, exact-by-design (unofficial), official (the unmodified lake comparator trusts comparator.json's
# permitted_axioms: no GOAL S1(3)), conditional, none.
ACCEPTING_TRUST = frozenset({"sound", "sound-conditional", "notary"})


def counts_as_accepted(verdict, trust):
    """the single acceptance predicate of every envelope (bin/fv, MCP, fvapi, CI, fv watch)"""
    return verdict == "ACCEPTED" and trust in ACCEPTING_TRUST
VALID_SEVERITIES = frozenset({"error", "warning", "info", "hint"})

THEOREM_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
SIMPLE_THEOREM_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")

# Matches Lean 4 compiler diagnostics (incl. Lean 4.33+ named codes):
#   path/to/File.lean:12:4: error: message
#   path/to/File.lean:8:48: error(lean.unknownIdentifier): Unknown identifier `m`
LEAN_DIAG_RE = re.compile(
    r"^(?P<file>[^\s:\n][^:\n]*?):(?P<line>\d+):(?P<col>\d+):\s*(?P<sev>error|warning|info|information)(?:\((?P<lcode>[^)]+)\))?:\s*(?P<msg>.*)$"
)

SARIF_RULES = {
    "FV001": {
        "id": "FV001",
        "name": "LeanBuildError",
        "shortDescription": {"text": "Lean elaboration or build diagnostic"},
        "defaultConfiguration": {"level": "error"},
    },
    "FV002": {
        "id": "FV002",
        "name": "StatementDrift",
        "shortDescription": {"text": "Solution statement or definition differs from pinned official challenge"},
        "defaultConfiguration": {"level": "error"},
    },
    "FV003": {
        "id": "FV003",
        "name": "IllegalAxiom",
        "shortDescription": {"text": "Disallowed axiom (e.g., sorryAx, native_decide, custom axiom) in proof closure"},
        "defaultConfiguration": {"level": "error"},
    },
    "FV004": {
        "id": "FV004",
        "name": "KernelRejection",
        "shortDescription": {"text": "Trusted official Lean kernel or required second kernel rejected a declaration"},
        "defaultConfiguration": {"level": "error"},
    },
    "FV005": {
        "id": "FV005",
        "name": "SorryFrontier",
        "shortDescription": {"text": "Conditional proof depends on explicit sorry frontier lemmas"},
        "defaultConfiguration": {"level": "warning"},
    },
    "FV006": {
        "id": "FV006",
        "name": "VerificationNoVerdict",
        "shortDescription": {"text": "Verifier declined or encountered an error (fail-closed, not accepted)"},
        "defaultConfiguration": {"level": "warning"},
    },
    "FV007": {
        "id": "FV007",
        "name": "StatementAuditFinding",
        "shortDescription": {"text": "Statement fidelity or challenge configuration lint finding"},
        "defaultConfiguration": {"level": "warning"},
    },
}


# --------------------------------------------------------------------------- security & input helpers
def validate_sha256(h):
    return isinstance(h, str) and bool(SHA256_RE.fullmatch(h))   # fullmatch: `$` also matched before a final "\n"


def validate_theorem_name(name, allow_dotted=True):
    if not isinstance(name, str) or not name or len(name) > 512:
        return False
    if "\x00" in name or ".." in name or "/" in name or "\\" in name:
        return False
    rx = THEOREM_NAME_RE if allow_dotted else SIMPLE_THEOREM_RE
    return bool(rx.fullmatch(name))   # fullmatch: with match, `$` accepted a trailing line feed


def sanitize_single_line(s, max_len=400):
    if not isinstance(s, str):
        s = str(s)
    # Strip ASCII control chars / ANSI escape sequences to block terminal & log injection
    s = re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", s)
    s = "".join(ch if (32 <= ord(ch) < 127 or ord(ch) >= 160) else " " for ch in s)
    return " ".join(s.split())[:max_len]


def safe_resolve_under_roots(path, allowed_roots, must_exist=True, expect_dir=None):
    """Resolve path with realpath and enforce containment inside at least one allowed root.
    Rejects NUL bytes, path traversal escaping allowed_roots, and symlinks pointing outside allowed_roots.
    Returns (resolved_path, None) on success or (None, error_message) on failure."""
    if not isinstance(path, str) or not path or "\x00" in path:
        return None, "invalid path"
    if len(path) > 4096:
        return None, "path too long"
    try:
        real = os.path.realpath(path)
    except OSError as e:
        return None, f"cannot resolve path: {e}"
    if allowed_roots:
        ok = False
        for root in allowed_roots:
            rr = os.path.realpath(root)
            if real == rr or real.startswith(rr + os.sep):
                ok = True
                break
        if not ok:
            return None, "path is outside allowed workspace roots"
    if must_exist and not os.path.exists(real):
        return None, "path does not exist"
    if expect_dir is True and os.path.exists(real) and not os.path.isdir(real):
        return None, "expected a directory"
    if expect_dir is False and os.path.exists(real) and not os.path.isfile(real):
        return None, "expected a regular file"
    return real, None


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# --------------------------------------------------------------------------- diagnostic parsing
def parse_lean_diagnostics(text, default_file=None, strip_prefix=None, max_diags=200):
    """Parse Lean 4 stdout/stderr compiler output into structured diagnostic dicts."""
    if not text:
        return []
    diags = []
    cur = None
    for raw_line in text.splitlines():
        m = LEAN_DIAG_RE.match(raw_line)
        if m:
            if cur is not None:
                diags.append(cur)
                if len(diags) >= max_diags:
                    cur = None
                    break
            fpath = m.group("file").strip()
            if strip_prefix and fpath.startswith(strip_prefix):
                fpath = os.path.relpath(fpath, strip_prefix)
            sev = m.group("sev")
            if sev == "information":
                sev = "info"
            lcode = m.group("lcode")
            msg = m.group("msg").rstrip()
            if lcode:
                msg = f"[{lcode}] {msg}"
            cur = {
                "rule_id": "FV001",
                "severity": sev,
                "file": fpath or default_file,
                "line": max(1, int(m.group("line"))),
                # Lean's FILE:LINE:COL column is 0-based (Lean.Position.column); the schema's column is
                # 1-based (minimum 1; LSP = column - 1, SARIF startColumn = column): +1, as tools/fvwork prints it
                "column": max(0, int(m.group("col"))) + 1,
                "end_line": None,
                "end_column": None,
                "message": msg,
                "source": "lean",
            }
        elif cur is not None:
            # Continuation line of multi-line Lean diagnostic
            if len(cur["message"]) < 4000:
                cur["message"] += "\n" + raw_line.rstrip()
    if cur is not None and len(diags) < max_diags:
        diags.append(cur)
    return diags


def classify_verdict_diagnostic(verdict, reason, basis="", default_file=None):
    """Produce a structured diagnostic summarizing a non-ACCEPT comparator/kernel/service outcome."""
    text = f"{reason or ''} {basis or ''}".strip()
    if verdict == "ACCEPTED":
        return []
    if verdict in ("CONDITIONAL", "ACCEPTED_MODULO_FRONTIER"):
        return [{
            "rule_id": "FV005",
            "severity": "warning",
            "file": default_file,
            "line": 1 if default_file else None,
            "column": 1 if default_file else None,
            "end_line": None,
            "end_column": None,
            "message": sanitize_single_line(reason or basis or "Accepted modulo explicit sorry frontier", 800),
            "source": "fastverify",
        }]
    if verdict in ("DECLINED", "NO-VERDICT", "ERROR", "PENDING"):
        return [{
            "rule_id": "FV006",
            "severity": "warning",
            "file": default_file,
            "line": 1 if default_file else None,
            "column": 1 if default_file else None,
            "end_line": None,
            "end_column": None,
            "message": sanitize_single_line(reason or basis or f"Verification {verdict} (fail-closed)", 800),
            "source": "fastverify",
        }]
    # REJECTED: classify cause for actionable UX & CI alerts
    low = text.lower()
    if "challenge definition is not sorried" in low or "cross-version gate" in low or "release comparator rule" in low:
        rule = "FV007"   # a rule of the challenge release's comparator (a challenge property), not a build
    elif any(k in low for k in ("illegal axiom", "sorryax", "not permitted", "lean.ofreducebool", "lean.ofreducenat", "lean.trustcompiler", "_native.native_decide.ax_", "_native.decide.ax_")):
        rule = "FV003"
    elif any(k in low for k in ("do not match", "not match", "const not found", "not a theorem", "not a definition", "statement", "compareat")):
        rule = "FV002"
    elif any(k in low for k in ("kernel", "lean default exited", "gruszka", "nanoda", "while replaying")):
        rule = "FV004"
    else:
        rule = "FV001"
    return [{
        "rule_id": rule,
        "severity": "error",
        "file": default_file,
        "line": 1 if default_file else None,
        "column": 1 if default_file else None,
        "end_line": None,
        "end_column": None,
        "message": sanitize_single_line(reason or basis or "Verification rejected", 800),
        "source": "fastverify",
    }]


def acceptance_exit_code(verdict, trust):
    """exit 0 only for an acceptance that counts; ACCEPTED under any other trust -> 2 (no sound verdict)"""
    if verdict == "ACCEPTED" and not counts_as_accepted(verdict, trust):
        return 2
    return verdict_exit_code(verdict)


def verdict_exit_code(verdict):
    if verdict == "ACCEPTED":
        return 0
    if verdict == "REJECTED":
        return 1
    if verdict in ("CONDITIONAL", "ACCEPTED_MODULO_FRONTIER"):
        return 3
    return 2


def make_envelope(
    mode,
    verdict,
    trust,
    verdict_basis,
    total_s,
    reason="",
    target=None,
    timing_extra=None,
    diagnostics=None,
    compiler_output=None,
    soundness=None,
    frontier=None,
    statement_audit=None,
    warnings=None,
    raw=None,
):
    if verdict == "ACCEPTED_MODULO_FRONTIER":
        verdict = "CONDITIONAL"
    if verdict not in VALID_VERDICTS:
        verdict = "ERROR"
    if trust not in VALID_TRUST:
        trust = "none"
    accepted = counts_as_accepted(verdict, trust)   # never for UNSAFE / unofficial / official trust
    reward = 1.0 if accepted else 0.0
    warnings = list(warnings or [])
    if verdict == "ACCEPTED" and not accepted:
        warnings.append(f"verdict ACCEPTED with trust {trust!r} is not a sound acceptance: accepted=false, reward=0.0, "
                        f"exit_code=2 (only {sorted(ACCEPTING_TRUST)} count)")
    timing = {"total_s": round(max(0.0, float(total_s or 0.0)), 4)}
    if timing_extra:
        for k, v in timing_extra.items():
            if v is not None:
                timing[k] = round(float(v), 4) if isinstance(v, (int, float)) else v
    env = {
        "api_version": API_VERSION,
        "mode": mode if mode in VALID_MODES else "project",
        "verdict": verdict,
        "accepted": accepted,
        "reward": reward,
        "exit_code": acceptance_exit_code(verdict, trust),
        "trust": trust,
        "verdict_basis": str(verdict_basis or ""),
        "reason": str(reason or ""),
        "target": target or {},
        "timing": timing,
        "diagnostics": list(diagnostics or []),
        "compiler_output": compiler_output,
        "soundness": soundness,
        "frontier": frontier,
        "statement_audit": statement_audit,
        "warnings": warnings,
        "raw": raw,
    }
    return env


def normalize_acceptance(env):
    """recompute accepted / reward / exit_code of an envelope (e.g. one read back from a file) from verdict + trust"""
    if not isinstance(env, dict):
        return env
    v, t = env.get("verdict"), env.get("trust")
    if t not in VALID_TRUST:
        env["trust"] = t = "none"
    acc = counts_as_accepted(v, t)
    if v == "ACCEPTED" and not acc and env.get("accepted"):
        env.setdefault("warnings", [])
        if isinstance(env["warnings"], list):
            env["warnings"].append(f"verdict ACCEPTED with trust {t!r} is not a sound acceptance (normalized)")
    env["accepted"] = acc
    env["reward"] = 1.0 if acc else 0.0
    env["exit_code"] = acceptance_exit_code(v, t)
    return env


# --------------------------------------------------------------------------- backend normalizers
def from_fastverify_result(res, total_s=None, project_dir=None, include_raw=True):
    """Normalize bin/fastverify OUT/result.json into API v1 envelope."""
    if not isinstance(res, dict):
        return from_error("project", "missing or malformed result.json", total_s or 0.0)
    verdict = res.get("verdict") or "ERROR"
    if not isinstance(verdict, str):   # a malformed verdict is an error, never a TypeError
        return from_error("project", f"malformed result.json verdict {verdict!r}", total_s or 0.0)
    # a verdict never counts from an interrupted run or one whose recorded process exit disagrees with it
    # (bin/fastverify writes the decided verdict as PENDING until its end-of-run integrity check and final save are done);
    # the recorded exit must be a JSON integer (true is not 1)
    want_exit = {"ACCEPTED": 0, "REJECTED": 1, "CONDITIONAL": 3}.get(verdict)
    # a MISSING exit is not final either: only an integer exit consistent with the decision counts
    if want_exit is not None and (res.get("interrupted") or type(res.get("exit")) is not int
                                  or res.get("exit") != want_exit):
        return from_error("project", f"result.json verdict {verdict} is not final (interrupted={res.get('interrupted')!r}, "
                          f"exit={res.get('exit')!r}, expected {want_exit}): no verdict", total_s or 0.0)
    # the trust label comes from what RAN, never from the preset's name (an --extra-arg / --check override keeps
    # mode.preset = 'sound' while the sound check did not decide): sound labels need mode.sound true, notary needs CN
    mode_d = res.get("mode") if isinstance(res.get("mode"), dict) else {}
    ran_sound = mode_d.get("sound") is True
    ran_checks = mode_d.get("check") if isinstance(mode_d.get("check"), list) else []
    trust = res.get("trust")
    if trust is None:
        trust = "sound" if ran_sound else ("notary" if "CN" in ran_checks else "none")
    if trust not in VALID_TRUST:
        trust = "none"
    if trust in ("sound", "sound-conditional") and not ran_sound:
        trust = "none"
    if trust == "notary" and "CN" not in ran_checks:
        trust = "none"
    basis = res.get("verdict_basis") or ""
    ss = res.get("stage_seconds") or {}
    if total_s is None:
        total_s = sum(v for v in ss.values() if isinstance(v, (int, float)))
    inp = res.get("inputs") or {}
    chx = inp.get("challenge_export") or {}
    exp = res.get("export") or {}
    snd_check = ((res.get("checks") or {}).get("sound") or {}).get("stage") or {}
    reason = snd_check.get("reason") or basis
    diags = []
    # Wire sound-auto build.failed_modules structured Lean errors (if present)
    failed_mods = (res.get("build") or {}).get("failed_modules") or []
    if isinstance(failed_mods, list):
        for fm in failed_mods:
            if not isinstance(fm, dict):
                continue
            err_s = fm.get("error") or ""
            parsed = parse_lean_diagnostics(err_s, default_file=fm.get("module")) if err_s else []
            if parsed:
                diags.extend(parsed)
            else:
                diags.append({
                    "rule_id": "FV001",
                    "severity": "error",
                    "file": fm.get("module"),
                    "line": 1,
                    "column": 1,
                    "end_line": None,
                    "end_column": None,
                    "message": sanitize_single_line(err_s or f"module build failed (rc={fm.get('rc')})", 600),
                    "source": "lean",
                })
    if not diags:
        diags = classify_verdict_diagnostic(verdict, reason, basis)
    mode = "export_in" if (res.get("mode") or {}).get("export_given") else "project"
    fr = res.get("frontier")
    if isinstance(fr, dict):
        fr = dict(fr)
        if "remaining" not in fr and isinstance(fr.get("frontier"), list):
            fr["remaining"] = [e.get("name") for e in fr["frontier"] if isinstance(e, dict) and e.get("name")]
    if verdict in ("CONDITIONAL", "ACCEPTED_MODULO_FRONTIER") or fr:
        mode = "frontier"
    return make_envelope(
        mode=mode,
        verdict=verdict,
        trust=trust,
        verdict_basis=basis,
        total_s=total_s,
        reason=reason,
        target={
            "project": project_dir or inp.get("project"),
            "challenge": inp.get("challenge"),
            "challenge_sha256": chx.get("sha256"),
            "export_path": exp.get("path"),
            "export_sha256": exp.get("sha256"),
        },
        timing_extra={
            "preflight_s": ss.get("preflight"),
            "prepare_s": ss.get("prepare"),
            "build_s": ss.get("build"),
            "export_s": ss.get("export"),
            "check_s": ss.get("checks_total") or ss.get("check_sound"),
        },
        diagnostics=diags,
        soundness=res.get("soundness"),
        frontier=fr,
        statement_audit=res.get("statement_audit"),
        warnings=res.get("warnings") or [],
        raw=res if include_raw else None,
    )


def from_fvserve_result(res, pset=None, theorem=None, source_file=None, overhead_ms=None, include_raw=True):
    """Normalize tools/fvserve JSON answer into API v1 envelope."""
    if not isinstance(res, dict) or "error" in res and "verdict" not in res:
        msg = res.get("error", "invalid fvserve response") if isinstance(res, dict) else "invalid fvserve response"
        return from_error("attempt", msg, 0.0, target={"pset": pset, "theorem": theorem})
    verdict = res.get("verdict") or "NO-VERDICT"
    why = res.get("why") or ""
    comp = res.get("compiler_output") or ""
    diags = parse_lean_diagnostics(comp, default_file=source_file)
    if source_file:   # fvserve compiles the attempt as its private PROJ/Attempt/<theorem>.lean
        att = "Attempt/" + str(res.get("theorem") or theorem or "").replace(".", "/") + ".lean"
        for d in diags:
            f = d.get("file") or ""
            if f == att or f.endswith("/" + att):
                d["file"] = source_file
    if verdict != "ACCEPTED" and not diags:
        diags = classify_verdict_diagnostic(verdict, why, default_file=source_file)
    elif verdict != "ACCEPTED" and why and not any(d["severity"] == "error" for d in diags):
        diags.extend(classify_verdict_diagnostic(verdict, why, default_file=source_file))
    exports = res.get("exports") or []
    checks = res.get("checks") or []
    exp_s = sum(e.get("s") or 0 for e in exports) if exports else None
    chk_s = sum(c.get("s") or 0 for c in checks) if checks else None
    pins_lbl = res.get("check_pins") or res.get("toolchain")
    kern_lbl = f"official Lean kernel ({pins_lbl})" if pins_lbl else "official Lean kernel (pinned check-sound judge)"
    basis = (
        f"SOUND (fvserve): official judge code (ccmp compareAt+checkAxioms) + {kern_lbl} "
        "(pleanchecker) + required second kernel (gruszka) on pinned official challenge export"
        if verdict == "ACCEPTED"
        else f"fvserve {verdict}: {why}"
    )
    return make_envelope(
        mode="attempt",
        verdict=verdict,
        trust="sound",
        verdict_basis=basis,
        total_s=res.get("total_s") or 0.0,
        reason=why,
        target={"pset": res.get("pset") or pset, "theorem": res.get("theorem") or theorem},
        timing_extra={
            "queue_s": res.get("queue_s"),
            "build_s": res.get("build_s"),
            "export_s": exp_s,
            "check_s": chk_s,
            "overhead_ms": overhead_ms,
        },
        diagnostics=diags,
        compiler_output=comp,
        raw=res if include_raw else None,
    )


def from_check_sound_result(res, export_path=None, challenge_sha256=None, total_s=None, include_raw=True):
    """Normalize check/sound/check-sound.sh JSON output into API v1 envelope."""
    if not isinstance(res, dict):
        return from_error("export_in", "missing or malformed check-sound JSON", total_s or 0.0)
    verdict = res.get("verdict") or "DECLINED"
    reason = res.get("reason") or ""
    basis = res.get("basis") or ""
    wall = total_s if total_s is not None else (res.get("wall_s") or 0.0)
    diags = classify_verdict_diagnostic(verdict, reason, basis)
    is_notary = (res.get("checker") == "checkNotary") or (res.get("trust") == "notary") or ("r7_digest" in res)
    soundness = {
        "version": res.get("version"),
        "wiring": res.get("wiring"),
        "binaries_sha256": res.get("binaries_sha256"),
        "leg_ms": res.get("leg_ms"),
    }
    for extra_k in ("pins", "pins_sha256", "toolchain", "r7_digest", "r7"):
        if res.get(extra_k) is not None:
            soundness[extra_k] = res.get(extra_k)
    return make_envelope(
        mode="export_in",
        verdict=verdict,
        trust="notary" if is_notary else "sound",
        verdict_basis=basis or f"{'checkNotary' if is_notary else 'checkSound'} {verdict}: {reason}",
        total_s=wall,
        reason=reason,
        target={"export_path": export_path, "challenge_sha256": challenge_sha256},
        timing_extra={"check_s": res.get("wall_s")},
        diagnostics=diags,
        soundness=soundness,
        raw=res if include_raw else None,
    )


def from_check_frontier_result(res, export_path=None, challenge_sha256=None, total_s=None, include_raw=True):
    """Normalize check/frontier/check-frontier.sh JSON output into API v1 envelope.
    Note: verdict CONDITIONAL always sets accepted=False and reward=0.0 (exit_code=3)."""
    if not isinstance(res, dict):
        return from_error("frontier", "missing or malformed check-frontier JSON", total_s or 0.0)
    verdict = res.get("verdict") or "DECLINED"
    reason = res.get("reason") or ""
    basis = res.get("basis") or ""
    wall = total_s if total_s is not None else (res.get("wall_s") or 0.0)
    if verdict == "ACCEPTED":
        trust = "sound"
    elif verdict == "CONDITIONAL":
        trust = "sound-conditional"
    elif verdict in ("DECLINED", "NO-VERDICT", "ERROR", "PENDING"):
        trust = "none"
    else:
        trust = "sound"
    diags = classify_verdict_diagnostic(verdict, reason, basis)
    fr_list = res.get("frontier") or []
    judge = res.get("judge") or {}
    frontier_block = {
        "frontier_size": res.get("frontier_size", len(fr_list)),
        "remaining": [e.get("name") for e in fr_list if isinstance(e, dict) and e.get("name")],
        "frontier": fr_list,
        "frontier_challenge_sha256": res.get("frontier_challenge_sha256"),
        "frontier_closed": res.get("frontier_closed"),
        "base_status": res.get("base_status"),
        "rewrite": res.get("rewrite"),
        "preparer": res.get("preparer"),
        "prepare_seconds": res.get("prepare_seconds"),
        "blockers": res.get("blockers"),
        "outside_pinned_frontier": res.get("outside_pinned_frontier"),
        "sorry_present": judge.get("sorry_present"),
        "not_allowed": judge.get("not_allowed"),
        "allowed_not_needed": judge.get("allowed_not_needed"),
        "diagnostic": judge.get("diagnostic"),
        "claim": res.get("claim"),
        "frontier_judge_sha256": res.get("frontier_judge_sha256"),
    }
    snd = res.get("checks") or res.get("sound_check")
    if isinstance(snd, dict) and (res.get("pins") is not None or res.get("pins_sha256") is not None):
        snd = dict(snd)
        if res.get("pins") is not None:
            snd["pins"] = res.get("pins")
        if res.get("pins_sha256") is not None:
            snd["pins_sha256"] = res.get("pins_sha256")
    return make_envelope(
        mode="frontier",
        verdict=verdict,
        trust=trust,
        verdict_basis=basis or f"checkFrontier {verdict}: {reason}",
        total_s=wall,
        reason=reason,
        target={"export_path": export_path, "challenge_sha256": challenge_sha256},
        timing_extra={"check_s": res.get("wall_s")},
        diagnostics=diags,
        soundness=snd,
        frontier=frontier_block,
        raw=res if include_raw else None,
    )


def from_incr_summary(res, project_dir=None, challenge_dir=None, challenge_sha256=None, total_s=None, include_raw=True):
    """Normalize tools/incr/incr-reverify.sh OUT/summary.json into API v1 envelope."""
    if not isinstance(res, dict):
        return from_error("project_incremental", "missing or malformed incr summary.json", total_s or 0.0)
    verdict = res.get("verdict") or "ERROR"
    attempts = res.get("attempts") or []
    last = attempts[-1] if attempts else {}
    last_chk = last.get("check") if isinstance(last.get("check"), dict) else {}
    reason = last_chk.get("reason") or last.get("reason") or res.get("reason") or ""
    wall = total_s if total_s is not None else (res.get("total_s") or sum(a.get("total_s") or 0 for a in attempts))
    diags = classify_verdict_diagnostic(verdict, reason)
    dirty_n = last.get("dirty") if last.get("dirty") is not None else last.get("dirty_modules")
    basis = (
        f"SOUND (incremental): verified by trusted check CS ({len(attempts)} attempt(s), "
        f"dirty_modules={dirty_n})"
        if verdict == "ACCEPTED"
        else f"SOUND (incremental) {verdict}: {reason}"
    )
    return make_envelope(
        mode="project_incremental",
        verdict=verdict,
        trust="sound",
        verdict_basis=basis,
        total_s=wall,
        reason=reason,
        target={
            "project": project_dir,
            "challenge": challenge_dir,
            "challenge_sha256": challenge_sha256,
        },
        timing_extra={
            "build_s": last.get("build_s"),
            "export_s": last.get("export_s"),
            "check_s": last.get("check_s"),
        },
        diagnostics=diags,
        raw=res if include_raw else None,
    )


def from_fvwork_result(res, project_dir=None, total_s=None, include_raw=True):
    """Normalize tools/fvwork (persistent repo daemon) JSON answer into API v1 envelope."""
    if not isinstance(res, dict) or ("error" in res and "verdict" not in res):
        msg = res.get("error", "invalid fvwork response") if isinstance(res, dict) else "invalid fvwork response"
        return from_error("project_incremental", msg, total_s or 0.0)
    verdict = res.get("verdict") or "NO-VERDICT"
    if verdict == "CONDITIONAL":
        trust = "sound-conditional"
    elif verdict in ("DECLINED", "NO-VERDICT", "ERROR", "PENDING"):
        trust = "none"
    else:
        trust = res.get("trust") or "sound"
    why = res.get("why") or ""
    basis = res.get("basis") or f"fvwork {verdict}: {why}"
    wall = total_s if total_s is not None else (res.get("latency_s") or 0.0)
    diags = []
    for att in res.get("attempts") or []:
        for mod_d in att.get("diagnostics") or []:
            mod = mod_d.get("module")
            for m in mod_d.get("messages") or []:
                pos = m.get("pos") or {}
                diags.append({
                    "rule_id": "FV001",
                    "severity": m.get("severity") if m.get("severity") in VALID_SEVERITIES else "error",
                    "file": mod,
                    "line": max(1, int(pos.get("line") or 1)),
                    "column": max(0, int(pos.get("column") or 0)) + 1,   # Lean's pos.column is 0-based
                    "end_line": None,
                    "end_column": None,
                    "message": str(m.get("data") or ""),
                    "source": "lean",
                })
    if verdict != "ACCEPTED" and not diags:
        diags = classify_verdict_diagnostic(verdict, why, basis)
    fr = res.get("frontier")
    ledger = res.get("ledger")
    frontier_block = None
    if fr is not None or ledger is not None:
        frontier_block = {
            "frontier_size": len(fr) if isinstance(fr, list) else 0,
            "remaining": [e.get("name") for e in (fr or []) if isinstance(e, dict) and e.get("name")],
            "frontier": fr or [],
            "ledger": ledger,
            "base_advanced": res.get("base_advanced"),
        }
    return make_envelope(
        mode="frontier" if verdict == "CONDITIONAL" else "project_incremental",
        verdict=verdict,
        trust=trust,
        verdict_basis=basis,
        total_s=wall,
        reason=why,
        target={
            "project": project_dir,
            "challenge_sha256": res.get("challenge_sha256"),
            "export_sha256": res.get("export_sha256"),
            "base_advanced": res.get("base_advanced"),
        },
        timing_extra={
            "queue_s": res.get("queue_s"),
            "build_s": res.get("build_s"),
            "export_s": res.get("export_s"),
            "check_s": res.get("check_s"),
        },
        diagnostics=diags,
        frontier=frontier_block,
        statement_audit=res.get("drift"),
        raw=res if include_raw else None,
    )


def from_error(mode, message, total_s=0.0, target=None):
    return make_envelope(
        mode=mode,
        verdict="ERROR",
        trust="none",
        verdict_basis=f"error: {sanitize_single_line(message, 400)}",
        total_s=total_s,
        reason=sanitize_single_line(message, 400),
        target=target,
        diagnostics=classify_verdict_diagnostic("ERROR", message),
    )


def enforce_process_exit(env, rc, mode, total_s=None):
    """Fail closed to ERROR (exit 2) if a subprocess's OS exit status disagrees with a definite JSON verdict
    (no exit/JSON disagreement in fv check, no signal/trap mismatch after the decision, across fv and MCP)."""
    if not isinstance(env, dict):
        return from_error(mode, f"invalid envelope (rc={rc})", total_s or 0.0)
    v = env.get("verdict")
    expected = {"ACCEPTED": 0, "REJECTED": 1, "CONDITIONAL": 3}.get(v)
    if expected is not None and rc != expected:
        return from_error(
            mode,
            f"subprocess exit/JSON mismatch: exited {rc} while JSON reported {v}",
            total_s if total_s is not None else (env.get("timing") or {}).get("total_s", 0.0),
            target=env.get("target"),
        )
    return env


# --------------------------------------------------------------------------- LSP & SARIF emitters
def to_lsp_diagnostics(envelope):
    """Convert API v1 envelope diagnostics to LSP 3.17 Diagnostics grouped by file URI/path."""
    sev_map = {"error": 1, "warning": 2, "info": 3, "hint": 4}
    by_file = {}
    for d in envelope.get("diagnostics") or []:
        fp = d.get("file") or "<verification>"
        line0 = max(0, (d.get("line") or 1) - 1)
        col0 = max(0, (d.get("column") or 1) - 1)
        eline0 = max(line0, (d.get("end_line") or (line0 + 1)) - 1)
        ecol0 = max(col0, (d.get("end_column") or (col0 + 1)) - 1)
        by_file.setdefault(fp, []).append({
            "range": {
                "start": {"line": line0, "character": col0},
                "end": {"line": eline0, "character": ecol0},
            },
            "severity": sev_map.get(d.get("severity"), 1),
            "code": d.get("rule_id") or "FV001",
            "source": d.get("source") or "fastverify",
            "message": d.get("message") or "",
        })
    return {
        "api_version": API_VERSION,
        "verdict": envelope.get("verdict"),
        "accepted": envelope.get("accepted"),
        "trust": envelope.get("trust"),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "files": by_file,
    }


def to_sarif_210(envelope, tool_version="1.0.0"):
    """Emit a valid OASIS SARIF 2.1.0 report for GitHub Code Scanning / VS Code SARIF Viewer."""
    level_map = {"error": "error", "warning": "warning", "info": "note", "hint": "note"}
    results = []
    used_rules = set()
    for d in envelope.get("diagnostics") or []:
        rid = d.get("rule_id") if d.get("rule_id") in SARIF_RULES else "FV001"
        used_rules.add(rid)
        r = {
            "ruleId": rid,
            "level": level_map.get(d.get("severity"), "error"),
            "message": {"text": d.get("message") or ""},
        }
        fp = d.get("file")
        if fp:
            loc = {
                "physicalLocation": {
                    "artifactLocation": {"uri": fp.lstrip("/") if not fp.startswith("file://") else fp},
                }
            }
            if d.get("line"):
                region = {"startLine": max(1, int(d["line"]))}
                if d.get("column"):
                    region["startColumn"] = max(1, int(d["column"]))
                loc["physicalLocation"]["region"] = region
            r["locations"] = [loc]
        results.append(r)
    rules = [SARIF_RULES[k] for k in sorted(used_rules)] if used_rules else list(SARIF_RULES.values())
    return {
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "version": "2.1.0",
        "runs": [{
            "tool": {
                "driver": {
                    "name": "fastverify",
                    "version": tool_version,
                    "informationUri": "https://github.com/Light-Prover/Light-Prover",
                    "rules": rules,
                }
            },
            "invocations": [{
                "executionSuccessful": envelope.get("verdict") not in ("ERROR", "DECLINED", "NO-VERDICT"),
                "properties": {
                    "verdict": envelope.get("verdict"),
                    "accepted": envelope.get("accepted"),
                    "reward": envelope.get("reward"),
                    "trust": envelope.get("trust"),
                    "verdict_basis": envelope.get("verdict_basis"),
                    "timing": envelope.get("timing"),
                },
            }],
            "results": results,
        }],
    }


# --------------------------------------------------------------------------- schema validator
def validate_batch_v1(obj):
    """the documented batch summary (MCP fv_verify_batch), validated ON ITS OWN entry point:
    validate_v1 is the single-envelope contract and never accepts a batch summary. Items
 are attempt envelopes with indices 0..n-1 in order."""
    errs = []
    if not isinstance(obj, dict):
        return ["root must be a JSON object"]
    if obj.get("mode") != "batch_attempt":
        errs.append("mode must be 'batch_attempt'")

    def one_of(v, allowed):
        return isinstance(v, str) and v in allowed
    # the documented batch summary (MCP fv_verify_batch): count / accepted_count /
    # best_accepted_index over a list of {id, index, result} whose results are v1 attempt envelopes, each validated
    if obj.get("api_version") != API_VERSION:
        errs.append(f"api_version must be {API_VERSION!r}")
    res = obj.get("results")
    if not isinstance(res, list):
        return errs + ["results must be a list"]
    acc = []
    for i, it in enumerate(res):
        if not isinstance(it, dict) or not isinstance(it.get("result"), dict):
            errs.append(f"results[{i}] must be an object with an object result")
            continue
        if type(it.get("index")) is not int or it.get("index") != i:   # the producer's zero-based candidate order
            errs.append(f"results[{i}].index must be the integer {i}")
        if it["result"].get("mode") != "attempt":   # items are attempt envelopes, never a nested batch
            errs.append(f"results[{i}].result.mode must be 'attempt'")
        errs.extend(f"results[{i}].result: {e}" for e in validate_v1(it["result"]))
        if it["result"].get("accepted") is True:
            acc.append(it.get("index"))
    if type(obj.get("count")) is not int or obj.get("count") != len(res):
        errs.append("count must be the number of results")
    if type(obj.get("accepted_count")) is not int or obj.get("accepted_count") != len(acc):
        errs.append("accepted_count must be the number of accepted results")
    bai = obj.get("best_accepted_index")
    if (bai is not None and type(bai) is not int) or (bai is None) != (not acc) or (bai is not None and bai not in acc):
        errs.append("best_accepted_index must be the index of an accepted result (null if none)")
    if not one_of(obj.get("trust"), VALID_TRUST):
        errs.append(f"invalid trust: {obj.get('trust')!r}")
    return errs


def validate_v1(obj):
    """Lightweight stdlib structural validator against result-v1.schema.json.
    Returns list of error strings (empty list == valid)."""
    errs = []
    if not isinstance(obj, dict):
        return ["root must be a JSON object"]

    def one_of(v, allowed):   # an unhashable value (list, object) is invalid, never a TypeError
        return isinstance(v, str) and v in allowed
    req = ("api_version", "mode", "verdict", "accepted", "reward", "exit_code", "trust", "verdict_basis", "timing", "diagnostics")
    for k in req:
        if k not in obj:
            errs.append(f"missing required key: {k}")
    if obj.get("api_version") != API_VERSION:
        errs.append(f"api_version must be {API_VERSION!r}")
    if not one_of(obj.get("mode"), VALID_MODES):
        errs.append(f"invalid mode: {obj.get('mode')!r}")
    elif obj.get("mode") == "batch_attempt":   # a batch summary is never a single envelope
        errs.append("mode 'batch_attempt' is a batch summary, not a single result envelope (validate it with validate_batch_v1)")
    if not one_of(obj.get("verdict"), VALID_VERDICTS):
        errs.append(f"invalid verdict: {obj.get('verdict')!r}")
    acc_ok = one_of(obj.get("verdict"), VALID_VERDICTS) and one_of(obj.get("trust"), VALID_TRUST) and \
        counts_as_accepted(obj.get("verdict"), obj.get("trust"))
    if not isinstance(obj.get("accepted"), bool):
        errs.append("accepted must be boolean")
    elif obj["accepted"] != acc_ok:
        errs.append("accepted invariant violated: must equal (verdict == 'ACCEPTED' and trust in %s)" % sorted(ACCEPTING_TRUST))
    if obj.get("reward") not in (0.0, 1.0, 0, 1) or isinstance(obj.get("reward"), bool):
        errs.append("reward must be 0.0 or 1.0")
    elif float(obj["reward"]) != (1.0 if acc_ok else 0.0):
        errs.append("reward invariant violated: must be 1.0 iff accepted (verdict ACCEPTED with a sound-family trust)")
    if not isinstance(obj.get("exit_code"), int) or isinstance(obj.get("exit_code"), bool):
        errs.append("exit_code must be integer")
    elif obj.get("verdict") == "ACCEPTED" and (obj["exit_code"] == 0) != acc_ok:
        errs.append("exit_code invariant violated: 0 iff accepted")
    elif one_of(obj.get("verdict"), VALID_VERDICTS) and one_of(obj.get("trust"), VALID_TRUST) and \
            obj["exit_code"] != acceptance_exit_code(obj["verdict"], obj["trust"]):
        # the full verdict <-> exit-code table: 0 = a counted ACCEPTED, 1 = REJECTED,
        # 3 = CONDITIONAL, 2 = everything else (incl. an ACCEPTED under a non-counting trust)
        errs.append(f"exit_code invariant violated: verdict {obj['verdict']} with trust {obj['trust']} requires exit_code "
                    f"{acceptance_exit_code(obj['verdict'], obj['trust'])}, not {obj['exit_code']}")
    if not one_of(obj.get("trust"), VALID_TRUST):
        errs.append(f"invalid trust: {obj.get('trust')!r}")
    if not isinstance(obj.get("timing"), dict) or not isinstance(obj["timing"].get("total_s"), (int, float)):
        errs.append("timing.total_s must be a number")
    if not isinstance(obj.get("diagnostics"), list):
        errs.append("diagnostics must be a list")
    else:
        for i, d in enumerate(obj["diagnostics"]):
            if not isinstance(d, dict):
                errs.append(f"diagnostics[{i}] must be object")
                continue
            for fk in ("rule_id", "severity", "message"):
                if not isinstance(d.get(fk), str):
                    errs.append(f"diagnostics[{i}].{fk} must be string")
            if not one_of(d.get("severity"), VALID_SEVERITIES):
                errs.append(f"diagnostics[{i}].severity invalid: {d.get('severity')!r}")
    return errs


if __name__ == "__main__":
    import sys
    if len(sys.argv) == 3 and sys.argv[1] == "validate":
        try:   # unreadable / invalid JSON: a structured invalid result (exit 1), not a traceback
            with open(sys.argv[2], encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, ValueError, RecursionError) as ex:
            print(json.dumps({"valid": False, "errors": [f"cannot read JSON: {type(ex).__name__}: {str(ex)[:200]}"]}))
            sys.exit(1)
        try:
            e = validate_batch_v1(data) if isinstance(data, dict) and data.get("mode") == "batch_attempt" \
                else validate_v1(data)   # each contract on its own entry point, chosen by mode
        except Exception as ex:  # noqa: BLE001 - defensive: never a traceback for a malformed document
            e = [f"validator error on a malformed document: {type(ex).__name__}: {str(ex)[:200]}"]
        if e:
            print(json.dumps({"valid": False, "errors": e}))
            sys.exit(1)
        print(json.dumps({"valid": True, "errors": []}))
        sys.exit(0)
    print("usage: fv_schema.py validate FILE.json", file=sys.stderr)
    sys.exit(2)

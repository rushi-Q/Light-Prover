#!/usr/bin/python3 -I
"""triage.py — Fast sandboxed Pre-Proving Sub-Lemma Triage Gate.

Runs BEFORE dispatching open sorry sub-lemmas to expensive prover agents.
Performs:
  1. Static statement hazard lints (<5 ms):
     - Unused explicit data binders (variables never occurring in hypotheses or conclusion)
     - Unguarded partial operations (Nat.sub / `-` on Nat without <=/<, division `/` without != 0 / 0 <,
       Int.toNat, Real.sqrt without 0 <=, List.get!/head!)
     - Suspicious trivial conclusion (`True`) or `False` literal hypothesis
  2. Sandboxed Lean 4 elaboration & bounded-heartbeat refutation/vacuity probes (bwrap --unshare-all):
     - Probe A (AUTO_IMPLICIT_TRAP): re-elaborate signature under `set_option autoImplicit false`
       and `relaxedAutoImplicit false`; catches typos silently turned into universal variables!
     - Probe B (REFUTED — machine-checked proof of ¬ L_i): attempts to prove the negation of L_i
       via push_neg + omega/linarith/norm_num/decide/simp + concrete small boundary instantiations
       (0, 1, 2, -1, [], true, false). ZERO false positives: Lean's kernel checks the refutation!
     - Probe C (VACUOUS_PREMISES — machine-checked proof of H_1 -> ... -> H_k -> False):
       attempts to prove False from the hypotheses via omega/linarith/nlinarith/norm_num/decide/simp_all/tauto.
       ZERO false positives: Lean's kernel checks the contradiction!
     - Probe D (TRIVIAL_WITHOUT_HYPS): checks whether the conclusion already holds unconditionally
       after dropping all propositional hypotheses.
     - Probe E (AUTO_SOLVABLE): tries a 1-line standard tactic (rfl/omega/ring/norm_num/linarith/decide/simp/tauto)
       so trivial sub-lemmas are closed immediately without burning an LLM call!

All Lean probes execute strictly inside a network-less bwrap sandbox (S4).
"""
import argparse
import concurrent.futures as cf
import json
import os
import re
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
import common as C


def parse_binders_and_conclusion(header_text):
    """Parse `theorem name (b1 : T1) {b2 : T2} [b3 : T3] : C` into:
      {name, univ_params, binders: [{kind, names, type, is_prop_like, raw}], conclusion}
    Best-effort syntactic parser that handles Unicode identifiers, comments, and nested delimiters.
    """
    clean_hdr = C.strip_comments_preserving_lines(header_text)
    m = re.search(rf"\b(?:theorem|lemma)\s+({C.LEAN_IDENT_RE_STR})", clean_hdr)
    if not m:
        return None
    name = m.group(1)
    rest = clean_hdr[m.end():].strip()
    univ_params = ""
    if rest.startswith(".{"):
        end_u = rest.find("}")
        if end_u != -1:
            univ_params = rest[:end_u + 1]
            rest = rest[end_u + 1:].strip()

    binders = []
    i = 0
    n = len(rest)
    while i < n:
        while i < n and rest[i].isspace():
            i += 1
        if i >= n:
            break
        if rest[i] == ":":
            conclusion = rest[i + 1:].strip()
            return {"name": name, "univ_params": univ_params, "binders": binders, "conclusion": conclusion}
        if rest[i] in "({[":
            open_c = rest[i]
            close_c = {"(": ")", "{": "}", "[": "]"}[open_c]
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if rest[j] == open_c:
                    depth += 1
                elif rest[j] == close_c:
                    depth -= 1
                j += 1
            raw = rest[i:j]
            inner = raw[1:-1].strip()
            # Split inner at top-level ':'
            col = _find_top_level_colon(inner)
            if col != -1:
                lhs = inner[:col].strip()
                rhs = inner[col + 1:].strip()
                bnames = [x for x in lhs.split() if re.match(rf"^{C._LEAN_IDENT_PART}$", x)]
            else:
                bnames = []
                rhs = inner
            is_prop_like = _looks_like_prop(rhs, bnames)
            binders.append({
                "kind": open_c,
                "names": bnames,
                "type": rhs,
                "is_prop_like": is_prop_like,
                "is_known_data": _is_known_data_type(rhs),
                "raw": raw,
            })
            i = j
        else:
            # Unexpected token before ':' -> abort structured parse
            return None
    return None


def _find_top_level_colon(s):
    depth = 0
    for idx, ch in enumerate(s):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            return idx
    return -1


_DATA_TYPES = {
    "Nat", "ℕ", "PNat", "ℕ+", "Int", "ℤ", "Rat", "ℚ", "Real", "ℝ", "NNReal", "ℝ≥0", "ENNReal", "ℝ≥0∞",
    "Complex", "ℂ", "Bool", "String", "Char", "Unit", "PUnit",
}
_DATA_PREFIX_RE = re.compile(
    r"^(?:Fin|List|Array|Set|Finset|Multiset|Option|Vector|Matrix|ZMod|Polynomial|Subgroup|Subring|Submodule|"
    r"Ideal|EuclideanSpace|SchwartzMap|ContinuousMap|LinearMap|RingHom|AddMonoidHom|MonoidHom|Equiv|"
    r"Type|Sort|WithTop|WithBot|Measure|ProbabilityMeasure)\b"
)
_PROP_PRED_RE = re.compile(
    r"(?:\b(?:Is[A-Z]\w*|Has[A-Z]\w*|Even|Odd|Prime|Irreducible|Continuous\w*|Measurable\w*|"
    r"Differentiable\w*|Analytic\w*|ContDiff|Summable|Integrable|Tendsto|Nontrivial|Subsingleton|"
    r"Nonempty|Finite|Infinite|Compact\w*|Convex|Monotone|Antitone|StrictMono|Injective|Surjective|"
    r"Bijective|Martingale|Supermartingale|Submartingale|Filter\.\w+|Set\.EqOn|Function\.\w+|"
    r"Asymptotics\.\w+|PSF_Conditions|True|False)\b|\.Prime\b)"
)


def _is_known_data_type(ty):
    """True when `ty` is unambiguously a Lean data/universe type (never a Prop hypothesis)."""
    t = ty.strip()
    if t == "Prop":
        return False
    # Any logical/relational operator or Prop predicate means it's a proposition, not a data type
    if any(op in t for op in ("=", "≠", "<", "≤", ">", "≥", "↔", "∧", "∨", "¬", "∀", "∃", "∣", "∈", "⊆", "⊂", "=o[", "=O[")):
        return False
    if _PROP_PRED_RE.search(t):
        return False
    if t in _DATA_TYPES or _DATA_PREFIX_RE.match(t):
        return True
    # Function type between data types (e.g. `ℝ → ℝ`, `Fin n → ℕ`, `ℂ → ℂ`), excluding Prop codomains
    if "→" in t:
        parts = [p.strip() for p in t.split("→")]
        if all(p in _DATA_TYPES or bool(_DATA_PREFIX_RE.match(p)) or re.match(r"^[A-Zα-ωΑ-Ω][0-9'₀-₉]*$", p) for p in parts if p):
            return True
    return False


def _looks_like_prop(ty, bnames=None):
    """Heuristic to distinguish propositional hypotheses (e.g. `x > 0`, `Summable f`, `a = b`) from data binders."""
    t = ty.strip()
    if t == "Prop":
        return False
    if _is_known_data_type(t):
        return False
    if any(op in t for op in ("=", "≠", "<", "≤", ">", "≥", "↔", "∧", "∨", "¬", "→", "∀", "∃", "∣", "∈", "⊆", "⊂", "=o[", "=O[")):
        return True
    if _PROP_PRED_RE.search(t):
        return True
    if bnames and len(bnames) == 1 and re.match(r"^h(?:[A-Z0-9_']|[a-z](?:[A-Z0-9_']|$))", bnames[0]):
        return True
    return False


_SAFE_DIV_DENOM_RE = re.compile(
    r"^(?:\(?\s*[1-9][0-9]*(?:\.[0-9]+)?(?:\s*:\s*[ℝℚℂℤℕA-Za-z]+)?\s*\)?|"
    r"π|Real\.pi|\(?\s*[1-9][0-9]*\s*\*\s*(?:π|Real\.pi)\s*\)?|"
    r"Nat\.factorial\b|ZLattice\.covolume\b)"
)


def _has_unguarded_var_division(conc):
    """True when conclusion contains `/` with a non-constant, non-positive-literal denominator."""
    # Asymptotic statements (`=o[atTop]`, `=O[atTop]`, `IsEquivalent atTop`) evaluate for large x where x != 0
    if "atTop" in conc and ("=o[" in conc or "=O[" in conc or "IsEquivalent" in conc):
        return False
    for m in re.finditer(r"(?<![/\-])/(?![/\-])\s*(\([^)]*\)|[^\s,;:)}\]+*^-]+)", conc):
        denom = m.group(1).strip()
        if not denom or _SAFE_DIV_DENOM_RE.match(denom):
            continue
        return True
    return False


def static_lints(header_text, parsed):
    """Fast static hazard lints on a theorem signature."""
    warnings = []
    if not parsed:
        return warnings
    binders = parsed["binders"]
    conc = parsed["conclusion"]
    all_prop_types = [b["type"] for b in binders if b["is_prop_like"]]
    all_hyp_text = " ".join(all_prop_types)
    full_stmt = all_hyp_text + " " + conc

    # 1. Unused explicit data binders (only flag known data types to avoid false positives on Prop hypotheses)
    for idx, b in enumerate(binders):
        if b["kind"] != "(" or b["is_prop_like"] or not b.get("is_known_data"):
            continue
        later_text = " ".join(x["type"] for x in binders[idx + 1:]) + " " + conc
        for v in b["names"]:
            if v == "_" or v.startswith("_"):
                continue
            if not re.search(rf"(?<![\w']){re.escape(v)}(?![\w'])", later_text):
                warnings.append({
                    "code": "UNUSED_DATA_BINDER",
                    "severity": "warn",
                    "message": f"explicit data binder '{v} : {b['type']}' is never used in hypotheses or conclusion",
                })

    # 2. Unguarded Nat subtraction
    has_nat = any(b["type"].strip() in ("Nat", "ℕ") for b in binders if not b["is_prop_like"])
    if has_nat and re.search(r"(?:Nat\.sub|\s-\s)", conc):
        if not any(op in all_hyp_text for op in ("≤", "<=", "<", "≥", ">=", ">")):
            warnings.append({
                "code": "UNGUARDED_NAT_SUB",
                "severity": "warn",
                "message": "Nat subtraction in conclusion with no ordering guard (≤/<) in hypotheses (truncates at 0)",
            })

    # 3. Unguarded division (skipping nonzero constants like / 2, / π, and asymptotic atTop)
    if _has_unguarded_var_division(conc):
        if not any(tok in all_hyp_text for tok in ("≠ 0", "!= 0", "0 <", "> 0", "1 <", "> 1", "≥ 1", ">= 1", "≥ 2", "NeZero", "Pos", "PNat", "ℕ+")):
            warnings.append({
                "code": "UNGUARDED_DIV",
                "severity": "warn",
                "message": "division in conclusion with no non-zero / positivity guard in hypotheses (Lean defines x / 0 = 0)",
            })

    # 4. Partial-op helpers
    if "Int.toNat" in full_stmt and not any(op in all_hyp_text for op in ("0 ≤", "0 <=", "≥ 0", ">= 0", "0 <", "> 0")):
        warnings.append({"code": "UNGUARDED_INT_TONAT", "severity": "warn", "message": "Int.toNat used without non-negativity guard"})
    if "Real.sqrt" in full_stmt and not any(op in all_hyp_text for op in ("0 ≤", "0 <=", "≥ 0", ">= 0", "0 <", "> 0")):
        warnings.append({"code": "UNGUARDED_REAL_SQRT", "severity": "warn", "message": "Real.sqrt used without non-negativity guard"})

    # 5. Trivial True conclusion / False hypothesis
    if conc.strip() == "True":
        warnings.append({"code": "TRIVIAL_TRUE_CONCLUSION", "severity": "high", "message": "conclusion is literally True"})
    if any(t.strip() == "False" for t in all_prop_types):
        warnings.append({"code": "FALSE_HYPOTHESIS", "severity": "high", "message": "hypothesis is literally False"})

    return warnings


def _build_univ_prop(parsed):
    """Build `∀ (b1) (b2) ..., conclusion` expression text from parsed signature."""
    if not parsed["binders"]:
        return f"({parsed['conclusion']})"
    bs = " ".join(b["raw"] for b in parsed["binders"])
    return f"(∀ {bs}, {parsed['conclusion']})"


def _tactic_set(has_mathlib):
    if has_mathlib:
        return {
            "prove": "first | rfl | omega | ring | norm_num | linarith | decide | simp | tauto",
            "vacuous": "first | contradiction | omega | linarith | nlinarith | norm_num | decide | simp_all | tauto",
            "refute_direct": "first | (push_neg; first | omega | decide | norm_num | linarith | tauto | simp) | (intro h; first | omega | decide | simp_all) | decide | omega",
            "hyp_arg": "(by first | omega | norm_num | linarith | decide | simp | tauto)",
            "contra_from_hc": "first | omega | linarith | (norm_num at hc; linarith) | (norm_num at hc) | decide | (simp at hc) | contradiction",
        }
    return {
        "prove": "first | rfl | omega | decide | simp",
        "vacuous": "first | contradiction | omega | decide | simp_all",
        "refute_direct": "first | (intro h; first | omega | decide | simp_all) | decide | omega",
        "hyp_arg": "(by first | omega | decide | simp)",
        "contra_from_hc": "first | omega | decide | (simp at hc) | contradiction",
    }


def _generate_counterexample_tactics(parsed, has_mathlib=False):
    """Generate targeted witness instantiations for explicit universal data binders.
    Works in BOTH core-only Lean 4 and Mathlib (does not require push_neg!).
    """
    explicit_binders = []
    data_slots = []
    for b in parsed["binders"]:
        if b["kind"] != "(":
            continue
        if b["is_prop_like"]:
            count = max(1, len(b["names"]))
            for _ in range(count):
                explicit_binders.append(("prop", None))
        else:
            for v in b["names"]:
                data_slots.append((len(explicit_binders), v, b["type"].strip()))
                explicit_binders.append(("data", (v, b["type"].strip())))
    # Limit combinatorial blowup to <= 3 explicit data vars
    if not data_slots or len(data_slots) > 3:
        return []
    vals_by_ty = {
        "Nat": ["0", "1", "2", "3"],
        "ℕ": ["0", "1", "2", "3"],
        "Int": ["0", "1", "-1", "2"],
        "ℤ": ["0", "1", "-1", "2"],
        "Rat": ["0", "1", "-1"],
        "ℚ": ["0", "1", "-1"],
        "Real": ["0", "1", "-1", "2"],
        "ℝ": ["0", "1", "-1", "2"],
        "Bool": ["false", "true"],
    }
    lists = []
    for _, _, ty in data_slots:
        if ty in vals_by_ty:
            lists.append(vals_by_ty[ty])
        elif ty.startswith("List "):
            lists.append(["[]"])
        else:
            return []
    import itertools
    tset = _tactic_set(has_mathlib)
    tactics = []
    for combo in itertools.product(*lists):
        if len(tactics) >= 24:
            break
        val_map = {slot_idx: val for (slot_idx, _, _), val in zip(data_slots, combo)}
        app_args = []
        for idx, (kind, _) in enumerate(explicit_binders):
            if kind == "data":
                v = val_map[idx]
                app_args.append(f"({v})" if v.startswith("-") else v)
            else:
                app_args.append(tset["hyp_arg"])
        w_label = ", ".join(f"{nm}={val}" for (_, nm, _), val in zip(data_slots, combo))
        tac = f"intro h; have hc := h {' '.join(app_args)}; {tset['contra_from_hc']}"
        tactics.append((w_label, tac))
    return tactics


def generate_probe_lean(context_before, header_text, parsed, max_heartbeats=80000):
    """Construct a Lean probe file that runs Probes A..E in ONE lean invocation (~0.5-2s)."""
    has_mathlib = bool(re.search(r"^\s*import\s+Mathlib\b", context_before, re.M))
    tset = _tactic_set(has_mathlib)
    lines = [context_before.rstrip(), "", "-- === FASTVERIFY SUB-LEMMA TRIAGE PROBES ==="]

    # Probe A: autoImplicit false check (strip leading attributes/modifiers, rename to _fv_probe_autoimpl)
    m_hdr = re.search(rf"\b(?:theorem|lemma)\s+{C.LEAN_IDENT_RE_STR}([\s\S]*)$", header_text)
    sig_rest = m_hdr.group(1) if m_hdr else ""
    if sig_rest:
        lines += [
            "section _FV_Probe_A",
            "set_option autoImplicit false",
            "set_option relaxedAutoImplicit false",
            "set_option linter.all false",
            f"private theorem _fv_probe_autoimpl{sig_rest} := sorry",
            "end _FV_Probe_A",
            "",
        ]

    ce_tactics = []
    if parsed:
        univ_prop = _build_univ_prop(parsed)
        univ_suffix = parsed["univ_params"]
        # Probe B: Refutation (prove ¬ ∀ ..., C)
        ce_tactics = _generate_counterexample_tactics(parsed, has_mathlib=has_mathlib)
        lines += [
            "section _FV_Probe_B",
            "set_option linter.all false",
            f"set_option maxHeartbeats {max_heartbeats}",
            f"private theorem _fv_probe_refute_direct{univ_suffix} : ¬ {univ_prop} := by",
            f"  {tset['refute_direct']}",
            "end _FV_Probe_B",
            "",
        ]
        # Witness-specific counterexamples (emit up to 16 crisp concrete witness tests in one check)
        if ce_tactics:
            lines += [
                "section _FV_Probe_B_CE",
                "set_option linter.all false",
                f"set_option maxHeartbeats {max_heartbeats}",
            ]
            for idx, (w_label, tac) in enumerate(ce_tactics[:16]):
                lines += [
                    f"private theorem _fv_probe_ce_{idx}{univ_suffix} : ¬ {univ_prop} := by",
                    f"  {tac}",
                ]
            lines += ["end _FV_Probe_B_CE", ""]

        # Probe C: Vacuity (contradictory premises -> False)
        prop_binders = [b for b in parsed["binders"] if b["is_prop_like"]]
        if prop_binders:
            bs_all = " ".join(b["raw"] for b in parsed["binders"])
            lines += [
                "section _FV_Probe_C",
                "set_option linter.all false",
                f"set_option maxHeartbeats {max_heartbeats}",
                f"private theorem _fv_probe_vacuous{univ_suffix} {bs_all} : False := by",
                f"  {tset['vacuous']}",
                "end _FV_Probe_C",
                "",
            ]
            # Probe D: Dropped-hypothesis triviality
            # Only if no prop binder name appears in the conclusion
            prop_names = [nm for b in prop_binders for nm in b["names"]]
            conc = parsed["conclusion"]
            if not any(re.search(rf"\b{re.escape(nm)}\b", conc) for nm in prop_names):
                non_prop_bs = " ".join(b["raw"] for b in parsed["binders"] if not b["is_prop_like"])
                lines += [
                    "section _FV_Probe_D",
                    "set_option linter.all false",
                    f"set_option maxHeartbeats {max_heartbeats}",
                    f"private theorem _fv_probe_nohyps{univ_suffix} {non_prop_bs} : {conc} := by",
                    f"  {tset['prove']}",
                    "end _FV_Probe_D",
                    "",
                ]

        # Probe E: Already auto-solvable in 1 line?
        bs_all = " ".join(b["raw"] for b in parsed["binders"])
        lines += [
            "section _FV_Probe_E",
            "set_option linter.all false",
            f"set_option maxHeartbeats {max_heartbeats}",
            f"private theorem _fv_probe_autosolve{univ_suffix} {bs_all} : {parsed['conclusion']} := by",
            f"  {tset['prove']}",
            "end _FV_Probe_E",
            "",
        ]
    return "\n".join(lines) + "\n", ce_tactics[:16]


def triage_one_task(task, build_tree, packages_ws, tc_prefix, timeout_s=30, max_heartbeats=80000):
    t0 = time.monotonic()
    lname = task["lemma"]
    header = task.get("statement_header") or ""
    parsed = parse_binders_and_conclusion(header) if header else None
    warnings = static_lints(header, parsed)

    result = {
        "lemma": lname,
        "id": task.get("id"),
        "status": "PASS",
        "refuted": False,
        "counterexample": None,
        "vacuous": False,
        "auto_implicit_trap": False,
        "auto_implicit_detail": None,
        "trivial_without_hyps": False,
        "auto_solvable": False,
        "warnings": warnings,
        "triage_s": 0.0,
    }

    prompt_code = task.get("prompt_code")
    if not prompt_code or not header:
        result["triage_s"] = round(time.monotonic() - t0, 3)
        return result

    # Extract context_before from prompt_code (everything before header)
    idx_h = prompt_code.rfind(header)
    context_before = prompt_code[:idx_h] if idx_h != -1 else ""
    probe_src, ce_list = generate_probe_lean(context_before, header, parsed, max_heartbeats=max_heartbeats)

    lean_bin = os.path.join(tc_prefix, "bin", "lean")
    lean_path = C.collect_lean_path(build_tree, packages_ws)

    with tempfile.TemporaryDirectory(prefix="fv-triage-") as td:
        pfile = os.path.join(td, "Probe.lean")
        with open(pfile, "w", encoding="utf-8") as f:
            f.write(probe_src)
        # Map line ranges of each probe section in Probe.lean so we know WHICH probes succeeded vs errored!
        sec_ranges = {}
        plines = probe_src.splitlines()
        cur_sec = None
        for ln_no, ln in enumerate(plines, 1):
            m_s = re.match(r"^section (_FV_Probe_\w+)", ln)
            if m_s:
                cur_sec = m_s.group(1)
                sec_ranges[cur_sec] = [ln_no, ln_no]
            elif cur_sec and ln.startswith(f"end {cur_sec}"):
                sec_ranges[cur_sec][1] = ln_no
                cur_sec = None
        # Also record exact line of each _fv_probe_ce_K
        ce_lines = {}
        for ln_no, ln in enumerate(plines, 1):
            m_ce = re.match(r"^private theorem _fv_probe_ce_(\d+)", ln)
            if m_ce:
                ce_lines[int(m_ce.group(1))] = (ln_no, ln_no + 1)

        ro = [build_tree, packages_ws, tc_prefix, td]
        env_extra = {
            "PATH": f"{tc_prefix}/bin:/usr/bin:/bin",
            "LEAN_PATH": lean_path,
            "HOME": "/tmp",
            "TMPDIR": "/tmp",
        }
        rc, out, err, wall = C.run_bwrap(
            [lean_bin, "-j", "1", pfile],
            ro_binds=ro, rw_binds=[], env_extra=env_extra, cwd=build_tree, timeout=timeout_s,
        )
        combined = out + "\n" + err

        # Parse errors by line number (handles both `error:` and Lean 4.20+ `error(lean.xxx):`)
        err_lines = {}
        for ln in combined.splitlines():
            m = re.match(r"^[^:]+:(\d+):\d+:\s*error(?:\([^)]*\))?:\s*(.*)$", ln)
            if m:
                lno = int(m.group(1))
                err_lines.setdefault(lno, []).append(m.group(2))

        def sec_has_error(sec):
            if sec not in sec_ranges:
                return True
            lo, hi = sec_ranges[sec]
            return any(lo <= el <= hi for el in err_lines)

        def sec_errors(sec):
            if sec not in sec_ranges:
                return []
            lo, hi = sec_ranges[sec]
            return [msg for el, msgs in sorted(err_lines.items()) if lo <= el <= hi for msg in msgs]

        # If context_before itself had an error (before _FV_Probe_A), abort probes cleanly
        a_start = sec_ranges.get("_FV_Probe_A", [10**9])[0]
        if any(el < a_start for el in err_lines):
            result["warnings"].append({
                "code": "TRIAGE_CONTEXT_ERROR",
                "severity": "info",
                "message": "context before lemma failed to elaborate in isolated probe",
            })
            result["triage_s"] = round(time.monotonic() - t0, 3)
            return result

        # Probe A: autoImplicit false
        if sec_has_error("_FV_Probe_A"):
            a_errs = sec_errors("_FV_Probe_A")
            if any("unknown identifier" in e.lower() or "unknown constant" in e.lower() or "autoimplicit" in e.lower() for e in a_errs):
                result["auto_implicit_trap"] = True
                result["auto_implicit_detail"] = "; ".join(a_errs[:3])
                result["status"] = "AUTO_IMPLICIT_TRAP"
                result["warnings"].append({
                    "code": "AUTO_IMPLICIT_TRAP",
                    "severity": "critical",
                    "message": f"signature relies on autoImplicit (likely typo): {result['auto_implicit_detail']}",
                })

        # Probe B: Refutation (direct or concrete counterexample witness)
        if "_FV_Probe_B" in sec_ranges and not sec_has_error("_FV_Probe_B"):
            result["refuted"] = True
            result["counterexample"] = "direct refutation proved ¬statement"
            result["status"] = "REFUTED"
        elif ce_lines:
            for idx, (lo, hi) in sorted(ce_lines.items()):
                if not any(lo <= el <= hi for el in err_lines):
                    w_label = ce_list[idx][0] if idx < len(ce_list) else f"witness_{idx}"
                    result["refuted"] = True
                    result["counterexample"] = f"witness ({w_label}) proved ¬statement"
                    result["status"] = "REFUTED"
                    break

        # Probe C: Vacuity (contradictory premises -> False)
        if "_FV_Probe_C" in sec_ranges and not sec_has_error("_FV_Probe_C"):
            result["vacuous"] = True
            if result["status"] == "PASS":
                result["status"] = "VACUOUS"
            result["warnings"].append({
                "code": "VACUOUS_PREMISES",
                "severity": "critical",
                "message": "hypotheses are provably contradictory (H_1 -> ... -> H_k -> False)",
            })

        # Probe D: Dropped-hypothesis triviality
        if "_FV_Probe_D" in sec_ranges and not sec_has_error("_FV_Probe_D"):
            result["trivial_without_hyps"] = True
            result["warnings"].append({
                "code": "TRIVIAL_WITHOUT_HYPS",
                "severity": "warn",
                "message": "conclusion is provable without any of the propositional hypotheses",
            })

        # Probe E: Auto-solvable
        if "_FV_Probe_E" in sec_ranges and not sec_has_error("_FV_Probe_E"):
            result["auto_solvable"] = True

        if result["status"] == "PASS" and any(w["severity"] in ("high", "critical") for w in result["warnings"]):
            result["status"] = "WARN"

    result["triage_s"] = round(time.monotonic() - t0, 3)
    return result


def run_triage(args):
    t0 = time.monotonic()
    manifest = json.load(open(args.manifest, encoding="utf-8"))
    base_tree = manifest["base_build_tree"]
    packages_ws = manifest["packages_workspace"]
    tc_prefix = manifest["toolchain_prefix"]
    out_dir = os.path.dirname(os.path.realpath(args.manifest))
    ledger_path = os.path.join(out_dir, "ledger.json")

    tasks = []
    for sc in manifest.get("subchallenges", []):
        if args.lemma and sc["lemma"] != args.lemma:
            continue
        tasks.append(json.load(open(sc["task_json"], encoding="utf-8")))

    with cf.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        results = list(ex.map(
            lambda t: triage_one_task(t, base_tree, packages_ws, tc_prefix, args.timeout, args.max_heartbeats),
            tasks,
        ))

    # Cross-frontier internal duplicate detection using authoritative `type_sha256` from manifest/check-frontier
    seen_type_sha = {}
    tsha_by_lemma = {sc["lemma"]: sc.get("type_sha256") for sc in manifest.get("subchallenges", []) if sc.get("type_sha256")}
    for r in results:
        tsha = tsha_by_lemma.get(r["lemma"])
        r["duplicate_of"] = None
        if tsha and tsha != C.sha256_str(""):
            if tsha in seen_type_sha:
                orig = seen_type_sha[tsha]
                r["duplicate_of"] = orig
                r["warnings"].append({
                    "code": "DUPLICATE_OPEN_LEMMA",
                    "severity": "warn",
                    "message": f"exact same statement hash as open frontier lemma '{orig}' (prove once, reuse!)",
                })
            else:
                seen_type_sha[tsha] = r["lemma"]

    # Update ledger.json if present
    if os.path.isfile(ledger_path) and not args.no_ledger_update:
        ledger = json.load(open(ledger_path, encoding="utf-8"))
        for r in results:
            entry = ledger.get("lemmas", {}).get(r["lemma"])
            if entry is not None:
                entry["triage"] = {
                    "status": r["status"],
                    "refuted": r["refuted"],
                    "counterexample": r["counterexample"],
                    "vacuous": r["vacuous"],
                    "auto_implicit_trap": r["auto_implicit_trap"],
                    "auto_solvable": r["auto_solvable"],
                    "duplicate_of": r["duplicate_of"],
                    "warning_codes": [w["code"] for w in r["warnings"]],
                    "triage_s": r["triage_s"],
                }
                if r["status"] in ("REFUTED", "VACUOUS", "AUTO_IMPLICIT_TRAP") and entry["status"] == "open":
                    entry["status"] = "triaged_bad"
        ledger["updated_at"] = C.now_iso()
        ledger.setdefault("history", []).append({
            "event": "triage",
            "at": C.now_iso(),
            "checked": len(results),
            "refuted": sum(1 for r in results if r["refuted"]),
            "vacuous": sum(1 for r in results if r["vacuous"]),
            "auto_implicit": sum(1 for r in results if r["auto_implicit_trap"]),
            "auto_solvable": sum(1 for r in results if r["auto_solvable"]),
        })
        C.atomic_write_json(ledger_path, ledger)

    report = {
        "schema": "fv-triage-report-v1",
        "created_at": C.now_iso(),
        "manifest": os.path.realpath(args.manifest),
        "total_checked": len(results),
        "counts": {
            "PASS": sum(1 for r in results if r["status"] == "PASS"),
            "REFUTED": sum(1 for r in results if r["status"] == "REFUTED"),
            "VACUOUS": sum(1 for r in results if r["status"] == "VACUOUS"),
            "AUTO_IMPLICIT_TRAP": sum(1 for r in results if r["status"] == "AUTO_IMPLICIT_TRAP"),
            "WARN": sum(1 for r in results if r["status"] == "WARN"),
            "auto_solvable": sum(1 for r in results if r["auto_solvable"]),
        },
        "wall_s": round(time.monotonic() - t0, 3),
        "results": results,
    }
    if args.out:
        C.atomic_write_json(args.out, report)
    else:
        C.atomic_write_json(os.path.join(out_dir, "triage.json"), report)
    print(json.dumps(report, ensure_ascii=False))
    return 0


def main():
    ap = argparse.ArgumentParser(description="Pre-proving sandboxed triage gate for minted sub-challenges.")
    ap.add_argument("manifest", help="Path to manifest.json produced by mint.py")
    ap.add_argument("--lemma", default=None, help="Triage a single lemma by full name")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--max-heartbeats", type=int, default=80000)
    ap.add_argument("--out", default=None, help="Output JSON report path (default: <manifest_dir>/triage.json)")
    ap.add_argument("--no-ledger-update", action="store_true")
    args = ap.parse_args()
    sys.exit(run_triage(args))


if __name__ == "__main__":
    main()

#!/usr/bin/python3 -I
"""render_ci_report.py — Render PR Markdown summary, SARIF 2.1.0, GitHub Actions outputs,
and statement-drift / illegal-axiom / sorry-frontier alerts from an API v1 envelope (D14).
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
FV_ROOT = os.path.realpath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(FV_ROOT, "schemas"))
import fv_schema  # noqa: E402


def render_markdown(env, cache_mode="cold", commit=None, prev_env=None):
    v = env["verdict"]
    trust = env["trust"]
    t = env.get("timing") or {}
    # PASS only for an acceptance that counts (fv_schema.counts_as_accepted: sound-family trust); an ACCEPTED under
    # UNSAFE / unofficial / official trust is shown as NOT ACCEPTED (fail-closed), never as a sound pass
    accepted_badge = ("PASS — NOTARY ACCEPTED" if trust == "notary" else "PASS — SOUND ACCEPTED") if env.get("accepted") \
        else f"NOT ACCEPTED — trust {trust} is not a sound acceptance (FAIL-CLOSED)"
    badge = {
        "ACCEPTED": accepted_badge,
        "REJECTED": "FAIL — REJECTED",
        "CONDITIONAL": "CONDITIONAL — ACCEPTED MODULO SORRY FRONTIER",
        "ACCEPTED_MODULO_FRONTIER": "CONDITIONAL — ACCEPTED MODULO SORRY FRONTIER",
        "DECLINED": "NO VERDICT — DECLINED (FAIL-CLOSED)",
        "NO-VERDICT": "NO VERDICT (FAIL-CLOSED)",
        "ERROR": "ERROR — NO VERDICT (FAIL-CLOSED)",
    }.get(v, v)

    diags = env.get("diagnostics") or []
    drift = [d for d in diags if d.get("rule_id") == "FV002"]
    axioms = [d for d in diags if d.get("rule_id") == "FV003"]
    kernel = [d for d in diags if d.get("rule_id") == "FV004"]

    lines = [
        f"## fastverify CI Gate: `{badge}`",
        "",
        f"| Field | Value |",
        f"|---|---|",
        f"| **Verdict** | `{v}` (`accepted={env['accepted']}`, `reward={env['reward']}`) |",
        f"| **Trust** | `{trust}` |",
        f"| **CI Mode** | `{cache_mode}` |",
        f"| **Wall Time** | `{t.get('total_s', 0):.2f} s` |",
    ]
    if commit:
        lines.append(f"| **Commit** | `{commit[:12]}` |")
    pin = (env.get("target") or {}).get("challenge_sha256")
    if pin:
        lines.append(f"| **Pinned Challenge SHA-256** | `{pin[:16]}…` |")

    stage_rows = []
    for label, key in (("Build", "build_s"), ("Export", "export_s"), ("Trusted Check", "check_s")):
        if t.get(key) is not None:
            stage_rows.append(f"{label}: `{t[key]:.2f}s`")
    if stage_rows:
        lines.append(f"| **Stages** | " + " · ".join(stage_rows) + " |")
    lines.append("")

    if drift:
        lines.append("> [!CAUTION]")
        lines.append("> **STATEMENT DRIFT ALERT (`FV002`)**: Target theorem statements or pinned definitions no longer match the official challenge export!")
        for d in drift[:5]:
            lines.append(f"> - {d['message']}")
        lines.append("")
    if axioms:
        lines.append("> [!CAUTION]")
        lines.append("> **ILLEGAL AXIOM / CHEAT ALERT (`FV003`)**: Disallowed axiom (`sorryAx`, `native_decide`, or custom axiom) found in target closure!")
        for d in axioms[:5]:
            lines.append(f"> - {d['message']}")
        lines.append("")
    if kernel:
        lines.append("> [!WARNING]")
        lines.append("> **KERNEL REJECTION (`FV004`)**: Trusted official Lean kernel or required second kernel rejected a declaration.")
        for d in kernel[:5]:
            lines.append(f"> - {d['message']}")
        lines.append("")

    fr = env.get("frontier")
    if isinstance(fr, dict):
        rem = fr.get("remaining") or fr.get("frontier") or []
        prev_rem = (prev_env.get("frontier") or {}).get("remaining") if isinstance(prev_env, dict) else None
        lines.append("### Sorry-Frontier Progress Ledger")
        rw = fr.get("rewrite")
        if rw:
            lines.append(f"- Frontier rewrite mode: `{rw}`")
        lines.append(f"- Remaining open frontier lemmas: **{len(rem) if isinstance(rem, list) else rem}**")
        if isinstance(rem, list) and isinstance(prev_rem, list):
            closed = sorted(set(prev_rem) - set(rem))
            added = sorted(set(rem) - set(prev_rem))
            lines.append(f"- Closed since previous base: **{len(closed)}** {closed[:10]}")
            if added:
                lines.append(f"- Newly added open lemmas: **{len(added)}** {added[:10]}")
        bs = fr.get("base_status")
        if isinstance(bs, dict):
            proved = bs.get("proved") or []
            dropped = bs.get("dropped") or []
            if proved:
                lines.append(f"- Verified proved (closed from base frontier): **{len(proved)}** {proved[:10]}")
            if dropped:
                lines.append("")
                lines.append("> [!WARNING]")
                lines.append(f"> **FRONTIER LEMMA DROPPED FROM CLOSURE**: {len(dropped)} previously open lemma(s) no longer appear in the targets' closure ({dropped[:10]}). Verify proofs did not bypass intended lemmas.")
        fr_entries = fr.get("frontier") or []
        if isinstance(fr_entries, list) and any(isinstance(e, dict) and e.get("source") for e in fr_entries):
            lines.append("")
            lines.append("<details><summary>Open frontier statements as written (display only; authoritative = pinned frontier challenge)</summary>\n")
            for e in fr_entries[:20]:
                if not isinstance(e, dict):
                    continue
                nm = e.get("name") or "?"
                srcs = e.get("source") or []
                if isinstance(srcs, list) and srcs and isinstance(srcs[0], dict):
                    s0 = srcs[0]
                    stmt = " ".join(str(s0.get("statement_as_written") or "").split())[:200]
                    lines.append(f"- `{nm}` (`{s0.get('file')}:{s0.get('line')}`): `{stmt}`")
                else:
                    lines.append(f"- `{nm}`")
            lines.append("\n</details>")
        lines.append("")

    if diags and not (drift or axioms or kernel):
        lines.append("### Diagnostics")
        for d in diags[:15]:
            loc = f"`{d['file']}:{d['line']}:{d['column']}` " if d.get("file") and d.get("line") else ""
            lines.append(f"- **{d['severity'].upper()}** `[{d['rule_id']}]` {loc}{d['message'].splitlines()[0]}")
        lines.append("")

    lines.append(f"<details><summary>Verdict basis</summary>\n\n`{env.get('verdict_basis', '')}`\n\n</details>\n")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input-kind", choices=["fastverify", "incr", "frontier", "v1"], required=True)
    ap.add_argument("--input", required=True)
    ap.add_argument("--out-json", required=True)
    ap.add_argument("--out-sarif", required=True)
    ap.add_argument("--out-md", required=True)
    ap.add_argument("--cache-mode", default="cold")
    ap.add_argument("--project", default=None)
    ap.add_argument("--challenge", default=None)
    ap.add_argument("--challenge-sha256", default=None)
    ap.add_argument("--commit", default=None)
    ap.add_argument("--wall-s", type=float, default=None)
    ap.add_argument("--prev-v1", default=None)
    args = ap.parse_args()

    def load(path):   # an unreadable / truncated report is no report (-> the error envelope)
        try:
            return json.load(open(path, encoding="utf-8")) if path and os.path.isfile(path) else None
        except (OSError, ValueError):
            return None
    raw = load(args.input)
    if args.input_kind == "v1" and isinstance(raw, dict):
        env = raw
    elif args.input_kind == "frontier":
        env = fv_schema.from_check_frontier_result(raw, export_path=None, challenge_sha256=args.challenge_sha256,
                                                   total_s=args.wall_s, include_raw=False)
        env["target"]["project"] = args.project
        env["target"]["challenge"] = args.challenge
    elif args.input_kind == "incr":
        env = fv_schema.from_incr_summary(raw, args.project, args.challenge, args.challenge_sha256,
                                          total_s=args.wall_s, include_raw=False)
    else:
        env = fv_schema.from_fastverify_result(raw, total_s=args.wall_s, project_dir=args.project, include_raw=False)

    fv_schema.normalize_acceptance(env)   # accepted / reward / exit_code from verdict + trust, for every input kind
    if args.commit:
        env["target"]["commit"] = args.commit
    prev_env = load(args.prev_v1)
    if not isinstance(prev_env, dict):
        prev_env = None

    with open(args.out_json, "w", encoding="utf-8") as f:
        json.dump(env, f, indent=2)
    with open(args.out_sarif, "w", encoding="utf-8") as f:
        json.dump(fv_schema.to_sarif_210(env), f, indent=2)
    md = render_markdown(env, cache_mode=args.cache_mode, commit=args.commit, prev_env=prev_env)
    with open(args.out_md, "w", encoding="utf-8") as f:
        f.write(md)

    # Write GitHub Actions step outputs & job summary when running under GitHub Actions
    gh_out = os.environ.get("GITHUB_OUTPUT")
    if gh_out:
        with open(gh_out, "a", encoding="utf-8") as f:
            f.write(f"verdict={env['verdict']}\n")
            f.write(f"accepted={'true' if env['accepted'] else 'false'}\n")
            f.write(f"trust={env['trust']}\n")
            f.write(f"exit_code={env['exit_code']}\n")
            f.write(f"wall_seconds={env['timing'].get('total_s', 0)}\n")
            f.write(f"result_json={os.path.realpath(args.out_json)}\n")
            f.write(f"sarif_file={os.path.realpath(args.out_sarif)}\n")
            f.write(f"summary_markdown={os.path.realpath(args.out_md)}\n")
    gh_sum = os.environ.get("GITHUB_STEP_SUMMARY")
    if gh_sum:
        with open(gh_sum, "a", encoding="utf-8") as f:
            f.write(md + "\n")

    print(json.dumps({
        "verdict": env["verdict"],
        "accepted": env["accepted"],
        "exit_code": env["exit_code"],
        "cache_mode": args.cache_mode,
        "wall_s": env["timing"].get("total_s"),
    }))
    return env["exit_code"]


if __name__ == "__main__":
    sys.exit(main())

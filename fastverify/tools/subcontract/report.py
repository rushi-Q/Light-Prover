#!/usr/bin/python3 -I
"""report.py — Progress Ledger Dashboard, PR Summary & Smart Dispatch Queue for tools/subcontract.

Reads `manifest.json` + `ledger.json` (+ optional `triage.json`) produced by `mint.py` / `triage.py` / `merge.py`
and emits:
  - Structured JSON summary (`fv-subcontract-report-v1`, default)
  - Crisp Markdown PR/CI dashboard (`--markdown`)
  - Priority-ordered dispatch queue (`--next-batch N`): skips closed and `triaged_bad`
    (REFUTED / VACUOUS / AUTO_IMPLICIT_TRAP) and internal duplicate frontier lemmas,
    prioritizing `auto_solvable` 1-liners first, then clean open lemmas.
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
import common as C


def build_report(ledger_path, manifest_path=None, next_batch=0):
    ledger = json.load(open(ledger_path, encoding="utf-8"))
    base_dir = os.path.dirname(os.path.realpath(ledger_path))
    if not manifest_path:
        cand = os.path.join(base_dir, "manifest.json")
        if os.path.isfile(cand):
            manifest_path = cand
    manifest = json.load(open(manifest_path, encoding="utf-8")) if manifest_path and os.path.isfile(manifest_path) else {}
    sc_by_name = {sc["lemma"]: sc for sc in manifest.get("subchallenges", [])}

    lemmas = ledger.get("lemmas") or {}
    total = len(lemmas)
    counts = {"closed": 0, "open": 0, "triaged_bad": 0, "other": 0}
    auto_solvable = []
    triaged_bad = []
    duplicates = []
    agents = {}

    rows = []
    for lname, entry in sorted(lemmas.items()):
        st = entry.get("status", "open")
        if st in counts:
            counts[st] += 1
        else:
            counts["other"] += 1
        tr = entry.get("triage") or {}
        tr_status = tr.get("status", "UNTESTED")
        if st == "triaged_bad" or tr_status in ("REFUTED", "VACUOUS", "AUTO_IMPLICIT_TRAP"):
            triaged_bad.append({
                "lemma": lname,
                "status": tr_status,
                "counterexample": tr.get("counterexample"),
                "warnings": tr.get("warning_codes") or [],
            })
        if st == "open" and tr.get("auto_solvable"):
            auto_solvable.append(lname)
        if tr.get("duplicate_of"):
            duplicates.append({"lemma": lname, "duplicate_of": tr["duplicate_of"]})
        cb = entry.get("closed_by")
        if cb:
            ag = agents.setdefault(cb, {"closed": 0, "lemmas": []})
            ag["closed"] += 1
            ag["lemmas"].append(lname)
        sc = sc_by_name.get(lname, {})
        rows.append({
            "lemma": lname,
            "status": st,
            "file": sc.get("rel_file") or entry.get("rel_file"),
            "line": sc.get("start_line") or entry.get("start_line"),
            "triage_status": tr_status,
            "auto_solvable": bool(tr.get("auto_solvable")),
            "duplicate_of": tr.get("duplicate_of"),
            "warnings": tr.get("warning_codes") or [],
            "closed_by": cb,
            "task_json": sc.get("task_json"),
        })

    # Smart dispatch queue: only open lemmas that are NOT triaged_bad and NOT duplicates of another open lemma
    dispatchable = []
    for r in rows:
        if r["status"] != "open":
            continue
        if r["triage_status"] in ("REFUTED", "VACUOUS", "AUTO_IMPLICIT_TRAP"):
            continue
        dup = r.get("duplicate_of")
        if dup and lemmas.get(dup, {}).get("status") == "open":
            continue
        # Priority: 0 = auto_solvable 1-liner, 1 = clean PASS no warnings, 2 = PASS/WARN with advisory lints, 3 = UNTESTED
        if r["auto_solvable"]:
            prio = 0
        elif r["triage_status"] == "PASS" and not r["warnings"]:
            prio = 1
        elif r["triage_status"] in ("PASS", "WARN"):
            prio = 2
        else:
            prio = 3
        dispatchable.append((prio, r["lemma"], r))
    dispatchable.sort(key=lambda x: (x[0], x[1]))
    queue = [
        {"priority": p, "lemma": nm, "task_json": r["task_json"], "file": r["file"], "line": r["line"], "auto_solvable": r["auto_solvable"]}
        for p, nm, r in dispatchable
    ]
    if next_batch > 0:
        queue = queue[:next_batch]

    pct = round(100.0 * counts["closed"] / total, 1) if total else 100.0
    return {
        "schema": "fv-subcontract-report-v1",
        "generated_at": C.now_iso(),
        "ledger": os.path.realpath(ledger_path),
        "parent_verdict": ledger.get("parent_verdict"),
        "day100_complete": bool(ledger.get("parent_verdict") == "ACCEPTED" and counts["open"] == 0 and counts["triaged_bad"] == 0),
        "progress_pct": pct,
        "counts": {
            "total": total,
            "closed": counts["closed"],
            "open": counts["open"],
            "triaged_bad": counts["triaged_bad"],
            "auto_solvable_open": len(auto_solvable),
            "duplicate_open": len(duplicates),
            "dispatchable": len(dispatchable),
        },
        "agents": agents,
        "triaged_bad": triaged_bad,
        "duplicates": duplicates,
        "next_batch": queue,
        "lemmas": rows,
        "history_events": len(ledger.get("history") or []),
    }


def format_markdown(rep):
    c = rep["counts"]
    lines = [
        f"### Sub-Challenge Frontier Progress (`{rep['parent_verdict']}` — {c['closed']}/{c['total']} closed, {rep['progress_pct']}%)",
        "",
        f"- **Open dispatchable**: {c['dispatchable']} (incl. {c['auto_solvable_open']} `auto_solvable` 1-liners)",
        f"- **Blocked by triage**: {c['triaged_bad']} (`REFUTED` / `VACUOUS` / `AUTO_IMPLICIT_TRAP`), **Internal duplicates**: {c['duplicate_open']}",
        "",
        "| Lemma | Location | Status | Triage | Notes |",
        "|---|---|---|---|---|",
    ]
    for r in rep["lemmas"]:
        loc = f"`{r['file']}:{r['line']}`" if r.get("file") else "—"
        notes = []
        if r.get("closed_by"):
            notes.append(f"proved by `{r['closed_by']}`")
        if r.get("auto_solvable") and r["status"] == "open":
            notes.append("`auto_solvable`")
        if r.get("duplicate_of"):
            notes.append(f"dup of `{r['duplicate_of']}`")
        if r.get("warnings"):
            notes.append(", ".join(r["warnings"][:3]))
        lines.append(f"| `{r['lemma']}` | {loc} | **{r['status']}** | {r['triage_status']} | {'; '.join(notes) or '—'} |")
    if rep["next_batch"]:
        lines += ["", "**Recommended next dispatch batch:** " + ", ".join(f"`{q['lemma']}`" for q in rep["next_batch"][:10])]
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description="Progress ledger dashboard & smart dispatch queue for tools/subcontract.")
    ap.add_argument("ledger", help="Path to ledger.json (or OUT_DIR containing ledger.json)")
    ap.add_argument("--manifest", default=None, help="Optional path to manifest.json")
    ap.add_argument("--markdown", action="store_true", help="Print Markdown PR/CI dashboard instead of JSON")
    ap.add_argument("--next-batch", type=int, default=0, help="Limit next_batch dispatch queue to N lemmas (0 = all)")
    args = ap.parse_args()
    lp = args.ledger
    if os.path.isdir(lp):
        lp = os.path.join(lp, "ledger.json")
    rep = build_report(lp, manifest_path=args.manifest, next_batch=args.next_batch)
    if args.markdown:
        sys.stdout.write(format_markdown(rep))
    else:
        print(json.dumps(rep, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())

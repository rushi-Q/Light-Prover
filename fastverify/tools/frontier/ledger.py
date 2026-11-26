#!/usr/bin/python3 -I
"""tools/frontier/ledger.py - progress ledger and merge gate between two conditional verdicts. UNTRUSTED
reporting: it only compares two results; every verdict it reads came from the trusted check.

  ledger.py diff BASE CURRENT [--json FILE]
  ledger.py gate BASE CURRENT [--allow-new] [--allow-changed] [--require-progress] [--block-dropped] [--json FILE]

BASE / CURRENT = a result of bin/fastverify (result.json, with --modulo-frontier), of check/frontier/check-frontier.sh (its
JSON line) or of tools/frontier/frontier.py (verdict.json). Output (diff): verdicts base -> current; open lemmas CLOSED
since the base (proved or no longer needed), NEW open lemmas, CHANGED statements (same name, different statement digest),
REMAINING ones; the frontier challenge digest of both. When CURRENT was produced with `check-frontier.sh --base BASE`,
closed lemmas are split into PROVED (still used, now without a sorry of their own) and DROPPED (no longer in the targets'
closure: maybe still sorried in the sources - a "frontier collapse" warning, e.g. a target proved by a trivial witness).

gate (a PR / merge gate): exit 0 = mergeable, 1 = blocked, 2 = cannot judge. Blocked when the current verdict is not
ACCEPTED/CONDITIONAL, or (unless allowed) a new open lemma appears, or (unless allowed) an open lemma's statement changed
(statement drift: the goalposts of an open lemma moved), or with --require-progress when nothing was closed. Target
statements need no gate: the trusted check pins them to the official challenge in every run.
"""
import json
import sys


def load(path):
    with open(path, encoding="utf-8") as f:
        t = f.read()
    try:
        j = json.loads(t)
    except ValueError:
        lines = [l for l in t.splitlines() if l.strip()]
        j = json.loads(lines[-1])
    if isinstance(j.get("frontier"), dict):          # bin/fastverify result.json
        fr = j["frontier"]
        return {"verdict": j.get("verdict"), "frontier": fr.get("frontier") or [], "base_status": fr.get("base_status"),
                "frontier_challenge_sha256": fr.get("frontier_challenge_sha256"), "source": "result.json"}
    v = j.get("verdict")
    if v == "ACCEPTED_MODULO_FRONTIER":
        v = "CONDITIONAL"
    return {"verdict": v, "frontier": j.get("frontier") or [], "base_status": j.get("base_status"),
            "frontier_challenge_sha256": j.get("frontier_challenge_sha256"), "source": j.get("checker") or j.get("tool")}


def digest(e):
    if e.get("type_sha256"):
        return e["type_sha256"]
    return json.dumps([e.get("levelParams") or e.get("level_params") or [], e.get("type") or e.get("type_pp")], ensure_ascii=False)


def diff(base, cur):
    b = {e["name"]: e for e in base["frontier"] if isinstance(e, dict) and "name" in e}
    c = {e["name"]: e for e in cur["frontier"] if isinstance(e, dict) and "name" in e}
    closed = sorted(set(b) - set(c))
    new = sorted(set(c) - set(b))
    both = sorted(set(b) & set(c))
    changed = [n for n in both if digest(b[n]) != digest(c[n])]
    remaining = [n for n in both if n not in changed]
    st = cur.get("base_status") if isinstance(cur.get("base_status"), dict) else {}
    proved = [n for n in closed if st.get(n) == "proved"]
    dropped = [n for n in closed if st.get(n) == "absent"]
    return {
        "closed_proved": proved, "closed_dropped": dropped,
        "warnings": (["%d open lemma(s) left the targets' closure without being proved (%s): check that the targets' proofs "
                      "did not bypass them (trivial witness / vacuous statement?)" % (len(dropped), ", ".join(dropped[:10]))]
                     if dropped else []),
        "verdict": {"base": base["verdict"], "current": cur["verdict"]},
        "open": {"base": len(b), "current": len(c)},
        "closed": closed, "new": new, "changed": changed, "remaining": remaining,
        "changed_detail": [{"name": n, "base": b[n].get("type"), "current": c[n].get("type")} for n in changed],
        "new_detail": [{"name": n, "statement": c[n].get("type")} for n in new],
        "frontier_challenge_sha256": {"base": base.get("frontier_challenge_sha256"),
                                      "current": cur.get("frontier_challenge_sha256")},
    }


def human(d):
    s = ["verdict: %s -> %s; open lemmas: %d -> %d" % (d["verdict"]["base"], d["verdict"]["current"], d["open"]["base"],
                                                        d["open"]["current"])]
    for k, title in (("closed", "closed since base"), ("new", "NEW open lemmas"), ("changed", "CHANGED statements")):
        if d[k]:
            s.append("  %s (%d): %s" % (title, len(d[k]), ", ".join(d[k][:30]) + (" ..." if len(d[k]) > 30 else "")))
    for x in d["changed_detail"][:10]:
        s.append("    %s\n      base:    %s\n      current: %s" % (x["name"], (x["base"] or "?")[:240], (x["current"] or "?")[:240]))
    s.append("  remaining: %d" % len(d["remaining"]))
    if d.get("closed_proved") or d.get("closed_dropped"):
        s.append("  closed = proved %d + dropped %d" % (len(d["closed_proved"]), len(d["closed_dropped"])))
    for w in d.get("warnings") or []:
        s.append("  WARNING: " + w)
    return "\n".join(s)


def main(argv):
    if len(argv) < 3 or argv[0] not in ("diff", "gate"):
        sys.stderr.write(__doc__)
        return 2
    cmd, bp, cp = argv[0], argv[1], argv[2]
    opts = argv[3:]
    jout = opts[opts.index("--json") + 1] if "--json" in opts else None
    try:
        d = diff(load(bp), load(cp))
    except Exception as e:  # noqa: BLE001
        print(json.dumps({"error": "cannot read the results: %s" % e}))
        return 2
    rc = 0
    if cmd == "gate":
        why = []
        if d["verdict"]["current"] not in ("ACCEPTED", "CONDITIONAL"):
            why.append("current verdict %s" % d["verdict"]["current"])
        if d["new"] and "--allow-new" not in opts:
            why.append("%d new open lemma(s): %s" % (len(d["new"]), ", ".join(d["new"][:10])))
        if d["changed"] and "--allow-changed" not in opts:
            why.append("statement drift of %d open lemma(s): %s" % (len(d["changed"]), ", ".join(d["changed"][:10])))
        if d.get("closed_dropped") and "--block-dropped" in opts:
            why.append("%d open lemma(s) dropped without proof: %s" % (len(d["closed_dropped"]), ", ".join(d["closed_dropped"][:10])))
        if "--require-progress" in opts and not d["closed"] and d["verdict"]["current"] != "ACCEPTED":
            why.append("no open lemma closed")
        d["gate"] = {"mergeable": not why, "blocked_by": why}
        rc = 0 if not why else 1
    sys.stderr.write(human(d) + ("\n  gate: %s" % ("MERGEABLE" if rc == 0 else "BLOCKED: " + "; ".join(d["gate"]["blocked_by"]))
                                 if cmd == "gate" else "") + "\n")
    js = json.dumps(d, ensure_ascii=False)
    if jout:
        open(jout, "w", encoding="utf-8").write(js + "\n")
    print(js)
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

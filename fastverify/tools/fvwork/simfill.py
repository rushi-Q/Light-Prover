#!/usr/bin/python3 -I
"""tools/fvwork/simfill.py - DAY 1..99 SIMULATION on a real library through a running fvwork daemon (benchmark
harness, untrusted).

  simfill.py --state S --src SRC --plan PLAN.json [--agents N] [--rogue] [--think SEC] [--out FILE.tsv]

PLAN.json = {"targets": [...], "files": {"rel/File.lean": {"lemmas": ["shortName", ...], "target": "shortName"}}}.
Day 1 (architect): every listed lemma's tactic proof is replaced by `sorry` in one merge request -> expected CONDITIONAL
with exactly those lemmas as the frontier. Then N agents (threads; each owns whole files, so patches never conflict)
fill their lemmas one by one through MERGE requests (judged on the current base, enter the base only if ACCEPTED /
CONDITIONAL): per lemma first a broken attempt (does not elaborate), then the honest proof (the original). With --rogue
one more agent submits cheats against the current base: hidden sorry (the proof uses a new sorried helper), a project
axiom, a moved goalpost (a target restated as a trivial theorem), each of which today's compile-only loop accepts.
The run ends ACCEPTED when the last lemma is filled. One TSV row per submission: agent, kind, lemma, verdict, latency,
queue, frontier size, ledger, why.
"""
import argparse, json, os, re, sys, threading, time, importlib.util

_spec = importlib.util.spec_from_file_location("fvwork", os.path.join(os.path.dirname(os.path.realpath(__file__)), "fvwork.py"))
fvwork = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fvwork)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+([^\s(:{\[]+)")


def find(lines, short):
    """(decl_line, by_line, end_line) of theorem `short` in lines (end = first top-level line after it)"""
    a = next(i for i, ln in enumerate(lines) if (m := DECL.match(ln)) and m.group(2).split(".")[-1] == short.split(".")[-1])
    by = next(j for j in range(a, len(lines)) if lines[j].rstrip().endswith(":= by"))
    end = len(lines)
    for j in range(by + 1, len(lines)):
        ln = lines[j]
        if ln and not ln[0].isspace() and not ln.startswith(("--", "·")):
            end = j
            break
    while end - 1 > by and not lines[end - 1].strip():
        end -= 1
    return a, by, end


def replace_proof(text, short, new_lines):
    lines = text.split("\n")
    a, by, end = find(lines, short)
    return "\n".join(lines[:by + 1] + new_lines + lines[end:])


def proof_of(text, short):
    lines = text.split("\n")
    a, by, end = find(lines, short)
    return lines[by + 1:end]


def renamer(lemmas, suffix):
    """L -> L+suffix for every planned lemma (declaration and every use in the file): the architect introduces NEW lemma
    names, so the frontier lemmas are not constants of the official challenge (library-style challenges contain every
    library lemma; see the board note on kind mismatches)"""
    if not suffix:
        return lambda t: t
    pats = [(re.compile(r"(?<![\w'])" + re.escape(l.split(".")[-1]) + r"(?![\w'])"), l.split(".")[-1] + suffix) for l in lemmas]

    def ren(t):
        for p, r in pats:
            t = p.sub(r, t)
        return t
    return ren


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--state", required=True); ap.add_argument("--src", required=True); ap.add_argument("--plan", required=True)
    ap.add_argument("--agents", type=int, default=2); ap.add_argument("--rogue", action="store_true")
    ap.add_argument("--think", type=float, default=0.0); ap.add_argument("--out")
    ap.add_argument("--no-broken", action="store_true")
    ap.add_argument("--rename", default="_fv", help="suffix of the renamed planned lemmas ('' = keep the names)")
    ap.add_argument("--candidates", action="store_true",
                    help="agents judge every attempt first as a CANDIDATE (no-advance, concurrent) and submit a merge "
                         "only for an ACCEPTED / CONDITIONAL candidate (the merge is judged again on the current base)")
    ap.add_argument("--rogue-file", help="file (plan key) the rogue agent attacks (default: the first)")
    ap.add_argument("--emit-frontier", metavar="FILE",
                    help="only judge the day-1 decomposition (not merged) and write its frontier names to FILE (for "
                         "serve --allowed: the architect pins WHICH lemmas may stay open)")
    a = ap.parse_args()
    plan = json.load(open(a.plan))
    raw = {rel: open(os.path.join(a.src, rel), encoding="utf-8").read() for rel in plan["files"]}
    rens = {rel: renamer(f["lemmas"], a.rename) for rel, f in plan["files"].items()}
    # orig = the library with the planned lemmas under their new names (proved): the state "after" the development
    orig = {rel: rens[rel](t) for rel, t in raw.items()}
    for rel, f in plan["files"].items():
        f["lemmas"] = [l.split(".")[-1] + a.rename for l in f["lemmas"]]
    cur = dict(raw)
    lock = threading.Lock()
    out = open(a.out, "w") if a.out else sys.stdout
    cols = ["t", "agent", "kind", "file", "lemma", "verdict", "exit", "latency_s", "queue_s", "build_s", "export_s",
            "check_s", "frontier", "closed", "new", "restated", "merged", "why"]
    out.write("\t".join(cols) + "\n"); out.flush()
    t0 = time.time()

    def submit(agent, kind, rel, lemma, files, candidate=False):
        req = {"op": "verify", "files": files, "label": f"{agent}:{kind}:{lemma}"}
        if candidate:
            req["advance"] = False
            kind = kind + "?"
        else:
            req["merge"] = True
        r = fvwork.request(a.state, req)
        led = r.get("ledger") or {}
        merged = bool(r.get("base_advanced"))
        if merged:
            with lock:
                cur.update(files)
        row = {"t": round(time.time() - t0, 1), "agent": agent, "kind": kind, "file": rel, "lemma": lemma,
               "verdict": r.get("verdict"), "exit": r.get("exit"), "latency_s": r.get("latency_s"), "queue_s": r.get("queue_s"),
               "build_s": r.get("build_s"), "export_s": r.get("export_s"), "check_s": r.get("check_s"),
               "frontier": len(r["frontier"]) if isinstance(r.get("frontier"), list) else "",
               "closed": ",".join(led.get("closed_since_base") or []), "new": ",".join(led.get("new_since_base") or []),
               "restated": ",".join(led.get("restated_since_base") or []), "merged": merged,
               "why": (r.get("why") or "")[:200].replace("\t", " ").replace("\n", " ")}
        with lock:
            out.write("\t".join(str(row[c]) for c in cols) + "\n"); out.flush()
        return r

    # day 1: the architect's decomposition (every planned lemma -> sorry), one merge
    files = {}
    for rel, f in plan["files"].items():
        t = orig[rel]
        for lem in f["lemmas"]:
            ind = re.match(r"^(\s*)", proof_of(t, lem)[0]).group(1) or "  "
            t = replace_proof(t, lem, [ind + "sorry"])
        files[rel] = t
    if a.emit_frontier:
        r = fvwork.request(a.state, {"op": "verify", "files": files, "advance": False, "label": "architect:plan"})
        names = [e["name"] for e in (r.get("frontier") or [])]
        open(a.emit_frontier, "w").write("\n".join(names) + "\n")
        print(json.dumps({"verdict": r.get("verdict"), "frontier": names, "latency_s": r.get("latency_s")}))
        return
    submit("architect", "decompose", "*", "*", files)
    rels = list(plan["files"])
    owned = {k: rels[k::a.agents] for k in range(a.agents)}

    def agent(k):
        for rel in owned[k]:
            for lem in plan["files"][rel]["lemmas"]:
                body = proof_of(orig[rel], lem)
                ind = re.match(r"^(\s*)", body[0]).group(1) or "  "
                if not a.no_broken:
                    with lock:
                        t = cur[rel]
                    submit(f"agent{k}", "broken", rel, lem,
                           {rel: replace_proof(t, lem, [ind + "exact (by decide : (2 : Nat) + 2 = 5)"])}, candidate=a.candidates)
                    time.sleep(a.think)
                with lock:
                    t = cur[rel]
                fill = {rel: replace_proof(t, lem, body)}
                if a.candidates:
                    r = submit(f"agent{k}", "fill", rel, lem, fill, candidate=True)
                    if r.get("verdict") not in ("ACCEPTED", "CONDITIONAL"):
                        continue
                    with lock:   # the merge re-applies the fill to the base current now (other files may have moved)
                        fill = {rel: replace_proof(cur[rel], lem, body)}
                submit(f"agent{k}", "fill", rel, lem, fill)
                time.sleep(a.think)

    def rogue():
        rel = a.rogue_file or rels[0]
        f = plan["files"][rel]
        lem = f["lemmas"][-1]
        body = proof_of(orig[rel], lem)
        ind = re.match(r"^(\s*)", body[0]).group(1) or "  "
        time.sleep(a.think)
        # (1) hidden sorry: the lemma "is proved" but its proof uses a NEW sorried helper
        with lock:
            t = cur[rel]
        lines = t.split("\n")
        d, by, end = find(lines, lem)
        helper = [f"theorem {lem.split('.')[-1]}_fvw_helper : True := by", "  sorry", ""]
        t2 = "\n".join(lines[:d] + helper + lines[d:by + 1] + [ind + f"have _ := {lem.split('.')[-1]}_fvw_helper"] + body + lines[end:])
        submit("rogue", "hidden-sorry", rel, lem, {rel: t2})
        time.sleep(a.think)
        # (2) a project axiom smuggled into the proof
        with lock:
            t = cur[rel]
        lines = t.split("\n")
        d, by, end = find(lines, lem)
        ax = [f"axiom {lem.split('.')[-1]}_fvw_ax : True", ""]
        t3 = "\n".join(lines[:d] + ax + lines[d:by + 1] + [ind + f"have _ := {lem.split('.')[-1]}_fvw_ax"] + body + lines[end:])
        submit("rogue", "axiom", rel, lem, {rel: t3})
        time.sleep(a.think)
        # (3) moved goalpost: a target restated as a trivial theorem (its proof compiles)
        tgt = f["target"]
        with lock:
            t = cur[rel]
        lines = t.split("\n")
        d, by, end = find(lines, tgt)
        m = DECL.match(lines[d])
        kw = m.group(1)
        pre = lines[d][:m.start(1)]
        t4 = "\n".join(lines[:d] + [f"{pre}{kw} {m.group(2)} : True := by", "  trivial"] + lines[end:])
        submit("rogue", "restate-target", rel, tgt, {rel: t4})

    th = [threading.Thread(target=agent, args=(k,)) for k in range(a.agents)]
    if a.rogue:
        th.append(threading.Thread(target=rogue))
    for x in th:
        x.start()
    for x in th:
        x.join()
    # final state: everything filled -> ACCEPTED expected (no-op merge re-checks the base as it is)
    with lock:
        final = {rel: cur[rel] for rel in rels}
    submit("architect", "final", "*", "*", final)
    print(json.dumps({"elapsed_s": round(time.time() - t0, 1)}), file=sys.stderr)


if __name__ == "__main__":
    main()

#!/usr/bin/python3 -I
"""loop.py — the "frontier model proves a theorem" scenario against fvserve: K provers, each works on one
problem in an attempt -> verify -> feedback loop until its attempt is ACCEPTED (or the sequence ends), with a simulated
model think time per attempt. The verification part is REAL (every attempt goes through the service and its trusted
check); the model is replayed from the stream generator's attempts (bench/throughput/mkstream.py: per problem, the
attempts in stream order up to and including its first honest one = failures / cheats, then a correct proof).

    loop.py --state DIR --pset NAME STREAM_DIR [--provers K] [--think S] [--problems N] [--best-of B] [--out TSV]
            [--official-model PASS_S:FAIL_S]

--best-of B: every round submits B attempts of the problem at once (the next B of its sequence) and stops at the first
round with an ACCEPTED attempt. --official-model P:F: also print the end-to-end time the same loop would take if every
verification cost the measured official per-attempt latency (P s for an attempt that compiles, F s for one that does
not) - a MODEL, the inputs come from measured official runs (stated in the output).
"""
import argparse, collections, concurrent.futures as cf, json, os, sys, threading, time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__)), ".."))
import fvserve  # noqa: E402


def sequences(stream):
    lab = json.load(open(os.path.join(stream, "labels.json")))
    seq = collections.OrderedDict()
    for b in sorted(lab):
        for th, (kind, exp) in sorted(lab[b].items()):
            s = seq.setdefault(th, [])
            if s and s[-1][0] == "ok":
                continue                      # the problem is solved at its first honest attempt
            s.append((kind, exp, os.path.join(stream, b, th + ".lean")))
    return seq


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--state", required=True)
    ap.add_argument("--pset", required=True)
    ap.add_argument("--provers", type=int, default=8)
    ap.add_argument("--think", type=float, default=0.0)
    ap.add_argument("--problems", type=int, default=0)
    ap.add_argument("--best-of", type=int, default=1)
    ap.add_argument("--official-model", default=None)
    ap.add_argument("--out")
    ap.add_argument("stream")
    a = ap.parse_args()
    seqs = sequences(a.stream)
    probs = [p for p, s in seqs.items() if s and s[-1][0] == "ok"]
    if a.problems:
        probs = probs[:a.problems]
    rows, lock = [], threading.Lock()

    def prover(th):
        s = seqs[th]
        t0 = time.time()
        vsum, n, solved = 0.0, 0, False
        i = 0
        while i < len(s) and not solved:
            rnd = s[i:i + a.best_of]
            i += len(rnd)
            if a.think:
                time.sleep(a.think)          # the model writes the next attempt(s)
            tv = time.time()
            with cf.ThreadPoolExecutor(len(rnd)) as ex:
                res = list(ex.map(lambda x: fvserve.request(a.state, {"op": "verify", "pset": a.pset, "theorem": th,
                                                                       "source": open(x[2]).read()}), rnd))
            vsum += time.time() - tv
            n += len(rnd)
            for (kind, exp, _), r in zip(rnd, res):
                with lock:
                    rows.append({"theorem": th, "kind": kind, "expected": exp, "verdict": r.get("verdict"),
                                 "total_s": r.get("total_s"), "batch_size": r.get("batch_size")})
                if r.get("verdict") == "ACCEPTED":
                    solved = True
        return {"theorem": th, "attempts": n, "solved": solved, "wall_s": round(time.time() - t0, 3),
                "verify_s": round(vsum, 3), "kinds": [k for k, _, _ in s[:n]]}

    t = time.time()
    with cf.ThreadPoolExecutor(a.provers) as ex:
        res = list(ex.map(prover, probs))
    wall = time.time() - t
    mism = [r for r in rows if r["verdict"] != r["expected"]]
    false_acc = [r for r in rows if r["expected"] == "REJECTED" and r["verdict"] == "ACCEPTED"]
    summ = {"problems": len(res), "solved": sum(r["solved"] for r in res), "attempts": sum(r["attempts"] for r in res),
            "provers": a.provers, "think_s": a.think, "best_of": a.best_of, "wall_s": round(wall, 2),
            "median_time_to_solve_s": sorted(r["wall_s"] for r in res)[len(res) // 2],
            "verify_share": round(sum(r["verify_s"] for r in res) / max(1e-9, sum(r["wall_s"] for r in res)), 3),
            "median_verify_per_round_s": sorted(x["total_s"] or 0 for x in rows)[len(rows) // 2],
            "verdict_mismatches": len(mism), "false_accepts": len(false_acc)}
    if a.official_model:
        P, F = (float(x) for x in a.official_model.split(":"))
        # same loop, every verification at the official per-attempt latency (an attempt that does not compile: F)
        def off(r):
            k = r["kinds"]
            rounds = [k[i:i + a.best_of] for i in range(0, len(k), a.best_of)]
            return sum(a.think + max((F if kk == "fail" else P) for kk in rd) for rd in rounds)
        offs = [off(r) for r in res]
        # provers run in parallel: makespan of the per-problem times over K provers (greedy, in problem order)
        lanes = [0.0] * a.provers
        for x in offs:
            j = lanes.index(min(lanes))
            lanes[j] += x
        summ["official_model"] = {"pass_s": P, "fail_s": F, "median_time_to_solve_s": round(sorted(offs)[len(offs) // 2], 2),
                                  "makespan_s": round(max(lanes), 2)}
    print(json.dumps(summ))
    if a.out:
        with open(a.out, "w") as f:
            f.write("theorem\tattempts\tsolved\twall_s\tverify_s\tkinds\n")
            for r in res:
                f.write(f"{r['theorem']}\t{r['attempts']}\t{r['solved']}\t{r['wall_s']}\t{r['verify_s']}\t{','.join(r['kinds'])}\n")


if __name__ == "__main__":
    main()

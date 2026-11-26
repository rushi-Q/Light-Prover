#!/usr/bin/python3 -I
"""fuzz.py ROOT N SEED THREADS [PRESET]  -- property-based differential test of the sound mode on random shapes.

Draws N random cases BASE-SHAPE-N-CONTENT[-sorryK|-kfalseK] (core base; shape wide/deep/layered with 4-48 modules;
content tiny/tactic/private/typeclass/universe/automation/inductive/kernel; a defect in a random module with probability
2/3: `sorry` or a FALSE `decide +kernel` theorem, both in the export closure). The expected verdict is known by
construction (clean -> ACCEPTED, defect -> REJECTED), so the official flow is not needed; every case runs once through
`bin/fastverify --preset PRESET` (default sound) via run.py. Prints one line per case and a summary:
  FAIL CRITICAL  the preset ACCEPTED a case with a defect
  AVAIL          a clean case not ACCEPTED (availability) / a defect case without a verdict
  PASS           otherwise
"""
import json, os, random, subprocess, sys

H = os.path.dirname(os.path.abspath(__file__))


def draw(rnd):
    shape = rnd.choice(["wide", "deep", "layered"])
    if shape == "layered":
        L, W = rnd.randint(2, 6), rnd.randint(2, 8); n = f"{L}x{W}"; N = L * W
    else:
        N = rnd.randint(4, 48); n = str(N)
    content = rnd.choice(["tiny", "tactic", "private", "typeclass", "universe", "automation", "inductive", "kernel"])
    case = f"core-{shape}-{n}-{content}-s{rnd.randint(0, 999)}"
    r = rnd.random()
    if r < 1 / 3:
        return case, "ACCEPTED"
    k = rnd.randrange(N)
    return case + (f"-sorry{k}" if r < 2 / 3 else f"-kfalse{k}"), "REJECTED"


def main():
    if len(sys.argv) < 5:
        sys.exit(__doc__)
    root, n, seed, threads = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    preset = sys.argv[5] if len(sys.argv) > 5 else "sound"
    rnd = random.Random(seed)
    cases = [draw(rnd) for _ in range(n)]
    stats = {"PASS": 0, "AVAIL": 0, "FAIL CRITICAL": 0}
    for case, exp in cases:
        subprocess.run([sys.executable, "-I", os.path.join(H, "gen.py"), root, case], stdout=subprocess.DEVNULL, check=False)
        subprocess.run([sys.executable, "-I", os.path.join(H, "run.py"), root, case, preset, threads],
                       stdout=subprocess.DEVNULL, check=False)
        v, merged, procs = None, None, None
        for line in open(os.path.join(root, "results.jsonl")):
            r = json.loads(line)
            if r["case"] == case and r["preset"] == preset:
                v = r.get("verdict"); st = (r.get("sched") or {}).get("sched_start") or {}
                merged = st.get("merged_groups"); procs = (r.get("sched") or {}).get("module_events")
        if exp == "REJECTED" and v == "ACCEPTED":
            res = "FAIL CRITICAL"
        elif v != exp:
            res = "AVAIL"
        else:
            res = "PASS"
        stats[res] += 1
        print(f"{res} {case} expected={exp} {preset}={v} merged_groups={merged} lean_procs={procs}", flush=True)
    print("SUMMARY", json.dumps(stats))
    print("RESULT", "FAIL" if stats["FAIL CRITICAL"] else "PASS")


if __name__ == "__main__":
    main()

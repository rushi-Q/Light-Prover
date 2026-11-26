#!/usr/bin/python3 -I
"""diff.py CASES.tsv OUTDIR [--jobs N] [--threads T] [--sound PATH] [--oracle PATH] : differential test of two independent
implementations of the conditional (frontier) verdict on the SAME exports.

CASES.tsv: lines `id<TAB>export<TAB>challenge_export<TAB>comparator.json<TAB>expected` with expected one of
  REJECTED | OK:<name,name,...> (conditional with exactly this frontier; OK: = empty frontier / plain accept) | ? (no
  fixed expectation; only agreement is checked) | REJECTED-or-? ...
Judges:
  sound  = fastverify/check/frontier/check-frontier.sh (unchanged sound check on the export with permitted + sorryAx, plus
        fvfrontier-judge: canonical sorried theorems -> axioms in memory, official checkAxioms)
  oracle = the independent oracle fv-frontier --from-export --canonical-only (untrusted rewrite of the
        export, kernels + ccmp-frontier on the REWRITTEN export)
Each verdict is normalised to OK(frontier set) / REJ / NOV (no verdict). Rows: AGREE / DISAGREE / CRITICAL (an OK of
a case expected REJECTED by either judge) / UNEXPECTED (both agree but differ from the expectation).
"""
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

LL = "$LIGHT_LEAN"
SOUND = os.path.join(LL, "fastverify/check/frontier/check-frontier.sh")
ORACLE = os.environ.get("FV_FRONTIER_ORACLE", "fv-frontier")   # the independent oracle (pass --oracle PATH)
PLAIN = os.environ.get("FV_FRONTIER_PLAIN", "frontier.py")     # the zero-trusted-change frontier.py (third judge)


def norm_sound(j, rc):
    v = j.get("verdict")
    if rc == 0 and v == "ACCEPTED":
        return ("OK", ())
    if rc == 3 and v == "CONDITIONAL":
        return ("OK", tuple(sorted(e["name"] if isinstance(e, dict) else e for e in j.get("frontier") or [])))
    if rc == 1 and v == "REJECTED":
        return ("REJ", ())
    return ("NOV", ())


def norm_oracle(j, rc):
    v = j.get("verdict")
    if rc == 3 and v == "ACCEPTED_MODULO_FRONTIER":
        return ("OK", tuple(sorted(f["name"] for f in j.get("frontier") or [])))
    if rc == 0 and v == "ACCEPTED":
        return ("OK", ())
    if rc == 1 and v == "REJECTED":
        return ("REJ", ())
    return ("NOV", ())


def norm_plain(j, rc):
    v = j.get("verdict")
    if rc == 0 and v == "ACCEPTED":
        return ("OK", ())
    if rc == 3 and v == "ACCEPTED_MODULO_FRONTIER":
        return ("OK", tuple(sorted(f["name"] for f in j.get("frontier") or [])))
    if rc == 1 and v == "REJECTED":
        return ("REJ", ())
    return ("NOV", ())


def run_case(row, out, threads, sound, oracle, extra_sound, extra_oracle, plain=None):
    cid, exp_, chal, cfg, expect = row
    od = os.path.join(out, cid)
    os.makedirs(od, exist_ok=True)
    res = {"id": cid, "expect": expect}
    t = time.time()
    p = subprocess.run([sound, exp_, chal, cfg, "--threads", str(threads), "--json", os.path.join(od, "sound.json"),
                        "--log", os.path.join(od, "sound.log")] + extra_sound, capture_output=True, text=True)
    try:
        j06 = json.load(open(os.path.join(od, "sound.json")))
    except Exception:
        j06 = {}
    res["sound"] = norm_sound(j06, p.returncode)
    res["sound_reason"] = (j06.get("reason") or "")[:300]
    res["sound_s"] = round(time.time() - t, 2)
    t = time.time()
    o1 = os.path.join(od, "oracle")
    p = subprocess.run([oracle, "--from-export", exp_, chal, cfg, o1, "--threads", str(threads)] + extra_oracle,
                       capture_output=True, text=True)
    try:
        j01 = json.load(open(os.path.join(o1, "frontier-result.json")))
    except Exception:
        j01 = {}
    res["oracle"] = norm_oracle(j01, p.returncode)
    res["oracle_reason"] = (j01.get("verdict_basis") or "")[:300]
    res["oracle_s"] = round(time.time() - t, 2)
    if plain:
        t = time.time()
        o5 = os.path.join(od, "plain")
        p = subprocess.run(["python3", "-I", plain, "verify", exp_, chal, cfg, o5, "--threads", str(threads)],
                           capture_output=True, text=True,
                           env=dict(os.environ, FASTVERIFY_ROOT=os.path.join(LL, "fastverify")))
        try:
            j05 = json.load(open(os.path.join(o5, "verdict.json")))
        except Exception:
            j05 = {}
        res["plain"] = norm_plain(j05, p.returncode)
        res["plain_reason"] = (j05.get("why") or p.stderr[-300:] or "")[:300]
        res["plain_s"] = round(time.time() - t, 2)
    return res


def classify(r):
    exp = r["expect"]
    a, b = r["sound"], r["oracle"]
    if "plain" in r:
        c = r["plain"]
        if exp == "REJECTED" and c[0] == "OK":
            return "CRITICAL"
        if c != a and not (exp == "REJECTED" and c[0] in ("REJ", "NOV") and a[0] in ("REJ", "NOV")):
            return "DISAGREE"
    if exp == "REJECTED" and (a[0] == "OK" or b[0] == "OK"):
        return "CRITICAL"
    if exp == "REJECTED" and a[0] in ("REJ", "NOV") and b[0] in ("REJ", "NOV"):
        return "AGREE" if a == b else "AGREE-NONACCEPT"
    if a != b:
        return "DISAGREE"
    if exp == "?":
        return "AGREE"
    want = ("REJ", ()) if exp == "REJECTED" else ("OK", tuple(sorted(x for x in exp[3:].split(",") if x)))
    return "AGREE" if a == want else "UNEXPECTED"


def main(argv):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("cases")
    ap.add_argument("out")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--sound", default=SOUND)
    ap.add_argument("--oracle", default=ORACLE)
    ap.add_argument("--oracle-args", default="--canonical-only")
    ap.add_argument("--sound-args", default="")
    ap.add_argument("--with-plain", action="store_true", help="third judge: the zero-trusted-change frontier.py verify")
    a = ap.parse_args(argv)
    rows = [ln.rstrip("\n").split("\t") for ln in open(a.cases) if ln.strip() and not ln.startswith("#")]
    os.makedirs(a.out, exist_ok=True)
    with ThreadPoolExecutor(a.jobs) as pool:
        results = list(pool.map(lambda r: run_case(r, a.out, a.threads, a.sound, a.oracle, a.sound_args.split(),
                                                   a.oracle_args.split(), PLAIN if a.with_plain else None), rows))
    bad = 0
    with open(os.path.join(a.out, "diff.tsv"), "w") as f:
        for r in results:
            c = classify(r)
            r["class"] = c
            if c in ("CRITICAL", "DISAGREE", "UNEXPECTED"):
                bad += 1
            line = (f"{c}\t{r['id']}\texpect={r['expect']}\tsound={r['sound'][0]}{list(r['sound'][1])}\t"
                    f"oracle={r['oracle'][0]}{list(r['oracle'][1])}\t" + (f"plain={r['plain'][0]}{list(r['plain'][1])}\t" if 'plain' in r else "")
                    + f"{r['sound_s']}s/{r['oracle_s']}s" + (f"/{r['plain_s']}s" if 'plain' in r else ""))
            if c != "AGREE":
                line += f"\tsound: {r['sound_reason']}\toracle: {r['oracle_reason']}" + (f"\tplain: {r.get('plain_reason')}" if 'plain' in r else "")
            print(line)
            f.write(line + "\n")
    json.dump(results, open(os.path.join(a.out, "diff.json"), "w"), indent=1)
    print(f"RESULT {'PASS' if bad == 0 else 'ATTENTION'}: {len(results)} cases, {bad} not AGREE")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

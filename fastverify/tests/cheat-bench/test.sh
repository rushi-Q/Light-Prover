#!/bin/bash
# tests/cheat-bench/test.sh [WORKDIR] [full]   (kind: e2e, all presets; no Mathlib in the quick set)
# Regression test of the proof-cheating benchmark: generates the corpus (gen.py), runs the cases through the official flow
# (--preset reference = official lake build + lean4export + Lean 4.36 lake comparator) and the fast presets, and prints one
# row per case x fast preset:  PASS|FAIL [label] case/preset official=V fast=V reason   (lib/component.sh format).
#   PASS          fast verdict == official verdict
#   FAIL-CRITICAL fast ACCEPTED where the official flow REJECTED (or any ACCEPT on the all-false challenges CHF/CHMF)
#   WARN          other difference (no verdict / false reject: availability)
#   PASS-SOUND-DIFF  documented case (cases.json expected_sound): sound ACCEPTS a valid proof the official BUILD rejects
#                 (T21: flaky first elaboration, retried by the sound build); PASS only if the unmodified official lake
#                 comparator (check/official/check.sh) accepts the very export the sound run checked
# quick (default, 21 cases, ~10-25 min on a loaded host): the cases that fool naive verifiers + controls, presets reference + sound;
# full: every case x reference/sound (~25 min on 64 threads; F24/F32 stall their builds on purpose; earlier the
# full set also ran the presets fast-exact and default, retired with check A).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/cheat-bench.XXXXXX")}; MODE=${2:-quick}
rm -rf "$W"; mkdir -p "$W"
export FV_UNDER_TEST=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
if [ "$MODE" = full ]; then
  "$H/run.sh" "$W" 8 8 'reference sound' > "$W/run.log" 2>&1
else
  "$H/run.sh" "$W" 6 ${EVAL_THREADS:-4} 'reference sound' \
    'F01* F04* F09* F12* F14* F17* F22* F25* F27* F30* F34* B01* B02* F35* F36* T00* T03* T09* T15* T21* T22*' > "$W/run.log" 2>&1
fi
FV=$FV_UNDER_TEST
python3 -I - "$W/summary.tsv" "$W/corpus/cases.json" "$W" "$FV" <<'PY'
import csv, json, sys
rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
cases = json.load(open(sys.argv[2]))
by = {}
for r in rows:
    by.setdefault(r["case"], {})[r["preset"]] = r
fails = 0
for c in sorted(by):
    ref = by[c].get("reference")
    for p, r in sorted(by[c].items()):
        if p == "reference":
            continue
        ov = ref["verdict"] if ref else "NONE"
        fv = r["verdict"]
        if (p == "sound" and fv == "ACCEPTED" and ov == "REJECTED" and cases[c].get("expected_sound") == "ACCEPTED"
                and cases[c]["challenge"] not in ("CHF", "CHMF")):
            # documented sound-but-different case (e.g. T21: the official build fails, the proof is valid): the accept is
            # only allowed if the UNMODIFIED official lake comparator accepts the very export the sound run checked
            run = json.load(open("%s/runs/%s.%s/result.json" % (sys.argv[3], c, p)))
            exp = (run.get("export") or {}).get("path")
            chx = "%s/runs/%s.%s/challenge.export" % (sys.argv[3], c, p)
            cfg = "%s/corpus/challenges/%s/comparator.json" % (sys.argv[3], cases[c]["challenge"])
            import subprocess
            rc = subprocess.run([sys.argv[4] + "/check/official/check.sh", exp or "/nonexistent", chx, cfg],
                                capture_output=True).returncode if exp else 99
            res = "PASS-SOUND-DIFF" if rc == 0 else "FAIL-CRITICAL"
            fails += res.startswith("FAIL")
            print("%s %s/%s official=%s fast=%s official lake comparator on the sound export: exit %s" % (
                "PASS [sound-only accept of a valid proof]" if res == "PASS-SOUND-DIFF" else "FAIL [CRITICAL]", c, p, ov, fv, rc))
            continue
        if fv == "ACCEPTED" and (ov != "ACCEPTED" or cases[c]["challenge"] in ("CHF", "CHMF")):
            res = "FAIL-CRITICAL"; fails += 1
        elif fv == ov:
            res = "PASS"
        else:
            res = "WARN"
        lab = {"PASS": "PASS", "WARN": "PASS [WARN availability: no verdict or false reject]", "FAIL-CRITICAL": "FAIL [CRITICAL]"}[res]
        print("%s %s/%s official=%s fast=%s %s" % (lab, c, p, ov, fv, " ".join(r["reason"].split())[:120]))
    if ref and cases[c]["challenge"] in ("CHF", "CHMF") and ref["verdict"] == "ACCEPTED":
        print("FAIL [CRITICAL] %s/reference the OFFICIAL flow accepted a false statement" % c); fails += 1
print("RESULT: %s (%d rows)" % ("PASS" if fails == 0 else "FAIL", sum(len(v) - 1 for v in by.values())))
sys.exit(1 if fails else 0)
PY

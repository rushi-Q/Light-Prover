#!/usr/bin/python3 -I
"""stages.py RUNDIR... : one line per run: verdict, trust, stage seconds, challenge build seconds, export size."""
import json, sys, os
for d in sys.argv[1:]:
    try:
        r = json.load(open(os.path.join(d, "result.json")))
    except Exception as e:
        print(os.path.basename(d), "NO RESULT", e); continue
    ss = r.get("stage_seconds", {})
    ce = (r.get("inputs") or {}).get("challenge_export") or {}
    ex = r.get("export") or {}
    ch = r.get("checks") or {}
    cks = " ".join(f"{k}:{v.get('verdict')}/{v.get('seconds')}" for k, v in ch.items())
    print(os.path.basename(d), r.get("verdict"), r.get("trust"), json.dumps(ss), "chal=%s" % ce.get("seconds"),
          "exp=%s/%s" % (ex.get("option"), ex.get("size")), "build=%s/%s" % ((r.get("build") or {}).get("option"),
          (r.get("build") or {}).get("seconds")), cks)

#!/usr/bin/python3 -I
"""audit_result.py RESULT.json [PINS.env] : audit a sound-mode result.json: verdict/trust/exit, challenge pin, the check
binaries recorded vs the tested pins (PINS.env, default the package's check/sound/pins.env), basis, export, warnings."""
import json, os, sys
r = json.load(open(sys.argv[1]))
pins = sys.argv[2] if len(sys.argv) > 2 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../check/sound/pins.env")
want = {}
for ln in open(pins):
    q = ln.split()
    if len(q) == 4 and q[0] == "PIN":
        want[q[1]] = q[2]
ok = True
def chk(c, msg):
    global ok
    print(("OK   " if c else "FAIL ") + msg)
    ok = ok and c
chk(r.get("verdict") == "ACCEPTED" and r.get("exit") == 0, f"verdict {r.get('verdict')} exit {r.get('exit')}")
chk(r.get("trust") == "sound", f"trust {r.get('trust')}")
s = r.get("soundness") or {}
ce = (s.get("trusted") or {}).get("challenge_export") or {}
chk(ce.get("pin_ok") is True and ce.get("sha256") == "3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d",
    f"challenge export {str(ce.get('sha256'))[:16]} pinned={str(ce.get('pinned_sha256'))[:16]} pin_ok={ce.get('pin_ok')}")
bins = ((s.get("trusted") or {}).get("check") or {}).get("binaries_sha256") or {}
for k, v in bins.items():
    chk(want.get(k) == v, f"binary {k} {v[:16]} {'= pinned' if want.get(k) == v else '!= pinned ' + str(want.get(k))[:16]}")
for k in ("ccmp", "pleanchecker", "gruszka"):
    chk(k in bins, f"binary {k} recorded")
cs = (r.get("checks") or {}).get("sound") or {}
chk(cs.get("verdict") == "ACCEPTED", f"CS verdict {cs.get('verdict')} ({cs.get('seconds')} s)")
e = r.get("export") or {}
print(f"INFO export {e.get('option')} {str(e.get('sha256'))[:16]} size {e.get('size')} identical_to_reference={(e.get('reference') or {}).get('identical')}")
print(f"INFO build {(r.get('build') or {}).get('option')} transforms {(r.get('mode') or {}).get('unsafe')}")
print(f"INFO overlap mode {(r.get('overlap') or {}).get('mode')}")
print(f"INFO stage_seconds {r.get('stage_seconds')}")
print(f"INFO started {r.get('started')} finished {r.get('finished')}")
chk(not r.get("warnings"), f"warnings {r.get('warnings')}")
print("AUDIT", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)

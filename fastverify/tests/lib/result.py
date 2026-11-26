#!/usr/bin/env python3
"""result.py RESULT_JSON OUTDIR LINK_EXPORT FASTVERIFY_RC SECONDS
Reads the package's result.json (tolerant to small schema differences), prints the harness lines
    fast: stage <name> exit <n> ...
    fast: export <size> bytes sha256 <first 16 hex>
    FAST: ACCEPTED|REJECTED (...)
hard-links the package export to LINK_EXPORT (for repros that inspect WORK/run/solution.export).
Exit: 0 ACCEPTED (final verdict or fast-check verdict), 1 REJECTED, 2 DECLINED, 4 ERROR (refused / no verdict)."""
import hashlib, json, os, sys

res_path, outdir, link, fvrc, secs = sys.argv[1:6]
try:
    r = json.load(open(res_path))
except Exception as e:  # unreadable result = no verdict = not accepted
    print(f"FAST: REJECTED (unreadable result.json: {e})"); sys.exit(1)


def get(d, *keys):
    for k in keys:
        if isinstance(d, dict) and k in d:
            return d[k]
    return None


# per-stage / per-check summary lines
for sect in ("build", "export"):
    s = get(r, sect, sect + "_stage")
    if isinstance(s, dict):
        ex = get(s, "exit", "rc", "status", "verdict")
        how = get(s, "path", "mode", "impl", "fallback", "declined")
        print(f"fast: stage {sect} exit {ex}" + (f" ({how})" if how is not None else ""))
checks = get(r, "checks") or {}
if isinstance(checks, dict):
    for name, c in checks.items():
        if isinstance(c, dict):
            print(f"fast: check {name} exit {get(c, 'exit', 'rc')} verdict {get(c, 'verdict', 'status')}")
        else:
            print(f"fast: check {name} {c}")

# export: sha from result.json, else hash the file the package names / wrote
exp = get(r, "export") or {}
epath = None
if isinstance(exp, dict):
    epath = get(exp, "path", "file", "export")
if not epath or not os.path.isfile(str(epath)):
    for cand in ("solution.export", "export/solution.export", "run/solution.export"):
        if os.path.isfile(os.path.join(outdir, cand)):
            epath = os.path.join(outdir, cand); break
if epath and not os.path.isabs(str(epath)):
    epath = os.path.join(outdir, epath)
sha = get(exp, "sha256") if isinstance(exp, dict) else None
if epath and os.path.isfile(epath):
    if not sha:
        h = hashlib.sha256()
        with open(epath, "rb") as f:
            for b in iter(lambda: f.read(1 << 24), b""):
                h.update(b)
        sha = h.hexdigest()
    os.makedirs(os.path.dirname(link), exist_ok=True)
    try:
        if os.path.lexists(link):
            os.unlink(link)
        os.link(epath, link)
    except OSError:
        try:
            import shutil; shutil.copyfile(epath, link)
        except OSError:
            pass
    print(f"fast: export {os.path.getsize(epath)} bytes sha256 {sha[:16]}")
elif sha:
    print(f"fast: export {get(exp, 'size', 'bytes')} bytes sha256 {str(sha)[:16]}")

# which path the package took (speed coverage): build mode, export tool, fast-check verdicts
bm = (get(r, "build") or {}).get("mode") if isinstance(get(r, "build"), dict) else None
em = (get(r, "export") or {}).get("mode") if isinstance(get(r, "export"), dict) else None
fc = ",".join(f"{k}={(c or {}).get('verdict')}" for k, c in (checks.items() if isinstance(checks, dict) else []) if k != "official")
bo = (get(r, "build") or {}).get("option") if isinstance(get(r, "build"), dict) else None
tr = get(r, "trust")
print(f"fast: path build={bo or bm or '-'} export={em or '-'} {fc}" + (f" trust={tr}" if tr else ""))
if r.get("agreement") is False:   # a fast check disagrees with the official verdict (e.g. false reject by C1)
    print("fast: disagreement: fast checks " + str(r.get("verdict_fast")) + " vs official " + str(r.get("verdict_official")))
v = str(get(r, "verdict", "final_verdict", "result") or "").upper()
vf = str(get(r, "verdict_fast") or "").upper()
vo = str(get(r, "verdict_official") or "").upper()
why = get(r, "verdict_basis", "reason", "message", "detail")
tag = f"verdict={v or 'none'} fast={vf or '-'} official={vo or '-'}; fastverify rc={fvrc}, {secs} s" + (f"; {why}" if why else "")
# The FAST outcome reported to the test: ACCEPTED if the package's final verdict OR its (unofficial) fast-check verdict
# accepts (an accept by the fast checks alone must already be correct); DECLINED -> 2; ERROR/refusal -> 4; else REJECTED.
if v.startswith("ACCEPT") or vf.startswith("ACCEPT"):
    print(f"FAST: ACCEPTED ({tag})"); sys.exit(0)
if v.startswith("DECLINE"):
    print(f"FAST: DECLINED ({tag})"); sys.exit(2)
if v.startswith("ERROR") or not v:
    print(f"FAST: ERROR ({tag})"); sys.exit(4)
print(f"FAST: REJECTED ({tag})"); sys.exit(1)

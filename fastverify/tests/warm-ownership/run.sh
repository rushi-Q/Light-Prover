#!/bin/bash
# tests/warm-ownership/run.sh [WORKDIR] -- regression test: warm-check ownership exports never credit an empty attempt (CRITICAL,
# tools/fvserve/fvserve.py --warm-check + tools/batchverify.py confirm_ownership): under --warm-check the ownership export
# of confirm_ownership ('own-<t>') went to the delta exporter, which exits 0 with a meta-only file for an attempt that does
# not declare t; an EMPTY attempt batched with an attempt proving its theorem was credited ACCEPTED (reward 1.0, trust
# sound) while the cold service REJECTS it. Reproduction inputs
# copied to data/ (SHA256SUMS).
# Rows:
#   unit/declares-*: batchverify.export_declares_theorem (fail-closed content check of an ownership export)
#   unit/confirm-ownership-*: Batch.verdicts with an exporter that exits 0 with a meta-only / theorem-less export -> the
#     attempt is REJECTED ('not declared by its own attempt'), never ACCEPTED; a real theorem record -> ACCEPTED
#   unit/fastbatch-own-not-delta: FastBatch.export never routes an 'own-' export to delta_export under --warm-check
#   e2e/{warm,cold}/*: the reproduction (official Lean 4.33.1 problem set, attempt A proves thmA + thmB, attempt B is a
#     comment only) on fvserve --warm-check and on the cold service: B is REJECTED on both (batched with A: batch_size 2),
#     A ACCEPTED on both, the fv-verdict-v1 envelope of B has accepted=false reward=0.0; e2e/pos-*: A only MENTIONS thmB,
#     B proves it -> ownership confirmed by B's real export, B ACCEPTED on both (service state under a short /tmp path). Needs the official 4.33.1 toolchain
#     (TC33), the warm binaries (WARM_BINS, default /scratch/fastverify-next/warm/v1); else the e2e rows SKIP.
# Untrusted attempts are compiled only inside fvserve's bwrap sandbox (no network). Exit 0 iff every row PASS.
# FV_ROOT=<package> runs the rows against another package copy (the test data stays here).
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FV_ROOT:-$(cd "$HERE/../.." && pwd)}
TC33=${TC33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
WARM_BINS=${WARM_BINS:-/scratch/fastverify-next/warm/v1}
base=${1:-${TMPDIR:-/tmp}}
W=$(mktemp -d "$base/warm-ownership.XXXXXX") || exit 2
S=$(mktemp -d /tmp/z37s.XXXXXX) || exit 2   # service state dirs: short paths (AF_UNIX socket path limit)
(cd "$HERE/data" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data: SHA256SUMS mismatch"; echo "RESULT pass=0 fail=1"; exit 1; }
cp -a "$HERE/data/pset" "$HERE/data/attA.lean" "$HERE/data/attB_empty.lean" "$W/"
chmod -R u+w "$W"
PIDS=()
cleanup() {
  for st in "$S/warm" "$S/cold"; do
    [ -S "$st/sock" ] && python3 -I -B "$FV/tools/fvserve/fvserve.py" stop --state "$st" > /dev/null 2>&1
  done
  for p in "${PIDS[@]}"; do kill "$p" 2>/dev/null; wait "$p" 2>/dev/null; done
  rm -rf "$W" "$S"
}
trap cleanup EXIT

python3 -I -B - "$FV" "$W" <<'PY'
import json, os, sys, tempfile, types
sys.dont_write_bytecode = True
fv, w = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(fv, "tools"))
sys.path.insert(0, os.path.join(fv, "tools", "fvserve"))
import batchverify as bv
P = F = 0
def row(ok, name, msg):
    global P, F
    print(("PASS " if ok else "FAIL ") + name + ": " + msg)
    if ok:
        P += 1
    else:
        F += 1

META = '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"x","version":"4.33.1"}}}\n'
def mk(name, body):
    p = os.path.join(w, name)
    open(p, "w").write(body)
    return p
cases = {
    "meta-only": (META, False),
    "empty": ("", False),
    "theorem": (META + '{"in":1,"str":{"pre":0,"str":"thmB"}}\n{"ie":0,"sort":0}\n'
                '{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":0}}\n', True),
    "def-not-theorem": (META + '{"in":1,"str":{"pre":0,"str":"thmB"}}\n'
                        '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":0}}\n', False),
    "namespaced": (META + '{"in":1,"str":{"pre":0,"str":"Foo"}}\n{"in":2,"str":{"pre":1,"str":"thmB"}}\n'
                   '{"thm":{"all":[2],"levelParams":[],"name":2,"type":0,"value":0}}\n', False),
    "other-theorem": (META + '{"in":1,"str":{"pre":0,"str":"thmB"}}\n{"in":2,"str":{"pre":0,"str":"thmC"}}\n'
                      '{"thm":{"all":[2],"levelParams":[],"name":2,"type":0,"value":0}}\n', False),
    "prefix-name": (META + '{"in":1,"str":{"pre":0,"str":"thmBx"}}\n'
                    '{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":0}}\n', False),
    "index-12-vs-1": (META + '{"in":1,"str":{"pre":0,"str":"thmB"}}\n'
                      '{"thm":{"all":[12],"levelParams":[],"name":12,"type":0,"value":0}}\n', False),
    "use-before-def": (META + '{"thm":{"all":[1],"levelParams":[],"name":1,"type":0,"value":0}}\n'
                       '{"in":1,"str":{"pre":0,"str":"thmB"}}\n', False),
    "spaced-json": (META + '{ "in":1, "str":{"pre":0,"str":"thmB"}}\n{ "thm":{"name":1}}\n', False),
}
fn = getattr(bv, "export_declares_theorem", None)
if fn is None:
    row(False, "unit/declares", "batchverify has no fail-closed ownership content check (export_declares_theorem)")
else:
    for k, (body, want) in cases.items():
        got = fn(mk("x-" + k + ".ndjson", body), "thmB")
        row(got is want, "unit/declares-" + k, "export_declares_theorem -> %s (want %s)" % (got, want))
    # an unreadable / missing ownership export is NOT "absent": None -> no verdict.
    # Safety assertion kept: never True (never credits the theorem)
    got = fn(os.path.join(w, "no-such-file"), "thmB")
    row(got is None, "unit/declares-missing-file", "unreadable -> %s (want None: no verdict, never True)" % got)

# confirm_ownership / verdicts with a fake exporter (the bug: exporter exit 0, meta-only file)
def fake_batch(export_body, t_in_other=True):
    b = object.__new__(bv.Batch)
    b.a = types.SimpleNamespace(par=2)
    b.res = {"checks": [{"exit": 0, "theorems": ["thmA", "thmB"], "tag": "r0"}],
             "attempts": {"thmA": {}, "thmB": {}}}
    b.olean_bytes = lambda n: (b"..thmA\x00..thmB\x00.." if n == "thmA" and t_in_other else b"")
    # the installed Batch locates the attempt objects under self.lib (olean_path):
    # give the fake batch its own lib with Attempt/thmA.olean (also names thmB) and an empty Attempt/thmB.olean
    b.lib = tempfile.mkdtemp(prefix="z037-lib.", dir=w)
    os.makedirs(os.path.join(b.lib, "Attempt"))
    open(os.path.join(b.lib, "Attempt", "thmA.olean"), "wb").write(b"..thmA\x00..thmB\x00.." if t_in_other else b"")
    open(os.path.join(b.lib, "Attempt", "thmB.olean"), "wb").write(b"")
    def export(root, names, tag, threads=None):
        if export_body is None:
            return None, "PANIC at dumpConstant: Constant thmB not found in environment."
        return mk("own-%s-%d.ndjson" % (names[0], len(export_body)), export_body), ""
    b.export = export
    return b
# an exporter that DECLINES (here: lean4export's panic) is no verdict (only a
# successful export without the theorem record, or the native exporter's structured 'target constant <t> not found in
# environment (declining)', rejects); fail-closed: never ACCEPTED, NO-VERDICT counts like REJECTED for rewards
for label, body, want in (("meta-only-export", META, "REJECTED"), ("theorem-less-export", cases["other-theorem"][0], "REJECTED"),
                          ("exporter-panics", None, "NO-VERDICT"), ("real-theorem-record", cases["theorem"][0], "ACCEPTED")):
    b = fake_batch(body)
    try:
        b.verdicts()
        vb, va = b.res["attempts"]["thmB"].get("verdict"), b.res["attempts"]["thmA"].get("verdict")
        row(vb == want and va == "ACCEPTED", "unit/confirm-ownership-" + label,
            "thmB %s (want %s), thmA %s: %s" % (vb, want, va, (b.res["attempts"]["thmB"].get("why") or "")[:90]))
    except Exception as e:  # noqa: BLE001
        row(False, "unit/confirm-ownership-" + label, "exception %r" % e)

# FastBatch.export under --warm-check: an 'own-' export must not use the delta exporter
try:
    import fvserve
    FB = fvserve.make_fastbatch(bv)
    calls = []
    class Svc:
        warm_check = True
        fast_export = True
        def delta_export(self, batch, root, names, tag, exclude=None, threads=None):
            calls.append(("delta", tag))
            p = mk("dx-" + tag + ".ndjson", META)
            return p, "", os.path.getsize(p), ["Attempt." + n for n in names]
        def native_export(self, batch, root, names, tag, threads):
            calls.append(("native", tag))
            return None   # -> export.sh fallback (stubbed below)
        def log(self, **k):
            pass
    fb = object.__new__(FB)
    fb.svc = Svc()
    import threading, time as _t
    fb.lock = threading.Lock(); fb.events = []; fb.t0 = _t.time(); fb.res = {"exports": []}
    def super_export(self, root, names, tag, threads=None):
        calls.append(("export.sh", tag))
        self.res["exports"].append({"tag": tag})
        return None, "PANIC at dumpConstant: Constant thmB not found"
    bv.Batch.export = super_export
    out, why = fb.export(None, ["thmB"], "own-thmB", 4)
    used = [c[0] for c in calls if c[1] == "own-thmB"]
    row("delta" not in used and out is None, "unit/fastbatch-own-not-delta",
        "own-thmB export paths %s, result %s" % (used, "None (not owned)" if out is None else out))
    calls.clear()
    fb.export(None, ["thmA", "thmB"], "r0", 4)
    row([c[0] for c in calls] == ["delta"], "unit/fastbatch-set-still-delta", "set export r0 paths %s (warm path kept)" % [c[0] for c in calls])
except Exception as e:  # noqa: BLE001
    row(False, "unit/fastbatch-own-not-delta", "exception %r" % e)
open(os.path.join(w, "unit.count"), "w").write("%d %d\n" % (P, F))
PY
read up uf < "$W/unit.count" 2>/dev/null || { up=0; uf=1; }
pass=$up; fail=$uf
ok() { echo "PASS $1: $2"; pass=$((pass+1)); }
ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }

# ---------------- e2e: the reproduction on the warm and the cold service ----------------
if [ ! -x "$TC33/bin/lean" ] || [ ! -x "$WARM_BINS/lean4export-delta" ] || [ ! -x /usr/bin/bwrap ]; then
  echo "SKIP e2e: needs the official 4.33.1 toolchain ($TC33), $WARM_BINS/lean4export-delta and bwrap"
elif grep -Eq -- "--warm-check is (disabled|not available)" "$FV/tools/fvserve/fvserve.py"; then
  # the package's interim guard (fvserve.py) refuses --warm-check: the
  # warm/cold e2e cannot start a warm service; it is skipped with the reason, and the guard itself is checked instead
  echo "SKIP e2e/warm-service-start: fvserve --warm-check is disabled by the package's interim guard (experimental warm mode)"
  mkdir -p "$S/warm"
  timeout 60 python3 -I -B "$FV/tools/fvserve/fvserve.py" serve --state "$S/warm" --pset "demo=$W/pset:0000000000000000000000000000000000000000000000000000000000000000" \
    --packages "$W" --toolchain "$TC33" --fv "$FV" --export-dir "$W" --warm-check > "$W/warm-guard.log" 2>&1; grc=$?
  if [ "$grc" != 0 ] && grep -q -- "--warm-check" "$W/warm-guard.log" && grep -Eq "not available|disabled" "$W/warm-guard.log" && [ ! -S "$S/warm/sock" ]; then
    ok e2e/warm-check-guard-refuses "exit $grc, no warm service started"
  else
    ko e2e/warm-check-guard-refuses "exit $grc: $(tail -c 200 "$W/warm-guard.log")"
  fi
else
  mkdir -p "$W/ws/.lake/packages" "$S/warm" "$S/cold"
  CSHA=$(sha256sum "$W/pset/challenge.export" | cut -d' ' -f1)
  python3 -I -B "$FV/tools/fvserve/fvserve.py" serve --state "$S/warm" --pset "demo=$W/pset:$CSHA" --packages "$W/ws" \
    --toolchain "$TC33" --fv "$FV" --threads 4 --max-batch 8 --linger 1.0 --snapshot-header "" --warm-check \
    --warm-bins "$WARM_BINS" > "$W/warm.log" 2>&1 &
  PIDS+=($!)
  python3 -I -B "$FV/tools/fvserve/fvserve.py" serve --state "$S/cold" --pset "demo=$W/pset:$CSHA" --packages "$W/ws" \
    --toolchain "$TC33" --fv "$FV" --threads 4 --max-batch 8 --linger 1.0 --snapshot-header "" > "$W/cold.log" 2>&1 &
  PIDS+=($!)
  for i in $(seq 1 900); do [ -S "$S/warm/sock" ] && [ -S "$S/cold/sock" ] && break; sleep 0.2; done
  if [ ! -S "$S/warm/sock" ] || [ ! -S "$S/cold/sock" ]; then
    ko e2e/start "service did not start: $(tail -c 300 "$W/warm.log" | tr '\n' ' ') | $(tail -c 300 "$W/cold.log" | tr '\n' ' ')"
  else
    python3 -I -B - "$FV" "$W" "$S" > "$W/e2e.out" 2>&1 <<'PY'
import concurrent.futures as cf, json, os, sys
sys.dont_write_bytecode = True
fv, w, sdir = sys.argv[1], sys.argv[2], sys.argv[3]
sys.path.insert(0, os.path.join(fv, "tools", "fvserve")); sys.path.insert(0, os.path.join(fv, "schemas"))
import fvserve, fv_schema
srcA = open(os.path.join(w, "attA.lean")).read(); srcB = open(os.path.join(w, "attB_empty.lean")).read()
# positive control: A merely MENTIONS thmB (its .olean holds 'thmB\0'), B proves thmB itself -> ownership must
# be confirmed by B's own export (real exporter output) and B ACCEPTED, on both services
srcA2 = "theorem thmA : True := trivial\ndef noteB : String := \"thmB\"\n"
srcB2 = "theorem thmB : 2 + 2 = 4 := rfl\n"
for label, st in (("warm", os.path.join(sdir, "warm")), ("cold", os.path.join(sdir, "cold"))):
    def send(thm, src):
        return fvserve.request(st, {"op": "verify", "pset": "demo", "theorem": thm, "source": src}, timeout=300)
    for case, a, b in (("", srcA, srcB), ("pos-", srcA2, srcB2)):
        for attempt in range(4):
            with cf.ThreadPoolExecutor(2) as ex:
                fA = ex.submit(send, "thmA", a); fB = ex.submit(send, "thmB", b)
                rA, rB = fA.result(), fB.result()
            if rB.get("batch_size") == 2 or rB.get("early"):
                break
        env = fv_schema.from_fvserve_result(rB, pset="demo", theorem="thmB", include_raw=False)
        print(json.dumps({"label": case + label, "A": rA.get("verdict"), "B": rB.get("verdict"), "B_why": rB.get("why"),
                          "B_batch_size": rB.get("batch_size"), "B_early": bool(rB.get("early")),
                          "env": {k: env[k] for k in ("verdict", "accepted", "reward", "trust", "exit_code")}}))
PY
    while read -r ln; do
      r=$(python3 -I -c '
import json, sys
j = json.loads(sys.argv[1]); L = j["label"]; e = j["env"]
rows = []
batched = j["B_batch_size"] == 2
rows.append((batched, L + "/batched", "B in a batch of %s with A%s" % (j["B_batch_size"], " (B answered early)" if j["B_early"] else "")))
if L.startswith("pos-"):
    rows.append((j["B"] == "ACCEPTED" and "alone exports thmB" in str(j["B_why"]), L + "/owner-confirmed-by-real-export",
                 "B %s: %s" % (j["B"], str(j["B_why"])[:110])))
    rows.append((e["accepted"] is True and e["reward"] == 1.0, L + "/envelope", "fv-verdict-v1 of B %s" % e))
else:
    rows.append((j["B"] == "REJECTED", L + "/empty-attempt-not-credited", "B %s (want REJECTED): %s" % (j["B"], str(j["B_why"])[:110])))
    rows.append((e["accepted"] is False and e["reward"] == 0.0, L + "/envelope", "fv-verdict-v1 of B %s" % e))
rows.append((j["A"] == "ACCEPTED", L + "/honest-attempt", "A %s (want ACCEPTED)" % j["A"]))
for okk, n, m in rows:
    print(("PASS " if okk else "FAIL ") + "e2e/" + n + ": " + m)' "$ln" 2>&1) || r="FAIL e2e/parse: $ln"
      while read -r rr; do case "$rr" in PASS*) ok "$(echo "${rr#PASS }" | cut -d: -f1)" "$(echo "$rr" | cut -d: -f2-)";;
        *) ko "$(echo "${rr#FAIL }" | cut -d: -f1)" "$(echo "$rr" | cut -d: -f2-)";; esac; done <<< "$r"
    done < <(grep '^{' "$W/e2e.out")
    grep -q '^{' "$W/e2e.out" || ko e2e/requests "$(tail -c 400 "$W/e2e.out" | tr '\n' ' ')"
  fi
fi
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]

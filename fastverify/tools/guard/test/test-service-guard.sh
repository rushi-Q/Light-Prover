#!/bin/bash
# test-service-guard.sh [WORK] : tools/batchverify.py and tools/fvserve under per-attempt resource limits (tools/guard).
# A 16-problem Mathlib problem set (the official flow on the positive batch yields the official challenge export), then
# 6 BOUNDED resource probes (mkprobes.py: 4 GB heap, 1 GB into the sandbox /tmp, 100 MB of messages, 100 child processes,
# 300 threads, a 90 s busy loop - each an honest proof that would be ACCEPTED without limits) + 10 honest attempts:
#   1. batchverify --limits (official lean per attempt): every probe NO-VERDICT (resource limit / timeout), every honest
#      attempt ACCEPTED (no false NO-VERDICT from the limits)
#   2. fvserve --fork-server --limits: the same per-attempt expectations through the fork-server path, sequentially; the
#      service is still alive and verifies honest attempts afterwards; a timed-out / killed fork child is gone
#   3. fvserve --max-pending 2 --max-inflight 1: a burst of honest attempts gets ACCEPTED or an immediate NO-VERDICT
#      'queue full', never REJECTED
#   4. fvserve --request-timeout 1: a client that never ends its request line is dropped; the service still answers
#   5. fvserve --max-inflight 1 --slow-after 3: an honest attempt submitted behind a runaway one (90 s loop, timeout 30 s)
#      is answered ACCEPTED long before the runaway one's NO-VERDICT (slow lane: no head-of-line blocking)
#   6. fork server killed: the next attempt is still verified (official lean), the worker is restarted and used again
#   7. a SIGKILLed service leaves its private export dir; the next service with the same parent removes it (tagged only)
#   8. --fair: client B's attempt submitted just after a 6-attempt burst of client A is not answered last;
#      --max-pending-per-client 2: part of A's burst gets 'queue full for this client' at once, B is still served
#   9. --linger 2 + a client that disconnects while its attempt lingers -> the next request is still answered
#  10. unit (no Lean): test-dispatch-error.py - an exception in take_batch is logged, the dispatcher survives, no deadlock
#  11. --no-fast-export (batchverify's export path) + every case submitted twice concurrently -> every verdict as the official flow's
#  12. 'stats' reports the code the service runs (sha256 at start) and lists files changed on disk since (restart needed);
#      the service runs with --profile laptop (recorded in the ready line)
# PASS iff all hold. Every probe is an honest proof, so an ACCEPTED is never unsound: it means the resource was not contained.
# Env: EVAL_THREADS (default 16), FV_PACKAGES (trusted workspace, node-local copy recommended; default
#   <repository root>/verify/challenge), TC433 (official 4.33.1), FV_SCRATCH (parent of the default WORK).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)               # tools/guard
FASTVERIFY=${FASTVERIFY:-$(cd "$H/../.." && pwd)}; LIGHT_LEAN=${LIGHT_LEAN:-$(dirname "$FASTVERIFY")}
WS=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}
TC=${TC433:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
TP=$FASTVERIFY/bench/throughput
W=${1:-${FV_SCRATCH:?node-local work directory outside /tmp, /home, /var and /run (required unless WORK is given)}/$USER-service-guard-test}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-16}
LIM='mem=1200M,nproc=256,procs=32,threads=128,out=16M,disk=64M,fsize=64M,cpu=120'
ATO=30
NAMES=nt_prime_1009,lia_chicken,ineq_amgm2,rfl_nat_mul,an_pi_gt3,dec_zmod,lia_two_consec,alg_diff_squares,nt_sqrt2_irr,amc_sum_1_to_100,lia_div3,lia_bound,lia_ages,lia_floor_div,lia_system,lia_mod_comb
bad=0
ok() { echo "PASS $*"; }
no() { echo "FAIL $*"; bad=1; }
python3 -I "$TP/corpus/gen.py" "$W/corpus" --names "$NAMES" > /dev/null || { echo "FAIL gen.py"; echo "RESULT FAIL"; exit 1; }
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FASTVERIFY/bin/fastverify" "$W/corpus/projects/BATCH" \
    "$W/corpus/challenges/BATCH" "$W/ref" --preset reference --threads "$T" --packages "$WS" > "$W/ref.log" 2>&1
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/ref/result.json" 2>/dev/null)
[ "$v" = ACCEPTED ] && ok "official flow on the positive batch: ACCEPTED" || { no "official flow on the positive batch: $v"; echo "RESULT FAIL"; exit 1; }
mkdir -p "$W/pset" && cp "$W/ref/challenge.export" "$W/corpus/challenges/BATCH/comparator.json" "$W/pset/"
SHA=$(sha256sum "$W/pset/challenge.export" | cut -d' ' -f1)
python3 -I "$H/test/mkprobes.py" "$W/corpus" "$W/att" > /dev/null || { no "mkprobes"; echo "RESULT FAIL"; exit 1; }
judge() {  # judge LABEL VERDICTS_JSON(theorem -> [verdict, why]) : probes NO-VERDICT, honest ACCEPTED
  python3 -I - "$1" "$2" "$W/att/expect.json" <<'PY'
import json, re, sys
lab, got, exp = sys.argv[1], json.load(open(sys.argv[2])), json.load(open(sys.argv[3]))
bad = 0
for t, e in sorted(exp.items()):
    v, why = got.get(t, ["MISSING", ""])
    if e["probe"] is None:
        good = v == "ACCEPTED"
    else:   # contained: a limit ended it (NO-VERDICT), or the sandbox refused the resource (fork path: Landlock denies
            # writes outside the child's output dir -> the probe's #eval fails -> REJECTED with a permission error)
        good = (v == "NO-VERDICT" and ("resource limit" in why or "timeout" in why)) or \
               (v == "REJECTED" and e["probe"] == "tmpfs" and lab == "fvserve" and re.search(r"ermission|denied|EACCES|read-only", why) is not None)
    if good:
        print(f"PASS {lab} {t} ({e['probe'] or 'honest'}): {v} {why[:110]}")
    else:
        crit = ""   # every probe is an honest proof: an ACCEPTED is sound, but it means the resource was not contained
        print(f"FAIL{crit} {lab} {t} ({e['probe'] or 'honest'}): {v} {why[:200]}")
        bad = 1
sys.exit(bad)
PY
}
# ---- 1. batchverify with limits (official lean per attempt)
mkdir -p "$W/att-bv" && cp "$W"/att/*.lean "$W/att-bv/"
python3 -I "$FASTVERIFY/tools/batchverify.py" --pset "$W/pset" --attempts "$W/att-bv" --out "$W/bv" --challenge-sha256 "$SHA" \
  --threads "$T" --packages "$WS" --toolchain "$TC" --snapshot-cache "$W/snap" --attempt-timeout $ATO --limits "$LIM" > "$W/bv.log" 2>&1
python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); json.dump({t: [a.get("verdict"), a.get("why","")] for t,a in r["attempts"].items()}, open(sys.argv[2],"w"))' \
  "$W/bv/batch.json" "$W/bv.verdicts.json" 2>/dev/null || echo '{}' > "$W/bv.verdicts.json"
judge batchverify "$W/bv.verdicts.json" || bad=1
# ---- 2. fvserve with the fork server and limits
FK=(); if bash "$FASTVERIFY/tools/fvserve/fork/build.sh" "$TC" "$W/fvfork" > "$W/fvfork-build.log" 2>&1; then FK=(--fork-server "$W/fvfork/fvfork"); else echo "NOTE fvfork not built here: testing the official-lean compile path only"; fi
start() {  # start STATE [args...]
  local st=$1; shift
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" serve --state "$st" --pset "t=$W/pset:$SHA" --threads "$T" --packages "$WS" \
    --toolchain "$TC" --fv "$FASTVERIFY" --svc-check "$@" > "$st.log" 2>&1 &
  for i in $(seq 1 300); do grep -q '"ready"' "$st.log" 2>/dev/null && return 0; kill -0 $! 2>/dev/null || return 1; sleep 1; done
  return 1
}
S=$W/svc
if start "$S" "${FK[@]}" --limits "$LIM" --attempt-timeout $ATO; then
  ok "service with limits ready"
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S" "$W/att" "$W/svc.verdicts.json" <<'PY'
import json, os, sys
sys.path.insert(0, sys.argv[1]); import fvserve
st, att, out = sys.argv[2], sys.argv[3], sys.argv[4]
got = {}
for f in sorted(os.listdir(att)):
    if f.endswith(".lean"):
        t = f[:-5]
        r = fvserve.request(st, {"op": "verify", "pset": "t", "theorem": t, "source": open(os.path.join(att, f)).read()})
        got[t] = [r.get("verdict"), r.get("why", "")]
json.dump(got, open(out, "w"))
PY
  judge fvserve "$W/svc.verdicts.json" || bad=1
  st=$(python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stats --state "$S")
  echo "$st" | grep -q '"uptime_s"' && ok "service alive after the probes: $(echo "$st" | python3 -I -c 'import json,sys; d=json.load(sys.stdin); print(d["verdicts"])')" || no "service not answering after the probes"
  # no leftover child of the fork server: only the fvfork process itself below its sandbox
  if [ ${#FK[@]} -gt 0 ]; then
    n=$(pgrep -f "fvfork/fvfork $S/snap/" | wc -l)
    [ "$n" -le 3 ] && ok "no leftover fork-server child ($n processes: bwrap, init, fvfork)" || no "leftover fork-server children: $n processes"
  fi
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S" > /dev/null; sleep 2
else
  no "service with limits did not start: $(tail -3 "$S.log")"
fi
# ---- 3. queue cap
S3=$W/svc3
if start "$S3" --max-pending 2 --max-inflight 1 --max-batch 1; then
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S3" "$W/corpus" > "$W/burst.txt" <<'PY'
import concurrent.futures as cf, os, sys
sys.path.insert(0, sys.argv[1]); import fvserve
st, corpus = sys.argv[2], sys.argv[3]
names = sorted(n for n in os.listdir(os.path.join(corpus, "projects")) if "--" not in n and n != "BATCH")
def go(t):
    r = fvserve.request(st, {"op": "verify", "pset": "t", "theorem": t,
                             "source": open(os.path.join(corpus, "projects", t, "Solution.lean")).read()})
    return t, r.get("verdict"), r.get("why", "")
with cf.ThreadPoolExecutor(len(names)) as ex:
    for t, v, why in ex.map(go, names):
        print(t, v, why[:80])
PY
  acc=$(grep -c ' ACCEPTED' "$W/burst.txt"); full=$(grep -c 'NO-VERDICT queue full' "$W/burst.txt"); other=$(grep -v -c -E ' ACCEPTED|NO-VERDICT queue full' "$W/burst.txt")
  [ "$other" = 0 ] && [ "$full" -gt 0 ] && [ "$acc" -gt 0 ] && ok "queue cap: $acc ACCEPTED, $full immediate 'queue full', 0 other" || no "queue cap: acc=$acc full=$full other=$other ($(grep -v -E ' ACCEPTED|queue full' "$W/burst.txt" | head -2))"
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S3" > /dev/null; sleep 2
else
  no "queue-cap service did not start"
fi
# ---- 4. request timeout
S4=$W/svc4
if start "$S4" --request-timeout 1; then
  python3 -I - "$S4" <<'PY' && ok "request timeout: a stalled and a trickling client are dropped, the service still answers" || no "request timeout"
import json, os, socket, sys, time
st = sys.argv[1]
s = socket.socket(socket.AF_UNIX); s.connect(os.path.join(st, "sock")); s.sendall(b'{"op": "verify", "pset"')
s.settimeout(10); t = time.time()
assert s.recv(100) == b"" and time.time() - t < 5, "not dropped"
s2 = socket.socket(socket.AF_UNIX); s2.connect(os.path.join(st, "sock")); s2.sendall(b'{"op": "stats"}\n'); s2.settimeout(10)
assert b"uptime_s" in s2.recv(65536)
# a TRICKLING client (one byte every 0.3 s never trips a per-recv timeout) must be dropped at the total deadline too
s3 = socket.socket(socket.AF_UNIX); s3.connect(os.path.join(st, "sock")); s3.setblocking(False); t = time.time(); dropped = None
while time.time() - t < 8:
    try:
        s3.send(b" ")
        if s3.recv(100) == b"":
            dropped = time.time() - t; break
    except BlockingIOError:
        pass
    except OSError:
        dropped = time.time() - t; break
    time.sleep(0.3)
print("trickling client dropped after", dropped)
assert dropped is not None and dropped < 4, f"trickling client not dropped ({dropped})"
PY
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S4" > /dev/null; sleep 2
else
  no "request-timeout service did not start"
fi
# ---- 5. slow lane: one batch slot; a runaway attempt must not hold back an honest one behind it
S5=$W/svc5
if start "$S5" --max-inflight 1 --slow-after 3 --max-slow 2 --attempt-timeout $ATO; then
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S5" "$W/att" "$W/corpus" <<'PY' && ok "slow lane: an honest attempt behind a runaway one is answered without waiting for its timeout" || no "slow lane"
import concurrent.futures as cf, os, sys, time
sys.path.insert(0, sys.argv[1]); import fvserve
st, att, corpus = sys.argv[2], sys.argv[3], sys.argv[4]
spin = open(os.path.join(att, "dec_zmod.lean")).read()                       # the 90 s loop (timeout 30 s)
honest = open(os.path.join(corpus, "projects", "lia_div3", "Solution.lean")).read()
t0 = time.time()
with cf.ThreadPoolExecutor(2) as ex:
    f1 = ex.submit(fvserve.request, st, {"op": "verify", "pset": "t", "theorem": "dec_zmod", "source": spin})
    time.sleep(1.0)
    th = time.time()
    f2 = ex.submit(fvserve.request, st, {"op": "verify", "pset": "t", "theorem": "lia_div3", "source": honest})
    r2 = f2.result(); t2 = time.time() - th
    r1 = f1.result(); t1 = time.time() - t0
print(f"honest: {r2['verdict']} after {t2:.1f} s; runaway: {r1['verdict']} after {t1:.1f} s ({r1.get('why','')[:60]})")
assert r2["verdict"] == "ACCEPTED" and r1["verdict"] == "NO-VERDICT" and t2 < t1 - 5, "honest attempt waited for the runaway one"
PY
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S5" > /dev/null; sleep 2
else
  no "slow-lane service did not start"
fi
# ---- 6. fork-server restart: after the worker dies, attempts still get verdicts and the worker comes back
if [ ${#FK[@]} -gt 0 ]; then
  S6=$W/svc6
  if start "$S6" "${FK[@]}"; then
    python3 -I - "$FASTVERIFY/tools/fvserve" "$S6" "$W/corpus" <<'PY' && ok "fork server restarted after it died; attempts verified throughout" || no "fork-server restart"
import os, subprocess, sys, time
sys.path.insert(0, sys.argv[1]); import fvserve
st, corpus = sys.argv[2], sys.argv[3]
src = lambda n: open(os.path.join(corpus, "projects", n, "Solution.lean")).read()
v = lambda n: fvserve.request(st, {"op": "verify", "pset": "t", "theorem": n, "source": src(n)})["verdict"]
stats = lambda: fvserve.request(st, {"op": "stats"}, 30)["verdicts"]
assert v("lia_div3") == "ACCEPTED"
n0 = stats().get("fork_compiles", 0)
subprocess.run(["pkill", "-f", "fvfork/fvfork " + st + "/snap/"])          # the worker (and its sandbox) only
time.sleep(1)
assert v("lia_bound") == "ACCEPTED", "attempt right after the worker died"
for _ in range(60):
    if stats().get("fork_restarts", 0) >= 1: break
    time.sleep(1)
s1 = stats()
assert s1.get("fork_restarts", 0) >= 1, f"no restart: {s1}"
assert v("lia_ages") == "ACCEPTED"
s2 = stats()
print(f"fork compiles before kill {n0}, restarts {s2.get('fork_restarts')}, fork compiles after {s2.get('fork_compiles')}, fallbacks {s2.get('fork_fallback', 0)}")
assert s2.get("fork_compiles", 0) > s1.get("fork_compiles", 0), "the restarted worker is not used"
PY
    python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S6" > /dev/null; sleep 2
  else
    no "fork-restart service did not start"
  fi
fi
# ---- 7. a killed service's private export dir is removed by the next service (same parent dir; tagged dirs only)
mkdir -p "$W/exd"; S7=$W/svc7
if start "$S7" --export-dir "$W/exd"; then
  SVP=$(pgrep -f "fvserve.py serve --state $S7 " | head -1); kill -9 $SVP; sleep 1; pkill -9 -f "fvfork/fvfork $S7/snap/" 2>/dev/null
  mkdir -p "$W/exd/fvserve-exports.untagged-keep"
  left=$(ls -d "$W"/exd/fvserve-exports.p* 2>/dev/null | wc -l)
  rm -rf "$S7"
  if start "$S7" --export-dir "$W/exd"; then
    now=$(ls -d "$W"/exd/fvserve-exports.p* | wc -l)
    [ "$left" = 1 ] && [ "$now" = 1 ] && [ -d "$W/exd/fvserve-exports.untagged-keep" ] && [ "$(ls -d "$W"/exd/fvserve-exports.p* | grep -c "\.p$SVP\.")" = 0 ] \
      && ok "stale export dir of a killed service removed at the next start (untagged dir kept)" || no "stale export dir: left=$left now=$now $(ls "$W/exd")"
    python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S7" > /dev/null; sleep 2
  else
    no "second service did not start"
  fi
else
  no "export-dir service did not start"
fi
# ---- 8. fair scheduling: one client's burst does not make another client wait behind all of it
S8=$W/svc8
if start "$S8" --fair --max-inflight 1 --max-batch 1; then
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S8" "$W/corpus" <<'PY' && ok "fair scheduling: a second client's attempt is not answered after a whole burst" || no "fair scheduling"
import concurrent.futures as cf, os, sys, time
sys.path.insert(0, sys.argv[1]); import fvserve
st, corpus = sys.argv[2], sys.argv[3]
names = sorted(n for n in os.listdir(os.path.join(corpus, "projects")) if "--" not in n and n != "BATCH")
src = lambda n: open(os.path.join(corpus, "projects", n, "Solution.lean")).read()
done = []
def go(client, n):
    r = fvserve.request(st, {"op": "verify", "pset": "t", "theorem": n, "source": src(n), "client": client})
    done.append((time.time(), client, r["verdict"]))
with cf.ThreadPoolExecutor(8) as ex:
    fs = [ex.submit(go, "A", n) for n in names[:6]]
    time.sleep(0.5)
    fs.append(ex.submit(go, "B", names[6]))
    [f.result() for f in fs]
order = [c for _, c, _ in sorted(done)]
print("completion order:", "".join(order), "verdicts:", sorted(set(v for _, _, v in done)))
assert all(v == "ACCEPTED" for _, _, v in done)
assert order.index("B") <= 3, "client B waited behind the whole burst of client A"
PY
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S8" > /dev/null; sleep 2
else
  no "fair service did not start"
fi
S8B=$W/svc8b
if start "$S8B" --max-pending-per-client 2 --max-inflight 1 --max-batch 1; then
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S8B" "$W/corpus" <<'PY' && ok "per-client queue cap: a burst is partly refused, another client is still served" || no "per-client queue cap"
import concurrent.futures as cf, os, sys, time
sys.path.insert(0, sys.argv[1]); import fvserve
st, corpus = sys.argv[2], sys.argv[3]
names = sorted(n for n in os.listdir(os.path.join(corpus, "projects")) if "--" not in n and n != "BATCH")
src = lambda n: open(os.path.join(corpus, "projects", n, "Solution.lean")).read()
req = lambda c, n: fvserve.request(st, {"op": "verify", "pset": "t", "theorem": n, "source": src(n), "client": c})
with cf.ThreadPoolExecutor(8) as ex:
    fa = [ex.submit(req, "A", n) for n in names[:6]]
    time.sleep(0.5)
    rb = ex.submit(req, "B", names[6]).result()
    ra = [f.result() for f in fa]
full = sum(1 for r in ra if "queue full for this client" in (r.get("why") or ""))
print("A:", [r["verdict"] for r in ra], "refused:", full, "| B:", rb["verdict"])
assert full >= 1 and rb["verdict"] == "ACCEPTED" and all(r["verdict"] in ("ACCEPTED", "NO-VERDICT") for r in ra)
PY
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S8B" > /dev/null; sleep 2
else
  no "per-client-cap service did not start"
fi
# ---- 9. a client that disconnects while its attempt lingers must not kill the dispatcher (later requests answered)
S9=$W/svc9
if start "$S9" --linger 2; then
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S9" "$W/corpus" <<'PY' && ok "linger + disconnect: the dispatcher survives, the next request is answered" || no "linger + disconnect"
import os, socket, sys, time
sys.path.insert(0, sys.argv[1]); import fvserve
st, corpus = sys.argv[2], sys.argv[3]
src = lambda n: open(os.path.join(corpus, "projects", n, "Solution.lean")).read()
try:
    fvserve.request(st, {"op": "verify", "pset": "t", "theorem": "lia_div3", "source": src("lia_div3")}, timeout=0.3)
except (socket.timeout, TimeoutError, OSError):
    pass                                   # the client gives up while the idle service lingers
time.sleep(3)                              # linger over: the dispatcher wakes to an empty queue
r = fvserve.request(st, {"op": "verify", "pset": "t", "theorem": "lia_bound", "source": src("lia_bound")}, timeout=300)
print("after the disconnect:", r.get("verdict"))
assert r.get("verdict") == "ACCEPTED"
PY
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S9" > /dev/null; sleep 2
else
  no "linger service did not start"
fi
# ---- 10. dispatcher error path with the real log() (logging under the condition's lock self-deadlocked); no Lean
if FVSERVE_PY="$FASTVERIFY/tools/fvserve/fvserve.py" timeout 60 python3 -I "$H/test/test-dispatch-error.py" > "$W/dispatch-error.txt" 2>&1; then
  ok "dispatcher survives an exception in take_batch and a cancelled linger attempt (4 unit cases)"
else
  no "dispatcher error path: $(tr '\n' ' ' < "$W/dispatch-error.txt" | cut -c1-300)"
fi
# ---- 11. concurrent batches on the fallback export path (--no-fast-export) must each check their OWN export:
#      every corpus case (honest + cheats) submitted twice at once, so honest and cheating siblings of a theorem overlap
S11=$W/svc11
if start "$S11" --no-fast-export --max-inflight 4; then
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S11" "$W/corpus" > "$W/f10.txt" 2>&1 <<'PY'
import concurrent.futures as cf, json, os, sys
sys.path.insert(0, sys.argv[1]); import fvserve
st, corpus = sys.argv[2], sys.argv[3]
cases = {c: v for c, v in json.load(open(os.path.join(corpus, "cases.json"))).items() if c != "BATCH"}
def one(c):
    v = cases[c]
    r = fvserve.request(st, {"op": "verify", "pset": "t", "theorem": v["challenge"],
                             "source": open(os.path.join(corpus, "projects", c, "Solution.lean")).read()}, timeout=900)
    return c, v["expected_official"], r.get("verdict"), (r.get("why") or "")[:140]
order = sorted(cases) + sorted(cases, reverse=True)
bad = []
with cf.ThreadPoolExecutor(12) as ex:
    for c, e, g, why in ex.map(one, order):
        if g != e:
            bad.append((c, e, g, why))
for b in bad:
    print("wrong:", *b)
print(f"{len(order)} requests ({len(cases)} cases x 2), {len(bad)} wrong")
sys.exit(1 if bad else 0)
PY
  if [ $? = 0 ]; then ok "fallback export path, concurrent siblings: $(tail -1 "$W/f10.txt")"; else no "fallback export race: $(tail -4 "$W/f10.txt" | tr '\n' ' ' | cut -c1-500)"; fi
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S11" > /dev/null; sleep 2
else
  no "service 11 did not start"
fi
# ---- 12. which code a running service uses: 'stats' reports the sha256 of the files loaded at start and which changed since
#      (a fix published while a service runs is not in use until a restart); the service runs from a private copy here
S12=$W/svc12; mkdir -p "$W/fvsrc12" && cp "$FASTVERIFY/tools/fvserve/fvserve.py" "$W/fvsrc12/"
python3 -I "$W/fvsrc12/fvserve.py" serve --state "$S12" --pset "t=$W/pset:$SHA" --threads "$T" --packages "$WS" --toolchain "$TC" \
    --fv "$FASTVERIFY" --profile laptop --max-pending 7 > "$S12.log" 2>&1 &
for i in $(seq 1 300); do grep -q '"ready"' "$S12.log" 2>/dev/null && break; kill -0 $! 2>/dev/null || break; sleep 1; done
if grep -q '"ready"' "$S12.log"; then
  python3 -I - "$FASTVERIFY/tools/fvserve" "$S12" "$W/fvsrc12/fvserve.py" <<'PY' && ok "stats reports the running code and flags a file changed since the start" || no "code version / stale report"
import hashlib, sys
sys.path.insert(0, sys.argv[1]); import fvserve
st, src = sys.argv[2], sys.argv[3]
a = fvserve.request(st, {"op": "stats"}, 30)
want = hashlib.sha256(open(src, "rb").read()).hexdigest()[:16]
assert a["code"]["fvserve"] == want and {"batchverify", "fvguard"} <= set(a["code"]) and a["stale"] == [], a
open(src, "a").write("\n# changed after the start\n")
b = fvserve.request(st, {"op": "stats"}, 30)
assert b["stale"] == ["fvserve"] and b["code"]["fvserve"] == want, b
print("code", a["code"], "stale after the change", b["stale"])
PY
  grep -q '"profile": "laptop"' "$S12.log" && ok "serve --profile laptop: the measured flag set, recorded in the ready line" || no "--profile not in the ready line"
  python3 -I "$FASTVERIFY/tools/fvserve/fvserve.py" stop --state "$S12" > /dev/null; sleep 2
else
  no "service 12 did not start"
fi
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit $bad

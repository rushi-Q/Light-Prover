#!/bin/bash
# test-fvserve.sh [WORK] : regression test of tools/fvserve: the persistent sound verification service.
# A 16-problem Mathlib set (the g06 problems); the OFFICIAL flow (bin/fastverify --preset reference) on the all-positive
# batch project must ACCEPT and yields the official problem-set challenge export; then ONE service (with the fork-server
# compile worker when it can be built here, and the trusted check-sound-svc.sh --integrity-cache) answers:
#   * every attempt of the g06 attempt set submitted one by one (honest -> ACCEPTED; cheats: axiom, weaker statement,
#     changed constant, macro-hidden sorry, ill-typed addDecl under debug.skipKernelTC, native_decide -> REJECTED; a
#     non-compiling attempt -> REJECTED with the compiler's error in `compiler_output`; a misspelt theorem; an attempt
#     importing another attempt's module -> REJECTED)
#   * the same attempts submitted CONCURRENTLY (they share batches: per-attempt verdicts must not change)
#   * best-of-3 of one theorem at once (does not compile / sorry / honest) -> REJECTED, REJECTED, ACCEPTED
#   * an attempt that tries to write into the service's batch directory (#eval writeFile) -> not ACCEPTED and no file
#   * after the fork server is killed, attempts are still verified (fallback to the official lean)
#   * a service started with a wrong challenge pin refuses to start
#   (the service runs with --keep 1 so that the concurrent part also checks that pruning never removes an in-flight batch)
# PASS iff every verdict = the expected one; "FAIL CRITICAL" if an attempt expected REJECTED is ACCEPTED.
# Env: EVAL_THREADS (default 16), FV_PACKAGES (trusted workspace; node-local copy recommended; default
#   <repository root>/verify/challenge), TC433 (official 4.33.1), FV_SCRATCH (parent of the default WORK).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)            # tools/fvserve
FASTVERIFY=${FASTVERIFY:-$(cd "$H/../.." && pwd)}; LIGHT_LEAN=${LIGHT_LEAN:-$(dirname "$FASTVERIFY")}
WS=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}
TC=${TC433:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
TP=$FASTVERIFY/bench/throughput
W=${1:-${FV_SCRATCH:?node-local work directory outside /tmp, /home, /var and /run (required unless WORK is given)}/$USER-fvserve-test}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-16}
NAMES=nt_prime_1009,lia_chicken,ineq_amgm2,rfl_nat_mul,an_pi_gt3,dec_zmod,lia_two_consec,alg_diff_squares,nt_sqrt2_irr,amc_sum_1_to_100,lia_div3,lia_bound,lia_ages,lia_floor_div,lia_system,lia_mod_comb
bad=0
ok() { echo "PASS $*"; }
no() { echo "FAIL $*"; bad=1; }
python3 -I "$TP/corpus/gen.py" "$W/corpus" --names "$NAMES" > /dev/null || { echo "FAIL gen.py"; echo "RESULT FAIL"; exit 1; }
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FASTVERIFY/bin/fastverify" "$W/corpus/projects/BATCH" \
    "$W/corpus/challenges/BATCH" "$W/ref" --preset reference --threads "$T" --packages "$WS" > "$W/ref.log" 2>&1
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/ref/result.json" 2>/dev/null)
[ "$v" = ACCEPTED ] && ok "official-flow positive batch ACCEPTED" || no "official flow on the positive batch: $v"
[ -f "$W/ref/challenge.export" ] || { echo "FAIL no official challenge export"; echo "RESULT FAIL"; exit 1; }
mkdir -p "$W/pset" && cp "$W/ref/challenge.export" "$W/pset/" && cp "$W/corpus/challenges/BATCH/comparator.json" "$W/pset/"
SHA=$(sha256sum "$W/pset/challenge.export" | cut -d' ' -f1)
# attempts (g06's): every problem with a cheating variant gets it, plus a non-compiling one, a misspelt theorem, an import
python3 -I "$TP/mkattempts.py" "$W/corpus" "$W/att" mix > /dev/null
printf 'import Mathlib\n\ntheorem lia_two_consec : ∀ n : ℕ, n %% 2 = 0 ∨ n %% 2 = 1 := by\n  intro n\n  exact v04_no_such_lemma n\n' > "$W/att/lia_two_consec.lean"
printf 'import Mathlib\n\ntheorem alg_diff_square : ∀ a b : ℝ, (a + b) * (a - b) = a ^ 2 - b ^ 2 := by\n  intro a b; ring\n' > "$W/att/alg_diff_squares.lean"
printf 'import Mathlib\nimport Attempt.amc_sum_1_to_100\n\ntheorem lia_div3 : ∀ n : ℕ, (n * 3 + 6) %% 3 = 0 := by intro n; omega\n' > "$W/att/lia_div3.lean"
EXP=$(python3 -I - "$W/corpus/cases.json" "$W/att.map.json" <<'PY'
import json, sys
cases = json.load(open(sys.argv[1])); m = json.load(open(sys.argv[2]))
exp = {t: cases[c]["expected_official"] for t, c in m.items()}
exp.update({"lia_two_consec": "REJECTED", "alg_diff_squares": "REJECTED", "lia_div3": "REJECTED"})
print(json.dumps(exp))
PY
)
# the service
FK=; if bash "$H/fork/build.sh" "$TC" "$W/fvfork" > "$W/fvfork-build.log" 2>&1; then FK=(--fork-server "$W/fvfork/fvfork"); else FK=(); echo "NOTE fvfork not built here (see $W/fvfork-build.log): testing the official-lean compile path only"; fi
start() {  # start STATE [args...]
  local st=$1; shift
  python3 -I "$H/fvserve.py" serve --state "$st" --pset "t=$W/pset:$SHA" --threads "$T" --packages "$WS" --toolchain "$TC" \
    --fv "$FASTVERIFY" --svc-check --keep 1 --max-batch 4 "$@" > "$st.log" 2>&1 &   # --keep 1 + several batches in flight: pruning must never touch an in-flight batch
  for i in $(seq 1 240); do grep -q '"ready"' "$st.log" 2>/dev/null && return 0; kill -0 $! 2>/dev/null || return 1; sleep 1; done
  return 1
}
S=$W/svc
start "$S" "${FK[@]}" || { no "service did not start: $(tail -3 "$S.log")"; echo "RESULT FAIL"; exit 1; }
ok "service ready: $(grep '"ready"' "$S.log" | cut -c1-160)"
judge() {  # judge LABEL RESULTS_TSV : compare per-attempt verdicts with EXP
  python3 -I - "$1" "$2" "$EXP" <<'PY'
import json, sys
lab, tsv, exp = sys.argv[1], sys.argv[2], json.loads(sys.argv[3])
rows = [ln.rstrip("\n").split("\t") for ln in open(tsv)]
hdr, rows = rows[0], rows[1:]
ix = {h: i for i, h in enumerate(hdr)}
bad = 0
for r in rows:
    t, v = r[ix["theorem"]], r[ix["verdict"]]
    e = exp.get(t, "?")
    if v == e:
        print(f"PASS {lab} {t}: {v}")
    elif e == "REJECTED" and v == "ACCEPTED":
        print(f"FAIL CRITICAL {lab} {t}: ACCEPTED, expected REJECTED"); bad = 1
    else:
        print(f"FAIL {lab} {t}: {v}, expected {e} ({r[ix['why']]})"); bad = 1
sys.exit(bad)
PY
}
python3 -I "$H/fvclient.py" seq --state "$S" --pset t "$W/att" --out "$W/seq.tsv" > "$W/seq.log" 2>&1
judge seq "$W/seq.tsv" || bad=1
python3 -I "$H/fvclient.py" burst --state "$S" --pset t "$W/att" --out "$W/burst.tsv" > "$W/burst.log" 2>&1
judge concurrent "$W/burst.tsv" || bad=1
# compiler feedback in the answer of a non-compiling attempt
python3 -I "$H/fvserve.py" submit --state "$S" --pset t --theorem lia_two_consec "$W/att/lia_two_consec.lean" > "$W/fb.json"
python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); sys.exit(0 if r["verdict"]=="REJECTED" and "v04_no_such_lemma" in r.get("compiler_output","") else 1)' "$W/fb.json" \
  && ok "feedback: compiler output returned for a non-compiling attempt" || no "feedback: $(head -c 300 "$W/fb.json")"
# best-of-3 of one theorem at once
mkdir -p "$W/bo"
printf 'import Mathlib\n\nopen Real Nat Finset\n\ntheorem lia_chicken : ∀ c r : ℕ, c + r = 35 → 2 * c + 4 * r = 94 → c = 23 := by\n  intro c r h1 h2\n  exact v04_no_such_lemma\n' > "$W/bo/1-fail.lean"
printf 'import Mathlib\n\nopen Real Nat Finset\n\ntheorem lia_chicken : ∀ c r : ℕ, c + r = 35 → 2 * c + 4 * r = 94 → c = 23 := by\n  sorry\n' > "$W/bo/2-sorry.lean"
cp "$W/corpus/projects/lia_chicken/Solution.lean" "$W/bo/3-honest.lean"
python3 -I "$H/fvclient.py" bestof --state "$S" --pset t --theorem lia_chicken "$W/bo/1-fail.lean" "$W/bo/2-sorry.lean" "$W/bo/3-honest.lean" --out "$W/bo.tsv" > "$W/bo.log" 2>&1
got=$(awk -F'\t' 'NR>1{printf "%s:%s ", $2, $5}' "$W/bo.tsv")
[ "$got" = "1-fail.lean:REJECTED 2-sorry.lean:REJECTED 3-honest.lean:ACCEPTED " ] && ok "best-of-3: $got" || no "best-of-3: $got"
# an attempt that tries to write into the service's batch directory
printf 'import Mathlib\n\n#eval show IO Unit from IO.FS.writeFile "%s/batches/PWNED" "x"\n\ntheorem rfl_nat_mul : (123456789 : ℕ) * 987654321 = 121932631112635269 := by norm_num\n' "$S" > "$W/pwn.lean"
python3 -I "$H/fvserve.py" submit --state "$S" --pset t --theorem rfl_nat_mul "$W/pwn.lean" > "$W/pwn.json"
pv=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$W/pwn.json")
[ ! -e "$S/batches/PWNED" ] && [ "$pv" != ACCEPTED ] && ok "write into the batch dir denied (verdict $pv, no file)" || no "write attack: verdict $pv, file $(ls "$S/batches/PWNED" 2>&1)"
# fork server killed -> attempts still verified (fallback to the official lean)
if [ ${#FK[@]} -gt 0 ]; then
  pkill -f "fvfork/fvfork $S/snap/"; sleep 1   # the worker (and its bwrap) only: the service argv has no snapshot path
  python3 -I "$H/fvserve.py" submit --state "$S" --pset t --theorem nt_prime_1009 "$W/att/nt_prime_1009.lean" > "$W/fb2.json"
  fv=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$W/fb2.json")
  [ "$fv" = "$(python3 -I -c 'import json,sys; print(json.loads(sys.argv[1])["nt_prime_1009"])' "$EXP")" ] && ok "after the fork server died: $fv (fallback)" || no "after the fork server died: $fv"
fi
python3 -I "$H/fvserve.py" stop --state "$S" > /dev/null; sleep 2
# a wrong challenge pin -> the service refuses to start
python3 -I "$H/fvserve.py" serve --state "$W/svc-badpin" --pset "t=$W/pset:$(printf '0%.0s' $(seq 64))" --threads 4 --packages "$WS" \
  --toolchain "$TC" --fv "$FASTVERIFY" > "$W/badpin.log" 2>&1
rc=$?; [ $rc -ne 0 ] && [ ! -S "$W/svc-badpin/sock" ] && grep -q 'refuse' "$W/badpin.log" && ok "wrong challenge pin: service refuses (rc $rc)" || no "wrong challenge pin: rc $rc $(tail -2 "$W/badpin.log")"
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit $bad

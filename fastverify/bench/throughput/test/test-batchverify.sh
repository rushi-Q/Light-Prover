#!/bin/bash
# test-batchverify.sh [WORK] : regression test of tools/batchverify.py: a mini problem set of 16 Mathlib
# problems; the OFFICIAL flow (bin/fastverify --preset reference) on the all-positive batch project (must ACCEPT; it also
# yields the official problem-set challenge export), then batchverify on attempts where 6 problems get a cheating variant
# (axiom, weaker statement, changed constant, macro-hidden sorry, ill-typed declaration added with debug.skipKernelTC,
# native_decide; all expected REJECTED), one a harmless @[implemented_by] look-alike (expected ACCEPTED), one an honest
# proof (ACCEPTED), one does not compile, one declares a misspelt theorem name, one imports another attempt's module
# (REJECTED), one honest attempt also declares another problem's theorem with sorry (both honest attempts ACCEPTED),
# and two honest attempts also prove another problem whose own attempt is a sorry / declares something else (those
# REJECTED: no cross-credit).
# PASS iff every per-attempt verdict = the expected
# one; "FAIL CRITICAL" if an attempt expected REJECTED is ACCEPTED. Also: a wrong --challenge-sha256 must give no ACCEPTED.
# Env: EVAL_THREADS (default 16), FV_PACKAGES (trusted workspace; a node-local copy is much faster on NFS hosts).
# Prints 'PASS ...' / 'FAIL ...' lines and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)            # bench/throughput
FASTVERIFY=${FASTVERIFY:-$(cd "$H/../.." && pwd)}; LIGHT_LEAN=${LIGHT_LEAN:-$(dirname "$FASTVERIFY")}
WS=${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}
W=${1:-${SCRATCH:-/scratch}/$USER-batchverify-test}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-16}
NAMES=nt_prime_1009,lia_chicken,ineq_amgm2,rfl_nat_mul,an_pi_gt3,dec_zmod,lia_two_consec,alg_diff_squares,nt_sqrt2_irr,amc_sum_1_to_100,lia_div3,lia_bound,lia_ages,lia_floor_div,lia_system,lia_mod_comb
bad=0
python3 -I "$H/corpus/gen.py" "$W/corpus" --names "$NAMES" > /dev/null || { echo "FAIL gen.py"; echo "RESULT FAIL"; exit 1; }
# 1. official flow on the positive batch (oracle) + the official challenge export of the problem set
env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 "$FASTVERIFY/bin/fastverify" "$W/corpus/projects/BATCH" \
    "$W/corpus/challenges/BATCH" "$W/ref" --preset reference --threads "$T" --packages "$WS" > "$W/ref.log" 2>&1
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/ref/result.json" 2>/dev/null)
[ "$v" = ACCEPTED ] && echo "PASS official-flow positive batch ACCEPTED" || { echo "FAIL official flow on the positive batch: $v"; bad=1; }
[ -f "$W/ref/challenge.export" ] || { echo "FAIL no official challenge export"; echo "RESULT FAIL"; exit 1; }
mkdir -p "$W/pset" && cp "$W/ref/challenge.export" "$W/pset/" && cp "$W/corpus/challenges/BATCH/comparator.json" "$W/pset/"
SHA=$(sha256sum "$W/pset/challenge.export" | cut -d' ' -f1)
# 2. attempts: every problem with a cheating variant gets it; two broken attempts
python3 -I "$H/mkattempts.py" "$W/corpus" "$W/att" mix > /dev/null
printf 'import Mathlib\n\ntheorem lia_two_consec : ∀ n : ℕ, n %% 2 = 0 ∨ n %% 2 = 1 := by\n  intro n\n  exact v04_no_such_lemma n\n' > "$W/att/lia_two_consec.lean"
printf 'import Mathlib\n\ntheorem alg_diff_square : ∀ a b : ℝ, (a + b) * (a - b) = a ^ 2 - b ^ 2 := by\n  intro a b; ring\n' > "$W/att/alg_diff_squares.lean"
# interference: an attempt that imports another attempt's module (must not compile: attempts see only the trusted packages)
printf 'import Mathlib\nimport Attempt.amc_sum_1_to_100\n\ntheorem lia_div3 : ∀ n : ℕ, (n * 3 + 6) %% 3 = 0 := by intro n; omega\n' > "$W/att/lia_div3.lean"
# interference: an honest attempt that ALSO declares another problem's theorem (with sorry) while that problem's honest
# attempt is in the batch: both honest attempts must be ACCEPTED (the duplicate is separated by the splitting)
printf 'import Mathlib\n\nopen Real Nat Finset\n\ntheorem amc_sum_1_to_100 : ∑ i ∈ range 101, i = 5050 := sorry\n\ntheorem lia_bound : ∀ n : ℕ, 3 * n + 2 < 20 → n ≤ 5 := by intro n h; omega\n' > "$W/att/lia_bound.lean"
# credit assignment: attempt lia_ages ALSO proves lia_floor_div validly, while lia_floor_div's own attempt uses sorry:
# lia_floor_div must be REJECTED (judged only from its own attempt), lia_ages ACCEPTED
printf 'import Mathlib\n\nopen Real Nat Finset\n\ntheorem lia_floor_div : ∀ n : ℕ, n / 2 + (n + 1) / 2 = n := by intro n; omega\n\ntheorem lia_ages : ∀ a b : ℕ, a = 3 * b → a + 10 = 2 * (b + 10) → a = 30 := by intro a b h1 h2; omega\n' > "$W/att/lia_ages.lean"
printf 'import Mathlib\n\nopen Real Nat Finset\n\ntheorem lia_floor_div : ∀ n : ℕ, n / 2 + (n + 1) / 2 = n := sorry\n' > "$W/att/lia_floor_div.lean"
# credit assignment: attempt lia_system also proves lia_mod_comb validly, while lia_mod_comb's own
# attempt declares something else: lia_mod_comb must NOT be credited (REJECTED: not declared by its own attempt)
printf 'import Mathlib\n\nopen Real Nat Finset\n\ntheorem lia_mod_comb : ∀ n : ℕ, n %% 4 = 3 → n %% 2 = 1 := by intro n h; omega\n\ntheorem lia_system : ∀ x y : ℤ, x + y = 10 → x - y = 4 → x = 7 ∧ y = 3 := by intro x y h1 h2; omega\n' > "$W/att/lia_system.lean"
printf 'import Mathlib\n\ntheorem v04_other : True := trivial\n' > "$W/att/lia_mod_comb.lean"
python3 -I "$FASTVERIFY/tools/batchverify.py" --pset "$W/pset" --attempts "$W/att" --out "$W/bv" --challenge-sha256 "$SHA" \
    --threads "$T" --fv "$FASTVERIFY" --packages "$WS" > "$W/bv.log" 2>&1
python3 -I - "$W" <<'EOF' || bad=1
import json, sys
W = sys.argv[1]
b = json.load(open(W + "/bv/batch.json"))
m = json.load(open(W + "/att.map.json"))
cases = json.load(open(W + "/corpus/cases.json"))
exp = {n: cases[c]["expected_official"] for n, c in m.items()}
exp["lia_two_consec"] = "REJECTED"      # does not compile
exp["alg_diff_squares"] = "REJECTED"    # declares a different theorem name
exp["lia_div3"] = "REJECTED"            # imports another attempt's module: does not compile
exp["lia_bound"] = "ACCEPTED"           # honest, plus a sorry'd duplicate of amc_sum_1_to_100 (whose honest attempt must still be ACCEPTED)
exp["lia_ages"] = "ACCEPTED"            # honest, plus a VALID proof of lia_floor_div
exp["lia_floor_div"] = "REJECTED"       # its own attempt uses sorry: no credit for lia_ages' proof
exp["lia_system"] = "ACCEPTED"          # honest, plus a VALID proof of lia_mod_comb
exp["lia_mod_comb"] = "REJECTED"        # its own attempt does not declare lia_mod_comb: no credit for lia_system's proof
bad = 0
for n in sorted(exp):
    got = (b["attempts"].get(n) or {}).get("verdict")
    why = (b["attempts"].get(n) or {}).get("why", "")[:90]
    if exp[n] == "REJECTED" and got == "ACCEPTED":
        print(f"FAIL CRITICAL {n} ({m.get(n)}): ACCEPTED, expected REJECTED"); bad = 1
    elif got == exp[n]:
        print(f"PASS {n} ({m.get(n)}) expected={exp[n]} got={got}: {why}")
    else:
        print(f"FAIL {n} ({m.get(n)}) expected={exp[n]} got={got}: {why}"); bad = 1
print(f"INFO batch: {b['summary']} in {b['seconds']} s, {b['n_checks']} checks")
sys.exit(bad)
EOF
# 3. a wrong challenge pin: no ACCEPTED at all
python3 -I "$FASTVERIFY/tools/batchverify.py" --pset "$W/pset" --attempts "$W/att" --out "$W/bv-wrongpin" \
    --challenge-sha256 0000000000000000000000000000000000000000000000000000000000000000 --threads "$T" \
    --fv "$FASTVERIFY" --packages "$WS" > "$W/bv-wrongpin.log" 2>&1
if grep -q '"ACCEPTED": [1-9]' "$W/bv-wrongpin.log"; then echo "FAIL CRITICAL wrong challenge pin gave ACCEPTED"; bad=1
else echo "PASS wrong challenge pin: no ACCEPTED ($(tail -1 "$W/bv-wrongpin.log" | cut -c1-80))"; fi
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit $bad

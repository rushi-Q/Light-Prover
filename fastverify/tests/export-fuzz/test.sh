#!/bin/bash
# test.sh [WORKDIR] : regression test of the sound check against crafted exports. Steps:
#   1 setup        bulk CS variant (after check-sound.sh --preflight), parsediff, base projects (official flow)
#   2 seams        every seams.py case of every base: no FAIL-CRITICAL / FAIL-PARSER; the official verdict equals
#                  results/seams-expected.tsv (else DRIFT) and CS's verdict equals the recorded one or the official one
#                  (IMPROVED, e.g. after a fix of a decline on a crafted name); any other change = REGRESSION
#   3 fuzz         campaign.sh with 2 mutants per operator per base (seed 1): no FAIL-CRITICAL / FAIL-PARSER row
#   4 export-in    the seams cases through bin/fastverify --from-export --preset sound: verdict = CS verdict, never a wrong accept
#   5 parser       parser agreement (parsediff) on every base export (solution + challenge): no DIVERGE
# Prints 'PASS|FAIL <step>: ...' and 'RESULT pass=N fail=M'; exit 0 iff no FAIL. ~10-20 min on a host with 16-32 cores.
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
T=${1:-$W/test-$(date +%Y%m%d%H%M%S)}; mkdir -p "$T"; J=${EXPORT_FUZZ_JOBS:-8}
pass=0; fail=0
ok() { echo "PASS $*"; pass=$((pass+1)); }; ko() { echo "FAIL $*"; fail=$((fail+1)); }
bash "$H/setup.sh" > "$T/setup.log" 2>&1 && ok "setup: $(tail -1 "$T/setup.log")" || { ko "setup: $(tail -3 "$T/setup.log" | tr '\n' ' ')"; echo "RESULT pass=$pass fail=$fail"; exit 1; }
# 2 seams
bash "$H/runseams.sh" "$T/seams" "$J" > "$T/seams.log" 2>&1
python3 -I - "$T/seams" "$H/results/seams-expected.tsv" <<'PY' > "$T/seams.check"
import os, sys
root, exp = sys.argv[1], sys.argv[2]
want = {}
for l in open(exp):
    b, cid, of, cs, pd = l.rstrip('\n').split('\t')[:5]; want[(b, cid)] = (of, cs)
bad = 0; n = 0
for b in sorted(os.listdir(root)):
    f = os.path.join(root, b, 'results.tsv')
    if not os.path.exists(f): continue
    for l in open(f):
        p = l.rstrip('\n').split('\t'); cid = p[0][len(b) + 1:]; n += 1
        st, cs, of = p[9], p[5], p[7]
        if st.startswith('FAIL'):
            print(f'FAIL {b} {cid}: {st} (CS {cs}, official {of})'); bad += 1; continue
        w = want.get((b, cid))
        if w is None:
            print(f'NEW {b} {cid}: official {of}, CS {cs} (no recorded expectation)'); continue
        if of != w[0]:
            print(f'DRIFT {b} {cid}: official verdict {of}, recorded {w[0]} (environment changed: investigate)'); bad += 1
        elif cs != w[1]:
            # a change TOWARDS the official verdict is an improvement (e.g. a fixed decline: DECLINED -> REJECTED)
            if cs == of:
                print(f'IMPROVED {b} {cid}: CS {w[1]} -> {cs} (= official)')
            else:
                print(f'REGRESSION {b} {cid}: CS {cs}, recorded {w[1]} (official {of})'); bad += 1
print(f'checked {n} cases, {bad} failures')
PY
grep -q ', 0 failures$' "$T/seams.check" && ok "seams: $(tail -1 "$T/seams.check")" || ko "seams: $(grep -v '^NEW' "$T/seams.check" | head -5 | tr '\n' ' ')"
# 3 fuzz
bash "$H/campaign.sh" "$T/fuzz" 2 1 "$J" > "$T/fuzz.log" 2>&1
nf=$(cat "$T"/fuzz/*/results.tsv 2>/dev/null | awk -F'\t' '$10 ~ /^FAIL/' | wc -l); nr=$(cat "$T"/fuzz/*/results.tsv 2>/dev/null | wc -l)
[ "$nr" -gt 0 ] && [ "$nf" = 0 ] && ok "fuzz: $nr mutants, 0 FAIL rows" || ko "fuzz: $nr mutants, $nf FAIL rows (see $T/fuzz/*/results.tsv)"
# 4 export-in end to end
bash "$H/e2e_exportin.sh" "$T/seams" "$T/e2e" "$J" > "$T/e2e.log" 2>&1
ne=$(wc -l < "$T/e2e/rows.tsv"); nb=$(grep -vc '^PASS' "$T/e2e/rows.tsv")
[ "$ne" -gt 0 ] && [ "$nb" = 0 ] && ok "export-in: $ne cases, all PASS" || ko "export-in: $ne cases, $nb not PASS ($T/e2e/rows.tsv)"
# 5 parser agreement on the base exports
bash "$H/parsediff/realrun.sh" "$T/r7.tsv" "$W"/bases/*/out/solution.export "$W"/bases/*/out/challenge.export > "$T/r7.log" 2>&1 \
  && ok "parser-agreement: $(tr -s ' \n' ' ' < "$T/r7.log")" || ko "parser-agreement: $(tr -s ' \n' ' ' < "$T/r7.log")"
echo "RESULT pass=$pass fail=$fail (work dir $T)"
[ "$fail" = 0 ]

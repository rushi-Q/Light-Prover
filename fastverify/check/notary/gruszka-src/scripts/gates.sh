#!/bin/bash
CAP=${CAP:-$(cd "$(dirname "$0")" && pwd)/capped}
# Soundness gates: all small tests, adversarial vectors (bad_* must be
# rejected, good_* accepted). Prints a summary; exit 1 on a wrong verdict,
# a good test or vector not accepted, or a crash.
D=${GRUSZKA_DIR:-$(cd "$(dirname "$0")/.." && pwd)}
BIN=${1:-$D/target/release/gruszka}
case "$BIN" in /*) ;; *) BIN=$PWD/$BIN;; esac
$D/scripts/run_tests.sh $BIN > /tmp/sk-gates.$$
cat /tmp/sk-gates.$$
bad=0
grep -A100 "== WRONG" /tmp/sk-gates.$$ | grep -B100 "== good not" | grep -q '^bad accepted' && bad=1
# milestone 16: a crash or a good test not accepted fails the gate too
grep -q ' crash(' /tmp/sk-gates.$$ && { echo "SMALL TESTS CRASHED"; bad=1; }
grep -A100 "== good not" /tmp/sk-gates.$$ | grep -B100 "== bad declined" | grep -q '^good' && { echo "A GOOD SMALL TEST NOT ACCEPTED"; bad=1; }
for f in $D/tests/adv/*.ndjson; do
  # s*: sessions cut every 2 declarations (a reset inside every chain);
  # f*: level tables flushed after every declaration (milestone 19)
  for w in 1 4 ns1 ns4 s1 s4 f1; do
    o=file; sd=0; lf=4194304; case $w in ns*) o=ns; w=${w#ns};; s*) sd=2; w=${w#s};; f*) lf=0; w=${w#f};; esac
    # milestone 38: a cap kill is reported as such, not as a wrong verdict
    # with an empty reason (ADV_SECS: the region gates' checked runs are slow)
    r=$(SK_LVL_FLUSH=$lf SK_SESSION_DECLS=$sd SK_ORDER=$o "$CAP" 2000 ${ADV_SECS:-20} $BIN $f $w 2>/dev/null | tail -1; echo "rc=${pipestatus[1]:-${PIPESTATUS[0]}}")
    rc=${r##*rc=}; r=${r%rc=*}; r=${r%$'\n'}
    case "$rc" in
      142) echo "ADV TIMEOUT (${ADV_SECS:-20} s cap) w$w: $(basename $f)"; bad=1; continue;;
      137) echo "ADV CAPPED (2000 MB) w$w: $(basename $f)"; bad=1; continue;;
    esac
    case "$(basename $f)" in
      bad_*) case "$r" in rejected*) ;; *) echo "ADV WRONG w$w: $(basename $f): $r"; bad=1;; esac;;
      # milestone 34: a good vector not accepted fails the gate too (M33's
      # mutant major_lp was seen only as a printed line)
      good_*) case "$r" in accepted*) ;; *) echo "ADV GOOD NOT ACCEPTED w$w: $(basename $f): $r"; bad=1;; esac;;
    esac
  done
done
echo "adv: $(ls $D/tests/adv/*.ndjson | wc -l) vectors checked, wrong or not accepted=$bad"
# milestone 26: subset checks (--only): Pestka's fixtures, INDEX lies, the
# sweep over the bad vectors (tests/only.sh)
$D/tests/only.sh $BIN > /tmp/sk-only.$$ 2>&1 || { grep -E '^FAIL' /tmp/sk-only.$$; bad=1; }
grep -E '^(sweep|ONLYDONE)' /tmp/sk-only.$$; rm -f /tmp/sk-only.$$
# verdict parity with Pestka on the corpora (GATES_CORPORA="" skips)
if [ "${GATES_CORPORA-x}" != "" ]; then
  $D/scripts/parity.sh $BIN ${GATES_CORPORA} || bad=1
fi
rm /tmp/sk-gates.$$
exit $bad

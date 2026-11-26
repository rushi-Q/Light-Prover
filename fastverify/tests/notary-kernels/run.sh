#!/bin/bash
# tests/notary-kernels/run.sh [WORKDIR] - regression test of check/notary/check-notary.sh --kernels:
#  (1) --kernels all on valid official 4.36 output that unfolds a theorem body (thmunfold, accepted by the official lake
#      comparator): con-leche / con-ron reject it (theorem bodies are opaque to them) -> must be DECLINED, never REJECTED;
#  (2) a declaration named «internal error» must not change con-leche's classification (anchored lines only);
#  (3) nanoda_bin exit codes: 101 + a panic in its type checker = rejected, 1 = error (not decided);
#  (4) --kernels without gruszka: gruszka-r7 is added (R7 keeps its third, independent parser; basis/kernels say so);
#  plus controls: default notary ACCEPTS thmunfold; an export the official kernel rejects stays REJECTED with --kernels all.
# Inputs: data/ (sha256 in data/SHA256SUMS; thmunfold-*.lean are the sources the exports were made from with the official
# Lean 4.36.0 lean + leanexport, in bwrap without network). Exit 0 iff every row passes.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd); CN=$FV/check/notary/check-notary.sh; D=$H/data
W=${1:-$(mktemp -d /tmp/notary-kernels-test.XXXXXX)}; mkdir -p "$W"
(cd "$D" && sha256sum -c --quiet SHA256SUMS) || { echo "FAIL data integrity"; exit 1; }
NP=$FV/check/notary/pins.env; pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$NP"; }
SG=$(pin selftest_good); SC=$(pin selftest_challenge); SCFG=$(pin selftest_comparator)
KBAD=/scratch/fastverify-next/selftest/selftest-kbad.export   # selftest_good with fvSelfTest's proof ill-typed (check/sound pins)
P=0; F=0
row() {  # row NAME WANT_RC PYTHON_PREDICATE(j) -- check-notary args...
  local n=$1 want=$2 pred=$3; shift 4
  local out rc; out=$("$CN" "$@" --threads 4 2> "$W/$n.err" | tail -n 1); rc=$?
  rc=$(printf '%s' "$out" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.read())["exit"])' 2>/dev/null || echo X)
  if [ "$rc" = "$want" ] && printf '%s' "$out" | python3 -I -c "import json,sys; j=json.loads(sys.stdin.read()); sys.exit(0 if ($pred) else 1)" 2>/dev/null; then
    echo "PASS $n (rc=$rc)"; P=$((P+1))
  else echo "FAIL $n: want rc=$want [$pred], got rc=$rc: $(printf '%s' "$out" | cut -c1-600)"; F=$((F+1)); fi
}
ks() { echo "j.get('kernel_status') and j['kernel_status'].get('$1',{}).get('status')=='$2'"; }
row thmunfold-default 0 "j['verdict']=='ACCEPTED' and j['r7_digest']['matched_legs']==['ccmp','lean','gruszka']" -- \
  "$D/thmunfold-solution.export" "$D/thmunfold-challenge.export" "$D/thmunfold-comparator.json"
row thmunfold-all-declined 2 "j['verdict']=='DECLINED' and j['kernels']=='gruszka,con-ron,con-leche' and 'theorem bodies as opaque' in j['reason'] and $(ks con-leche rejected) and $(ks gruszka accepted)" -- \
  "$D/thmunfold-solution.export" "$D/thmunfold-challenge.export" "$D/thmunfold-comparator.json" --kernels all
sed 's/"str":"k04t"/"str":"internal error"/g' "$D/thmunfold-solution.export" > "$W/thmunfold-inj.export"
row name-injection-anchored 2 "j['verdict']=='DECLINED' and $(ks con-leche rejected) and 'internal error' in j['kernel_status']['con-leche']['message']" -- \
  "$W/thmunfold-inj.export" "$D/thmunfold-challenge.export" "$D/thmunfold-comparator.json" --kernels gruszka,con-leche
row conron-only-adds-gruszka 2 "j['kernels']=='gruszka,con-ron' and $(ks con-ron rejected) and $(ks gruszka accepted)" -- \
  "$D/thmunfold-solution.export" "$D/thmunfold-challenge.export" "$D/thmunfold-comparator.json" --kernels con-ron
row nanoda-only-keeps-r7-3legs 0 "j['verdict']=='ACCEPTED' and j['kernels']=='gruszka,nanoda' and j['r7_digest']['matched_legs']==['ccmp','lean','gruszka'] and 'gruszka,nanoda' in j['basis'] and $(ks nanoda accepted)" -- \
  "$SG" "$SC" "$SCFG" --kernels nanoda
[ -f "$KBAD" ] && row official-reject-stays-rejected 1 "j['verdict']=='REJECTED' and 'Lean default exited with 1' in j['reason']" -- \
  "$KBAD" "$SC" "$SCFG" --kernels all
# nanoda 0.4.17 on an export whose theorem was moved to the end (official leanonly ACCEPTS; the official comparator with
# nanoda REJECTS; gruszka rejects it too: 'not declared before', pre-existing). nanoda's panic
# here is 'declaration not found in infer_const' (it reached a declaration it had not loaded: an ordering limitation), so
# it is 'not decided' and the verdict is DECLINED, never REJECTED (gruszka's order rejection is 'not decided' too);
# nanoda's genuine type-checker panics stay 'rejected' (unit row below)
row nanoda-101-classified 2 "j['verdict']=='DECLINED' and j['kernel_status']['nanoda']['status']=='not decided' and 'could not resolve a declaration' in j['kernel_status']['nanoda']['reason']" -- \
  "$D/accept-fmt-thm-moved-to-end.export" "$D/rhminiF-challenge.export" "$D/rhminiF-comparator.leanonly.json" --kernels nanoda
# unit rows of the classifier (check-notary.sh --xk-classify NAME LOG RC; test interface, exit 2)
cls() {  # cls NAME RC WANT_STATUS LOGTEXT
  printf '%b' "$4" > "$W/cls.log"; local got; got=$("$CN" --xk-classify "$1" "$W/cls.log" "$2" | head -1)
  if [ "$got" = "$3" ]; then echo "PASS classify $1 rc=$2 -> $3"; P=$((P+1)); else echo "FAIL classify $1 rc=$2: want '$3', got '$got' for: $4"; F=$((F+1)); fi
}
cls nanoda 101 rejected "thread 'thread_2' (1303093) panicked at src/tc.rs:955:71:\nassertion failed: self.def_eq(u, v)\n"
cls nanoda 101 "not decided" "thread 'main' (7) panicked at src/parser.rs:120:9:\nbad line\n"
cls nanoda 101 "not decided" "thread 'thread_2' (5) panicked at src/tc.rs:230:13:\ndeclaration not found in infer_const, foo\n"
cls nanoda 1 "not decided" "Error: failed to open configuration file\n"
cls nanoda 0 accepted ""
cls con-leche 1 rejected "con-leche: invalid: application type mismatch [at theorem internal error._proof_1_1, fold position 70] (--verified) t=3.6s\n"
cls con-leche 1 rejected "con-leche: invalid: type mismatch [at theorem out of memory, fold position 9] (--verified)\n"
cls con-leche 1 "not decided" "con-leche: invalid: fuel exhausted: whnf loop [at theorem t, fold position 9] (--verified)\n"
cls con-leche 1 "not decided" "INTERNAL PANIC: out of memory\n"
cls con-leche 1 "not decided" "con-leche: invalid: the kernel refused a \`Nat\` numeral because its size exceeds the maximum [at def n, fold position 3]\n"
cls con-leche 0 "not decided" "con-leche: 1 inductive blocks modelled in-process\n"
cls con-leche 0 accepted "con-leche: accepted 458 declarations (--verified)\n"
cls con-ron 1 rejected "con-ron: rejected: application type mismatch [at thm k04t._proof_1_1, fold position 70] (--verified) t=5.6s\n"
cls con-ron 134 "not decided" "memory allocation of 123 bytes failed\n"
cls con-ron 0 accepted "con-ron: accepted 458 declarations (--verified)\n"
cls gruszka 1 rejected "rejected: FooBfs: recursor type: motive major type mismatch\n"
cls gruszka 2 "not decided" "declined: numNested differs\n"
cls gruszka 0 accepted "accepted\n"
echo "notary-kernels: $P passed, $F failed"; [ -n "${1:-}" ] || rm -rf "$W"; [ $F = 0 ]

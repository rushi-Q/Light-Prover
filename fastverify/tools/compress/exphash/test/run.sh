#!/bin/bash
# Regression test of the export-level sharing tools (exphash, redirects*.py, expcompress) against the TRUSTED check.
#   test/run.sh [WORKDIR]      (default $FV_SCRATCH/$USER-exphash-test.PID or a mktemp dir; needs bwrap, Lean v4.33.1, lean4export,
#                               fastverify/check/sound/check-sound.sh preflight OK; auto-builds exphash if needed)
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
TOOLS=$(cd "$HERE/.." && pwd)
FV=$(cd "$TOOLS/../../.." && pwd)
if [ -n "${1:-}" ]; then
  W=$1
elif [ -n "${FV_SCRATCH:-}" ]; then
  W=$FV_SCRATCH/${USER:-u}-exphash-test.$$
else
  W=$(mktemp -d "${TMPDIR:-/tmp}/exphash-test.XXXXXX")
fi
if [ -n "${BIN_DIR:-}" ] && [ -x "$BIN_DIR/exphash" ]; then
  :
elif [ -x "${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-exphash-target/release/exphash" ]; then   # build.sh's default target
  BIN_DIR="${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-exphash-target/release"
else
  BIN_DIR=$("$TOOLS/build.sh" | tail -1)
fi
T33=${T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
EXP=${EXP:-/scratch/fastverify-next/exporter/lean4export-979c4f8}
[ -x "$EXP" ] || EXP=$FV/../env/tools/lean4export/.lake/build/bin/lean4export
CS=$FV/check/sound/check-sound.sh
fail=0
row() { printf '%-6s %s\n' "$1" "$2"; [ "$1" = PASS ] || fail=1; }
rm -rf "$W"; mkdir -p "$W"
cp "$HERE/x/Main.lean" "$HERE/x/Challenge.lean" "$HERE/x/comparator.json" "$W/"
TG=$(cat "$HERE/x/targets.txt")
for m in Main Challenge; do
  tg=$TG; [ $m = Challenge ] && tg=${TG/ main_thm2/}
  bwrap --ro-bind / / --bind "$W" "$W" --dev /dev --proc /proc --unshare-net --chdir "$W" \
    --setenv PATH "$T33/bin:/usr/bin:/bin" -- "$T33/bin/lean" -o $m.olean $m.lean > "$W/$m.build.log" 2>&1 || { row FAIL "build $m"; rm -rf "$W"; exit 1; }
  bwrap --ro-bind / / --bind "$W" "$W" --dev /dev --proc /proc --unshare-net --chdir "$W" \
    --setenv PATH "$T33/bin:/usr/bin:/bin" --setenv LEAN_PATH "$W:$T33/lib/lean" -- "$EXP" $m -- $tg > "$W/$m.export" 2> "$W/$m.export.log" \
    || { row FAIL "export $m"; rm -rf "$W"; exit 1; }
done
check() {
  "$CS" "$1" "$W/Challenge.export" "$W/comparator.json" --threads 4 2>/dev/null | tail -1 | \
    /usr/bin/python3 -c 'import json,sys; print(json.loads(sys.stdin.read())["verdict"])' 2>/dev/null || echo ERROR
}
ndecl() { grep -c -E '^\{"(thm|def|inductive|axiom|opaque|quot)"' "$1"; }
v0=$(check "$W/Main.export"); [ "$v0" = ACCEPTED ] && row PASS "original export ACCEPTED ($(ndecl "$W/Main.export") decls)" || row FAIL "original export $v0"
"$BIN_DIR/exphash" "$W/Main.export" "$W/h" 2> "$W/h.log"
awk -F'\t' 'NR>1 && ($2 ~ /^Tst\./ || $2 ~ /^main_thm/) {print $2 "\tTst\t" $1}' "$W/h/decls.tsv" > "$W/project.tsv"
# case 1
python3 "$TOOLS/redirects.py" "$W/h/decls.tsv" "$W/r1.tsv" --project "$W/project.tsv" --targets "$HERE/x/targets.txt" 2>/dev/null
"$BIN_DIR/expcompress" "$W/Main.export" "$W/r1.tsv" "$HERE/x/targets.txt" "$W/c1.export" 2> "$W/c1.log"
v1=$(check "$W/c1.export"); n0=$(ndecl "$W/Main.export"); n1=$(ndecl "$W/c1.export")
[ "$v1" = ACCEPTED ] && [ "$n1" -lt "$n0" ] && row PASS "case 1 theorem sharing: $(wc -l < "$W/r1.tsv") redirects, decls $n0 -> $n1, ACCEPTED" \
  || row FAIL "case 1: $v1, decls $n0 -> $n1"
# case 2
"$BIN_DIR/exphash" --classes --project "$W/project.tsv" "$W/Main.export" "$W/hc" 2> "$W/hc.log"
python3 "$TOOLS/redirects_sem.py" "$W/hc/decls.tsv" "$W/r2.tsv" --project "$W/project.tsv" --targets "$HERE/x/targets.txt" 2>/dev/null
"$BIN_DIR/expcompress" "$W/Main.export" "$W/r2.tsv" "$HERE/x/targets.txt" "$W/c2.export" 2> "$W/c2.log"
v2=$(check "$W/c2.export"); n2=$(ndecl "$W/c2.export")
pair() { grep -q -E "^($1	$2|$2	$1)\$" "$W/r2.tsv"; }
pair "Tst.sq'" Tst.sq && pair Tst.Q Tst.P && pair Tst.Q.sum Tst.P.sum && pair Tst.s2 Tst.s1 && \
  [ "$(grep -c -E '^Tst\.t[123]	Tst\.t[123]$' "$W/r2.tsv")" = 2 ] && hasall=1 || hasall=0
[ "$v2" = ACCEPTED ] && [ "$n2" -lt "$n1" ] && [ $hasall = 1 ] && row PASS "case 2 semantic sharing (sq~sq', P~Q, P.sum~Q.sum, s1~s2, t1~t2~t3): $(wc -l < "$W/r2.tsv") redirects, decls $n0 -> $n2, ACCEPTED" \
  || row FAIL "case 2: $v2, decls $n0 -> $n2, expected redirects present=$hasall"
# case 3
printf 'Tst.u2\tTst.t2\n' > "$W/r3.tsv"
"$BIN_DIR/expcompress" "$W/Main.export" "$W/r3.tsv" "$HERE/x/targets.txt" "$W/c3.export" 2> "$W/c3.log"
v3=$(check "$W/c3.export")
[ "$v3" = REJECTED ] && row PASS "case 3 wrong redirect -> trusted check REJECTED" || row FAIL "case 3 wrong redirect -> $v3"
# case 4
awk -F'\t' 'BEGIN{OFS="\t"} {if ($1=="Tst.sq'"'"'") $2="Statements"; print}' "$W/project.tsv" > "$W/project4.tsv"
python3 "$TOOLS/redirects_sem.py" "$W/hc/decls.tsv" "$W/r4.tsv" --project "$W/project4.tsv" --targets "$HERE/x/targets.txt" 2>/dev/null
grep -q "^Tst.sq'	" "$W/r4.tsv" && row FAIL "case 4: a Statements-module definition was redirected" || row PASS "case 4 Statements-module definitions are never redirected"
# case 5
python3 "$TOOLS/classes_plan.py" "$W/hc/decls.tsv" "$W/cp5.tsv" --project "$W/project.tsv" --targets "$HERE/x/targets.txt" --semantic 2>/dev/null
"$BIN_DIR/expcompress" "$W/Main.export" --choose "$W/cp5.tsv" "$HERE/x/targets.txt" "$W/c5.export" --write-redirects "$W/r5.tsv" 2> "$W/c5.log"
v5=$(check "$W/c5.export"); n5=$(ndecl "$W/c5.export")
[ "$v5" = ACCEPTED ] && [ "$n5" -lt "$n0" ] && row PASS "case 5 --choose (cheapest acyclic representatives): $(wc -l < "$W/r5.tsv") redirects, decls $n0 -> $n5, ACCEPTED" \
  || row FAIL "case 5: $v5, decls $n0 -> $n5"
# case 6
EXPHASH_BIN="$BIN_DIR" "$TOOLS/share.sh" "$W/Main.export" "$W/Challenge.export" "$W/comparator.json" "$W/g6" --check 4 > "$W/g6.log" 2>&1
v6=$(/usr/bin/python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$W/g6/check.json" 2>/dev/null || echo ERROR)
n6=$(ndecl "$W/g6/solution.export" 2>/dev/null || echo 0)
[ "$v6" = ACCEPTED ] && [ "$n6" -lt "$n0" ] && row PASS "case 6 share.sh generic (challenge constants nominal): $(wc -l < "$W/g6/redirects.tsv") redirects, decls $n0 -> $n6, ACCEPTED" \
  || row FAIL "case 6: $v6, decls $n0 -> $n6"
rm -rf "$W"
[ $fail = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
exit $fail

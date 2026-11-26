#!/bin/bash
# compress-failure-classes/rename-partial-drop/run.sh [WORK] (Stage 3 tool guard)
# Failure class (attribute.py 'renamed names'): a rename OLD -> NEW is a set of edits in several modules (a `replace` of the
# declaration line + `subst OLD NEW` in every user). Dropping it only in the module that failed leaves the other modules
# referring to a name that no longer exists ('Unknown identifier'). Guard: tools/compress/scheme/rename_deny.py must
# drop the WHOLE rename (every subst of OLD, and the replace that declares NEW) and keep unrelated renames whole.
# Lean part (plain official lean in bwrap, no Mathlib; edits applied with tools/compress/dedup/apply_edits.py): the naive
# partial drop breaks the build with 'Unknown identifier', rename_deny's output builds.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-$(cd "$H/../../.." && pwd)}
W=${1:-/tmp/$USER-s3r-rn}; rm -rf "$W"; mkdir -p "$W/p/src/R"
TC=${TC433:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
bad=0; ok() { echo "PASS $*"; }; no() { echo "FAIL $*"; bad=1; }
# R.Defs declares foo_alt (line 2) and bar_alt (line 3); R.U1 and R.U2 use them
printf 'namespace R\ntheorem foo_alt : True := trivial\ntheorem bar_alt : True := trivial\nend R\n' > "$W/p/src/R/Defs.lean"
printf 'import R.Defs\nnamespace R\ntheorem u1 : True := foo_alt\ntheorem v1 : True := bar_alt\nend R\n' > "$W/p/src/R/U1.lean"
printf 'import R.Defs\nnamespace R\ntheorem u2 : True := foo_alt\nend R\n' > "$W/p/src/R/U2.lean"
T=$(printf '\t')
{ printf 'R.Defs%s2%s2%sreplace%srename-edit%stheorem foo : True := trivial\n' "$T" "$T" "$T" "$T" "$T"
  printf 'R.Defs%s0%s0%ssubst%srename-edit%sfoo_alt foo\n' "$T" "$T" "$T" "$T" "$T"
  printf 'R.U1%s0%s0%ssubst%srename-edit%sfoo_alt foo\n' "$T" "$T" "$T" "$T" "$T"
  printf 'R.U2%s0%s0%ssubst%srename-edit%sfoo_alt foo\n' "$T" "$T" "$T" "$T" "$T"
  printf 'R.Defs%s3%s3%sreplace%srename-edit%stheorem bar : True := trivial\n' "$T" "$T" "$T" "$T" "$T"
  printf 'R.Defs%s0%s0%ssubst%srename-edit%sbar_alt bar\n' "$T" "$T" "$T" "$T" "$T"
  printf 'R.U1%s0%s0%ssubst%srename-edit%sbar_alt bar\n' "$T" "$T" "$T" "$T" "$T"; } > "$W/rn.tsv"
echo "R.U2" > "$W/failing.txt"                      # the train saw R.U2 fail with the rename foo_alt -> foo
python3 -I "$FV/tools/compress/scheme/rename_deny.py" "$W/rn.tsv" "$W/rn.out" "$W/failing.txt" > "$W/rd.out" 2>&1 || no "rename_deny exited non-zero: $(tail -1 "$W/rd.out")"
nfoo=$(grep -c 'foo' "$W/rn.out"); nbar=$(grep -c 'bar' "$W/rn.out")
[ "$nfoo" = 0 ] && [ "$nbar" = 3 ] && ok "rename_deny drops the whole rename foo_alt->foo (all 4 edits, every module) and keeps bar_alt->bar whole (3)" || no "rename_deny kept $nfoo foo edits / $nbar bar edits (want 0 / 3)"
grep -v "^R.U2${T}" "$W/rn.tsv" > "$W/naive.tsv"   # the naive repair: drop only the failing module's edits
if [ -x "$TC/bin/lean" ] && [ -x /usr/bin/bwrap ]; then
  build() {   # build DIR: compile R.Defs, R.U1, R.U2 in dependency order with plain lean (olean output in DIR/build)
    local d=$1; mkdir -p "$d/build/R"
    for m in Defs U1 U2; do
      /usr/bin/bwrap --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --bind "$d" "$d" --unshare-all --die-with-parent --new-session \
        --clearenv --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_PATH "$TC/lib/lean:$d/build" --chdir "$d/src" -- \
        "$TC/bin/lean" "R/$m.lean" -o "$d/build/R/$m.olean" > "$d/build/$m.log" 2>&1 || { echo "R.$m"; return 1; }
    done; return 0; }
  python3 -I "$FV/tools/compress/dedup/apply_edits.py" "$W/p" "$W/naive" "$W/naive.tsv" --srcdir src --copy > /dev/null 2>&1
  f=$(build "$W/naive") && no "the naive partial drop builds (expected 'Unknown identifier')" || {
    grep -q "Unknown identifier\|unknown identifier" "$W/naive/build/"*.log && ok "the naive partial drop breaks $f with 'Unknown identifier' (the class is real)" || no "naive drop failed differently: $(cat "$W/naive/build/"*.log | head -2 | tr '\n' ' ')"; }
  python3 -I "$FV/tools/compress/dedup/apply_edits.py" "$W/p" "$W/fixed" "$W/rn.out" --srcdir src --copy > /dev/null 2>&1
  f=$(build "$W/fixed") && ok "rename_deny's output builds (bar renamed everywhere, foo_alt untouched)" || no "rename_deny's output does not build ($f: $(head -2 "$W/fixed/build/"*.log | tr '\n' ' '))"
  grep -q "theorem bar : True" "$W/fixed/src/R/Defs.lean" && grep -q "foo_alt" "$W/fixed/src/R/U2.lean" && ok "content: bar_alt renamed, foo_alt kept" || no "content not as expected"
else
  echo "NOTE no official 4.33.1 toolchain / bwrap here: Lean confirmation skipped"
fi
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

#!/bin/bash
# compress-failure-classes/chainmerge-private-clash/run.sh [WORK] (Stage 3 tool guard)
# Failure class (attribute.py 'chain-merge clash'; seen in the full-RH C1 build: 8 groups 'private declaration `X` has
# already been declared'): a chain merge puts two modules into one, and a short name declared in both (one of them
# `private`) then clashes. Guard: tools/compress/scheme/cm_deny.py must deny the kept module of such a group and only
# of such a group. Lean part (no Mathlib, plain official lean in bwrap): the merged text fails with 'already been declared',
# the unmerged modules compile - so the guard's decision matches what the build would do.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-$(cd "$H/../../.." && pwd)}
W=${1:-/tmp/$USER-s3r-cm}; rm -rf "$W"; mkdir -p "$W/src/R"
TC=${TC433:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
bad=0; ok() { echo "PASS $*"; }; no() { echo "FAIL $*"; bad=1; }
# group G1 (clash): R.A and R.B both declare `R.helper`, R.A's `private` (private names are scoped to their module, so
# the two modules build separately) -> merged into R.B, the same full name is declared twice
printf 'namespace R\nprivate theorem helper : True := trivial\ntheorem useA : True := helper\nend R\n' > "$W/src/R/A.lean"
printf 'namespace R\nprivate theorem helper : 1 = 1 := rfl\ntheorem useB : 1 = 1 := helper\nend R\n' > "$W/src/R/B.lean"
# group G2 (clean): R.C and R.D declare different names -> merged into R.D, must NOT be denied
printf 'namespace R.C\nprivate theorem c1 : True := trivial\nend R.C\n' > "$W/src/R/C.lean"
printf 'namespace R.D\ntheorem d1 : True := trivial\nend R.D\n' > "$W/src/R/D.lean"
# group G3 (both public, same short name): not this class (cm_deny is about `private`), must NOT be denied
printf 'namespace R.E\ntheorem same : True := trivial\nend R.E\n' > "$W/src/R/E.lean"
printf 'namespace R.F\ntheorem same : True := trivial\nend R.F\n' > "$W/src/R/F.lean"
printf 'R.A R.B\nR.C R.D\nR.E R.F\n' > "$W/plan.tsv"
python3 -I "$FV/tools/compress/scheme/cm_deny.py" "$W/src" "$W/plan.tsv" "$W/deny.txt" > "$W/cm.out" 2>&1 || no "cm_deny.py exited non-zero: $(tail -1 "$W/cm.out")"
[ "$(cat "$W/deny.txt" 2>/dev/null)" = "R.B" ] && ok "cm_deny denies exactly the clashing group's kept module (R.B)" || no "cm_deny denied: '$(tr '\n' ' ' < "$W/deny.txt" 2>/dev/null)' (want R.B only)"
# Lean confirmation (skipped without the official 4.33.1 toolchain)
if [ -x "$TC/bin/lean" ] && [ -x /usr/bin/bwrap ]; then
  lean() { /usr/bin/bwrap --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --bind "$W" "$W" --unshare-all --die-with-parent --new-session --clearenv \
             --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_PATH "$TC/lib/lean" --chdir "$W" -- "$TC/bin/lean" "$@"; }
  cat "$W/src/R/A.lean" "$W/src/R/B.lean" > "$W/merged_G1.lean"     # what a chain merge of G1 would produce
  lean "$W/merged_G1.lean" > "$W/merged_G1.out" 2>&1
  grep -q "already been declared" "$W/merged_G1.out" && ok "the merged G1 module fails with 'already been declared' (the class is real)" || no "merged G1 did not fail as expected: $(head -2 "$W/merged_G1.out" | tr '\n' ' ')"
  lean "$W/src/R/A.lean" > /dev/null 2>&1 && lean "$W/src/R/B.lean" > /dev/null 2>&1 && ok "the unmerged modules compile (denying the merge keeps the tree buildable)" || no "unmerged modules do not compile"
  cat "$W/src/R/C.lean" "$W/src/R/D.lean" > "$W/merged_G2.lean"; lean "$W/merged_G2.lean" > /dev/null 2>&1 && ok "the clean group G2 merges and compiles (no false deny)" || no "clean group G2 failed to compile merged"
else
  echo "NOTE no official 4.33.1 toolchain / bwrap here: Lean confirmation skipped"
fi
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"

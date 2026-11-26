#!/bin/bash
# tests/build-importarts-empty/run.sh [SCRATCH] : component test of the opt-in sound build item
# `sound-fast-path=importarts-empty` (importArts = {} for module-system importers too, no up-front
# transitive importArts walk). On the module-system toy (build/test/projects/module-system: public / private / import all /
# meta imports) built by build/build.sh --preset B3:
#   1. with the item: BUILT, every setup.json has importArts {}, the plan is written in < 1 s
#   2. every output file (.olean/.olean.server/.olean.private/.ilean/.ir/.ir.sig/.c) is byte-identical to the build with
#      plain sound-fast-path (exact importArts)
#   3. a module using a PRIVATE def of a plain (non-`import all`) import fails in BOTH modes (no visibility change)
# Prints PASS/FAIL rows and RESULT; exit 0 iff all PASS.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FVD=$(cd "$H/../.." && pwd)
TC=${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}; WS=${FV_PACKAGES:-$(cd "$FVD/.." && pwd)/verify/challenge}
S=$(mktemp -d "${1:-${TMPDIR:-/tmp}}/build-importarts-empty.XXXXXX") || exit 2
trap 'chmod -R u+w "$S" 2>/dev/null; rm -rf "$S"' EXIT
pass=0; fail=0; ok() { echo "PASS $1"; pass=$((pass+1)); }; bad() { echo "FAIL $1"; fail=$((fail+1)); }
cp -a "$FVD/build/test/projects/module-system" "$S/pos"; cp -a "$S/pos" "$S/leak"
printf 'module\nimport M.B\npublic import M.A\ntheorem t_leak : m2priv = 1 := rfl\n' > "$S/leak/src/M/C.lean"
for p in pos leak; do for m in sfp ia; do
  cp -a "$S/$p" "$S/$p-$m"; it=sound-fast-path; [ $m = ia ] && it=sound-fast-path=importarts-empty
  "$FVD/build/build.sh" "$S/$p-$m" "$WS" "$TC" --log "$S/log-$p-$m" --preset B3 --unsafe $it --threads 4 > "$S/$p-$m.out" 2>&1
  echo $? > "$S/$p-$m.rc"
done; done
[ "$(cat $S/pos-ia.rc)" = 0 ] && ok "build-importarts-empty module-system toy BUILT with importarts-empty" || bad "build-importarts-empty importarts-empty build rc $(cat $S/pos-ia.rc): $(tail -2 $S/pos-ia.out | tr '\n' ' ' | cut -c1-200)"
[ "$(cat $S/pos-sfp.rc)" = 0 ] && ok "build-importarts-empty module-system toy BUILT with sound-fast-path" || bad "build-importarts-empty sound-fast-path build rc $(cat $S/pos-sfp.rc)"
ne=$(find "$S/pos-ia/.lake/build/ir" -name '*.setup.json' -print0 | xargs -0 grep -L '"importArts": {}' | wc -l)
ns=$(find "$S/pos-ia/.lake/build/ir" -name '*.setup.json' 2>/dev/null | wc -l)
[ "$ns" -gt 0 ] && [ "$ne" = 0 ] && ok "build-importarts-empty importarts-empty: $ns setup.json files, all with importArts {}" || bad "build-importarts-empty importarts-empty: $ne of $ns setup.json files with non-empty importArts"
nexact=$(find "$S/pos-sfp/.lake/build/ir" -name '*.setup.json' -print0 | xargs -0 grep -L '"importArts": {}' | wc -l)
[ "$nexact" -gt 0 ] && ok "build-importarts-empty control: plain sound-fast-path writes exact (non-empty) importArts ($nexact files)" || bad "build-importarts-empty control: plain sound-fast-path wrote no exact importArts"
d=0; n=0
while read -r f; do n=$((n+1)); cmp -s "$S/pos-sfp/.lake/build/$f" "$S/pos-ia/.lake/build/$f" || { d=$((d+1)); echo "  differs: $f"; }; done < <(cd "$S/pos-sfp/.lake/build" && find . -type f \( -name '*.olean*' -o -name '*.ilean' -o -name '*.ir' -o -name '*.ir.sig' -o -name '*.c' \) | sort)
[ $n -gt 0 ] && [ $d = 0 ] && ok "build-importarts-empty all $n output files byte-identical (exact importArts vs {})" || bad "build-importarts-empty $d of $n output files differ"
[ "$(cat $S/leak-sfp.rc)" = 1 ] && [ "$(cat $S/leak-ia.rc)" = 1 ] && ok "build-importarts-empty private def of a plain import: build fails in both modes" \
  || bad "build-importarts-empty visibility: rc sound-fast-path $(cat $S/leak-sfp.rc), importarts-empty $(cat $S/leak-ia.rc) (both must be 1)"
echo "RESULT pass=$pass fail=$fail"; [ $fail = 0 ]

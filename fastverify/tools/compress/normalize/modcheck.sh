#!/bin/bash
# modcheck.sh MODULE SRC_A SRC_B WORKDIR  -- elaborate two versions of one RH module against a full RH build tree
# (RHP = a full RH build tree, read-only) inside bwrap (no network, home hidden), then compare the two
# .olean files with OleanDiff (also in bwrap) and the A olean with the tree's own olean. Prints one RESULT line.
set -u
M=$1; SA=$2; SB=$3; W=$4
TC=${TC:-${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1}
P=${RHP:?full RH build tree with its .olean files, read-only (required)}
OD=${OLEANDIFF:-$(dirname "$(readlink -f "$0")")/oleandiff/OleanDiff.lean}
rel=${M//.//}
rm -rf "$W"; mkdir -p "$W/a" "$W/b" "$W/tmp"
cp "$SA" "$W/a/M.lean"; cp "$SB" "$W/b/M.lean"; cp "$OD" "$W/OleanDiff.lean"
LP=""
for pk in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do
  [ -d "$P/.lake/packages/$pk/.lake/build/lib/lean" ] && LP="$LP:$P/.lake/packages/$pk/.lake/build/lib/lean"
done
LP="${LP#:}:$P/.lake/build/lib/lean"
extra=""
case "$M" in GroundTheory.LocalFields.*|GroundTheory.GlobalFields.*) extra=',"synthInstance.maxHeartbeats":400000';; esac
printf '{"plugins":[],"package":"tree","options":{"relaxedAutoImplicit":false,"pp.unicode.fun":true,"maxSynthPendingDepth":3,"maxHeartbeats":4000000,"autoImplicit":false%s},"name":"%s","isModule":false,"importArts":{},"dynlibs":[]}\n' "$extra" "$M" > "$W/setup.json"
sbx() { env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home \
  --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --bind "$W" "$W" \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP" \
  --unshare-all --die-with-parent --new-session --chdir "$W" -- "$@"; }
for v in a b; do
  t0=$(date +%s.%N)
  sbx "$TC/bin/lean" --tstack=400000 "$W/$v/M.lean" -o "$W/$v/M.olean" --setup "$W/setup.json" > "$W/$v/stdout" 2> "$W/$v/stderr"
  echo $? > "$W/$v/rc"; t1=$(date +%s.%N); echo "$t1 - $t0" | bc > "$W/$v/secs"
done
ra=$(cat $W/a/rc); rb=$(cat $W/b/rc)
dab=NA; dat=NA
if [ "$ra" = 0 ] && [ "$rb" = 0 ]; then
  if cmp -s "$W/a/M.olean" "$W/b/M.olean"; then dab=BYTE-IDENTICAL; else
    sbx env LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$W/OleanDiff.lean" "$W/a/M.olean" "$W/b/M.olean" "$W/tmp" > "$W/diff_ab.txt" 2>&1
    dab=$(tail -1 "$W/diff_ab.txt" | cut -c1-200 | tr ' ' '_'); fi
  if cmp -s "$W/a/M.olean" "$P/.lake/build/lib/lean/$rel.olean"; then dat=BYTE-IDENTICAL; else dat=differs; fi
fi
echo "RESULT $M rcA=$ra rcB=$rb secsA=$(cat $W/a/secs) secsB=$(cat $W/b/secs) AvsB=$dab AvsTree=$dat"

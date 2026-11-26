#!/bin/bash
# mergecheck.sh "KEPT MEMBER1 MEMBER2 ..." MERGED_SRC WORKDIR -- elaborate a chain-merged module (named KEPT) against the
# full RH oleans (RHP, read-only) in bwrap, then OleanMergeDiff against the tree's oleans of KEPT and its members.
set -u
read -r -a G <<< "$1"; K=${G[0]}; SRC=$2; W=$3
TC=${TC:-${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1}
P=${RHP:?full RH build tree with its .olean files, read-only (required)}
OD=${OLEANMERGEDIFF:-$(dirname "$(readlink -f "$0")")/oleandiff/OleanMergeDiff.lean}
rm -rf "$W"; mkdir -p "$W/m"; cp "$SRC" "$W/m/M.lean"; cp "$OD" "$W/OleanMergeDiff.lean"
LP=""
for pk in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do
  [ -d "$P/.lake/packages/$pk/.lake/build/lib/lean" ] && LP="$LP:$P/.lake/packages/$pk/.lake/build/lib/lean"
done
LP="${LP#:}:$P/.lake/build/lib/lean"
extra=""
case "$K" in GroundTheory.LocalFields.*|GroundTheory.GlobalFields.*) extra=',"synthInstance.maxHeartbeats":400000';; esac
printf '{"plugins":[],"package":"tree","options":{"relaxedAutoImplicit":false,"pp.unicode.fun":true,"maxSynthPendingDepth":3,"maxHeartbeats":4000000,"autoImplicit":false%s},"name":"%s","isModule":false,"importArts":{},"dynlibs":[]}\n' "$extra" "$K" > "$W/setup.json"
sbx() { env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home \
  --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --bind "$W" "$W" \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP" \
  --unshare-all --die-with-parent --new-session --chdir "$W" -- "$@"; }
t0=$(date +%s.%N)
sbx "$TC/bin/lean" --tstack=400000 "$W/m/M.lean" -o "$W/m/M.olean" --setup "$W/setup.json" > "$W/m/stdout" 2> "$W/m/stderr"
rc=$?; t1=$(date +%s.%N)
args=()
for x in "${G[@]:1}" "$K"; do args+=("$P/.lake/build/lib/lean/${x//.//}.olean" "$x"); done
res=NA
if [ $rc = 0 ]; then
  sbx env LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$W/OleanMergeDiff.lean" "$W/m/M.olean" "$K" "${args[@]}" > "$W/diff.txt" 2>&1
  res=$(tail -1 "$W/diff.txt"); info=$(tail -2 "$W/diff.txt" | head -1 | tr ' ' '_')
else info=$(grep -m1 -o 'error: .*' "$W/m/stdout" | cut -c1-150 | tr ' ' '_'); fi
echo "RESULT $K members=$(( ${#G[@]} - 1 )) rc=$rc secs=$(echo "$t1 - $t0" | bc) verdict=$res $info"

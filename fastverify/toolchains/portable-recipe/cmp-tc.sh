#!/bin/bash
# cmp-tc.sh WS OUT N J EXCLUDE TC_A TC_B [ORDER]   - identity + CPU comparison of two toolchains on N Mathlib modules of WS
#   (deterministic sample, seed 37, minus the modules listed in EXCLUDE, e.g. the PGO training sample). Each pass elaborates
#   every module with one toolchain against the workspace's cached imports (same options as train-pgo.sh), J in parallel,
#   recording the .olean/.ilean sha256 and /usr/bin/time user+sys CPU per module. ORDER e.g. ABAB. Output OUT/summary.txt.
#   Every lean runs inside bwrap (--unshare-all: no network; home hidden; only /usr, WS, the toolchain(s) read-only and the
#   output dir writable) - Mathlib's metaprograms are fetched-project code (GOAL rule: untrusted code only in bwrap).
set -u
WS=$1 OUT=$2 N=$3 J=$4 EX=$5 A=$6 B=$7 ORDER=${8:-ABAB}
mkdir -p "$OUT"; OUT=$(readlink -f "$OUT"); WS=$(readlink -f "$WS"); M=$WS/.lake/packages/mathlib; LP=$(ls -d $WS/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':')
(cd "$M" && find Mathlib -name '*.lean' | sort) > "$OUT/all.txt"
python3 -c "import random; L=open('$OUT/all.txt').read().split(); ex=set(open('$EX').read().split()); random.seed(37); random.shuffle(L); print('\n'.join([x for x in L if x not in ex][:$N]))" > "$OUT/sample.txt"
k=0; : > "$OUT/summary.txt"
for c in $(echo "$ORDER" | grep -o .); do
  k=$((k+1)); case $c in A) TC=$A;; B) TC=$B;; esac; P=$OUT/p$k-$c; rm -rf "$P"; mkdir -p "$P"
  TC=$(readlink -f "$TC"); t0=$(date +%s.%N); export TC M P LP
  SBX=(bwrap --unshare-all --die-with-parent --new-session --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib
    --symlink usr/lib64 /lib64 --ro-bind /etc/ld.so.cache /etc/ld.so.cache --proc /proc --dev /dev --tmpfs /tmp --tmpfs /home
    --ro-bind "$(readlink -f "$WS")" "$(readlink -f "$WS")" --ro-bind "$(readlink -f "$TC")" "$(readlink -f "$TC")" --bind "$(readlink -f "$OUT")" "$(readlink -f "$OUT")" --chdir /tmp)
  "${SBX[@]}" xargs -a "$OUT/sample.txt" -P "$J" -I{} sh -c 'cd "$M" && f="{}"; h=$(echo "$f" | md5sum | cut -c1-16); \
    /usr/bin/time -f "%U %S %M" -o "$P/$h.time" env -i PATH=/usr/bin:/bin LEAN_PATH="$LP" timeout 900 "$TC/bin/lean" \
    -DmaxSynthPendingDepth=3 -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true -Dweak.linter.mathlibStandardSet=true \
    -R . "$f" -o "$P/$h.olean" -i "$P/$h.ilean" > "$P/$h.log" 2>&1; echo "$? $h $f" >> "$P/rc.txt"'
  w=$(python3 -c "import time; print(round(time.time()-$t0,1))")
  (cd "$P" && sha256sum *.olean *.ilean 2>/dev/null | sort -k2) > "$P.sha"
  cpu=$(cat "$P"/*.time | awk '{u+=$1; s+=$2} END{printf "%.1f", u+s}')
  echo "$k $c $(basename $(dirname $TC))/$(basename $TC) wall=${w}s cpu=${cpu}s rc0=$(grep -c '^0 ' $P/rc.txt)/$(wc -l < $P/rc.txt) sha=$(sha256sum < $P.sha | cut -c1-16)" | tee -a "$OUT/summary.txt"
  rm -f "$P"/*.olean "$P"/*.ilean
done
cat "$OUT/summary.txt"

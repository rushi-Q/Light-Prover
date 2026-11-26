#!/bin/bash
# train-pgo.sh TC WS OUT N J   - PGO training run for an instrumented toolchain (built with -DLEAN_PGO_GENERATE=ON):
#   elaborates N Mathlib modules (deterministic sample, seed 21) of the workspace WS (a Lake workspace whose packages carry
#   their built .oleans, e.g. Mathlib 31ce06ea for 4.37.0-rc1) with TC/bin/lean, J in parallel, each against the cached imports,
#   with Mathlib's lean options; raw profiles -> OUT/raw (%8m = online-merged pools), then llvm-profdata merge --sparse ->
#   OUT/lean.profdata. The elaborated outputs are discarded (only the code paths count).
#   Every lean runs inside bwrap (--unshare-all: no network; home hidden; only /usr, WS, the toolchain(s) read-only and the
#   output dir writable) - Mathlib's metaprograms are fetched-project code (rule: untrusted code only in bwrap).
#   llvm-profdata: $LLVM_PROFDATA, else the clang 18 environment of mkenv.sh ($FVCC_CENV18, default $PORT_WORK/cenv18).
set -u
TC=$1 WS=$2 OUT=$3 N=$4 J=$5; PD=${LLVM_PROFDATA:-${FVCC_CENV18:-${PORT_WORK:?work root of the portable-toolchain recipe, or set LLVM_PROFDATA or FVCC_CENV18 (required)}/cenv18}/bin/llvm-profdata}
mkdir -p "$OUT/raw" "$OUT/tmp"; OUT=$(readlink -f "$OUT"); WS=$(readlink -f "$WS"); TC=$(readlink -f "$TC"); M=$WS/.lake/packages/mathlib
LP=$(ls -d $WS/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':')
(cd "$M" && find Mathlib -name '*.lean' | sort) > "$OUT/all.txt"
python3 -c "import random,sys; L=open('$OUT/all.txt').read().split(); random.seed(21); random.shuffle(L); print('\n'.join(L[:$N]))" > "$OUT/sample.txt"
t0=$(date +%s)
SBX=(bwrap --unshare-all --die-with-parent --new-session --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib
  --symlink usr/lib64 /lib64 --ro-bind /etc/ld.so.cache /etc/ld.so.cache --proc /proc --dev /dev --tmpfs /tmp --tmpfs /home
  --ro-bind "$(readlink -f "$WS")" "$(readlink -f "$WS")" --ro-bind "$(readlink -f "$TC")" "$(readlink -f "$TC")" --bind "$(readlink -f "$OUT")" "$(readlink -f "$OUT")" --chdir /tmp)
export TC M OUT LP
"${SBX[@]}" xargs -a "$OUT/sample.txt" -P "$J" -I{} sh -c 'cd "$M" && f="{}"; o="$OUT/tmp/$(echo "$f" | md5sum | cut -c1-16)"; \
  env -i PATH=/usr/bin:/bin LEAN_PATH="$LP" LLVM_PROFILE_FILE="$OUT/raw/lean-%8m.profraw" timeout 600 "$TC/bin/lean" \
  -DmaxSynthPendingDepth=3 -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true -Dweak.linter.mathlibStandardSet=true \
  -R . "$f" -o "$o.olean" -i "$o.ilean" > "$o.log" 2>&1; echo "$? $f" >> "$OUT/rc.txt"; rm -f "$o.olean" "$o.ilean"'
echo "elaborated $N modules in $(( $(date +%s) - t0 )) s; rc histogram: $(cut -d' ' -f1 "$OUT/rc.txt" | sort | uniq -c | tr '\n' ' ')"
ls "$OUT/raw" | wc -l; du -sh "$OUT/raw"
"$PD" merge --sparse -o "$OUT/lean.profdata" "$OUT"/raw/*.profraw && ls -la "$OUT/lean.profdata" && sha256sum "$OUT/lean.profdata"

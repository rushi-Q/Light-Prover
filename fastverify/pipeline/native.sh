#!/bin/bash
# native.sh PKG_DIR OUT_DIR JOBS READY_FILE [BUILD_TC_ROOT]   (native code for the trusted package cache)
# BUILD_TC_ROOT = root of the toolchain the build uses (LEAN_TC); the lib is then also required to resolve ALL its undefined
# symbols in that toolchain's lib/lean/*.so (toolchain 7586a50cec resolves all 3,281, oleans identical) and to load there.
# Compiles every package ir/*.c shipped with the Mathlib cache (all packages, excl. Mathlib's Cache executable and any file
# with a main) with the OFFICIAL 4.33.1 leanc (-O1, largest first) into ONE shared lib and, if it links (--no-undefined) and
# loads (lean --load-dynlib --version), writes READY_FILE = '--load-dynlib=<lib>' which the scheduler appends to every later
# lean call (documented lean option; the interpreter then calls the native code of the package declarations instead of
# interpreting their IR; olean/ilean/c byte-identical in all A/Bs). Any failure => no READY_FILE => build stays interpreted.
# Runs in bwrap (no network; package cache + toolchain read-only, only OUT_DIR writable); only trusted inputs are compiled.
set -uo pipefail
PKG=$(readlink -f "$1"); OUT=$2; J=$3; READY=$4; BTC=${5:-}
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
mkdir -p "$OUT/obj"; OUT=$(readlink -f "$OUT")
t0=$(date +%s.%N)
( cd "$PKG" && find . -path '*/.lake/build/ir/*' -name '*.c' ! -path './mathlib/.lake/build/ir/Cache/*' -printf '%s %p\n' | sort -rn ) > "$OUT/cfiles.all"
: > "$OUT/cfiles.txt"; while read -r sz f; do grep -q '^int main(' "$PKG/$f" || echo "$f" >> "$OUT/cfiles.txt"; done < "$OUT/cfiles.all"
cat > "$OUT/cc.sh" <<CC
#!/bin/bash
cd "$PKG"; xargs -a "$OUT/cfiles.txt" -P "$J" -I{} sh -c 'o="$OUT/obj/\$(echo "{}" | sed "s|^\./||; s|/|_|g").o"; "$TC/bin/leanc" -c -O1 -DNDEBUG -DLEAN_EXPORTING "{}" -o "\$o" || echo "FAIL {}"'
cd "$OUT" && ls obj/*.o > objs.txt && "$TC/bin/leanc" -shared -o libpkgs.so.tmp @objs.txt -L"$TC/lib/lean" -lleanshared -lleanshared_1 -lleanshared_2 -lInit_shared -Wl,--no-undefined -Wl,-rpath,"$TC/lib/lean" && mv libpkgs.so.tmp libpkgs.so
CC
chmod +x "$OUT/cc.sh"
env -i bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin \
  --ro-bind /etc/ld.so.cache /etc/ld.so.cache --proc /proc --dev /dev --tmpfs /tmp \
  --ro-bind "$TC" "$TC" --ro-bind "$PKG" "$PKG" --bind "$OUT" "$OUT" --setenv HOME /tmp/home --setenv PATH /usr/bin:/bin \
  --chdir "$OUT" /bin/bash "$OUT/cc.sh" > "$OUT/cc.log" 2>&1
t1=$(date +%s.%N)
nf=$(wc -l < "$OUT/cfiles.txt"); no=$(ls "$OUT"/obj/*.o 2>/dev/null | wc -l); fails=$(grep -c '^FAIL' "$OUT/cc.log")
LEANBIN=$TC/bin/lean; symok=1
if [ -n "$BTC" ] && [ -s "$OUT/libpkgs.so" ]; then
  LEANBIN=$BTC/bin/lean
  nm -D --undefined-only "$OUT/libpkgs.so" | awk '{print $NF}' | sed 's/@.*//' | sort -u > "$OUT/undef.txt"
  for l in "$BTC"/lib/lean/*.so "$BTC"/lib/*.so /lib/x86_64-linux-gnu/libc.so.6 /lib/x86_64-linux-gnu/libm.so.6 /lib/x86_64-linux-gnu/libgcc_s.so.1; do [ -e "$l" ] && nm -D --defined-only "$l" 2>/dev/null; done | awk '{print $NF}' | sed 's/@.*//' | sort -u > "$OUT/tcdef.txt"
  missing=$(comm -23 "$OUT/undef.txt" "$OUT/tcdef.txt" | grep -v -E '^(__cxa_finalize|__deregister_frame_info|__register_frame_info|__gmon_start__|_ITM_.*|_Jv_RegisterClasses)$' | head -20)
  [ -n "$missing" ] && { symok=0; echo "native: symbols missing in $BTC: $(echo $missing | cut -c1-300)" >> "$OUT/check.log"; }
fi
if [ -s "$OUT/libpkgs.so" ] && [ "$no" -eq "$nf" ] && [ "$fails" -eq 0 ] && [ $symok = 1 ] && "$LEANBIN" --load-dynlib="$OUT/libpkgs.so" --version >> "$OUT/check.log" 2>&1; then
  echo "--load-dynlib=$OUT/libpkgs.so" > "$READY.tmp" && mv "$READY.tmp" "$READY"
  echo "native: READY $nf files -> $(stat -c %s "$OUT/libpkgs.so") bytes in $(echo "$t1 - $t0" | bc | cut -c1-6) s ($J jobs)"
else
  echo "native: NOT used (files=$nf objs=$no fails=$fails so=$(stat -c %s "$OUT/libpkgs.so" 2>/dev/null)); $(tail -3 "$OUT/cc.log" | tr '\n' ' ') $(tail -2 "$OUT/check.log" 2>/dev/null | tr '\n' ' ')"
fi
rm -rf "$OUT/obj"

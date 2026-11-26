#!/bin/bash
# build/native.sh BINDS_TSV OUT_DIR JOBS TOOLCHAIN_PREFIX   (fastverify build option B3 --unsafe native-pkg; ported
# from pipeline/native.sh)
# Compiles the C code that ships with the TRUSTED dependency packages (every <pkg>/.lake/build/ir/**/*.c of the packages
# listed in BINDS_TSV, i.e. the pinned workspace, excluding files with a main) with the toolchain's own leanc (-O1) into
# ONE shared library and, if it links (--no-undefined) and loads (lean --load-dynlib=LIB --version), writes
# OUT_DIR/ready = "--load-dynlib=OUT_DIR/libpkgs.so"; sched.py then adds that documented lean option to every lean it
# starts afterwards (the interpreter calls the native code of package declarations instead of interpreting their IR).
# UNSAFE (opt-in only): native code changes heartbeat accounting (finding 015: official timeout vs fast pass) and crashed
# lean on module-system files (057); the build is then not the official one. Any failure here => no ready file => the
# build simply stays interpreted. Runs in bwrap: no network, packages + toolchain read-only, only OUT_DIR writable.
set -uo pipefail
BINDS=$1; OUT=$2; J=$3; TC=$(readlink -f "$4")
mkdir -p "$OUT/obj"; OUT=$(readlink -f "$OUT")
t0=$(date +%s.%N)
: > "$OUT/cfiles.txt"
# S4 masks of every untrusted sandbox (all top-level dirs except the system ones hidden), and
# only plain absolute binds.tsv sources (lib/manifest.py: trusted workspace checkouts) are used
MASKS=(); RO=(); for d in /*; do
  [ -d "$d" ] && [ ! -L "$d" ] || continue
  case "${d#/}" in bin|sbin|lib|lib32|lib64|libx32|usr|etc|dev|proc|sys|nix|gnu|home|root|tmp|run|var) ;; *) MASKS+=(--tmpfs "$d"); RO+=(--remount-ro "$d") ;; esac
done
plainsrc() { case "$1" in /*) ;; *) return 1 ;; esac; case "$1/" in */../*|*/./*|*//*) return 1 ;; esac
             case "$1" in *[[:cntrl:]]*) return 1 ;; esac; return 0; }
while IFS=$'\t' read -r src dst; do
  plainsrc "$src" || continue
  [ -d "$src/.lake/build/ir" ] || continue
  find "$src/.lake/build/ir" -name '*.c' ! -path '*/ir/Cache/*' -printf '%s %p\n'
done < "$BINDS" | sort -rn | while read -r sz f; do grep -q '^int main(' "$f" || echo "$f"; done > "$OUT/cfiles.txt"
nf=$(wc -l < "$OUT/cfiles.txt")
[ "$nf" -gt 0 ] || { echo "native: no package C files"; exit 0; }
cat > "$OUT/cc.sh" <<CC
#!/bin/bash
xargs -a "$OUT/cfiles.txt" -d '\n' -P "$J" -n 1 sh -c 'o="$OUT/obj/\$(printf "%s" "\$1" | md5sum | cut -c1-32).o"; "$TC/bin/leanc" -c -O1 -DNDEBUG -DLEAN_EXPORTING "\$1" -o "\$o" || echo "FAIL \$1"' _
cd "$OUT" && ls obj/*.o > objs.txt && "$TC/bin/leanc" -shared -o libpkgs.so.tmp @objs.txt -L"$TC/lib/lean" -lleanshared -lleanshared_1 -lleanshared_2 -lInit_shared -Wl,--no-undefined -Wl,-rpath,"$TC/lib/lean" && mv libpkgs.so.tmp libpkgs.so
CC
chmod +x "$OUT/cc.sh"
ROB=(); while IFS=$'\t' read -r src dst; do plainsrc "$src" && ROB+=(--ro-bind "$src" "$src"); done < "$BINDS"
SBX=(env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --tmpfs /run --tmpfs /var "${MASKS[@]}" --dev /dev --proc /proc
     --ro-bind "$TC" "$TC")
"${SBX[@]}" "${ROB[@]}" --bind "$OUT" "$OUT" ${RO[@]+"${RO[@]}"} --unshare-all --die-with-parent --new-session --clearenv \
  --setenv HOME /tmp --setenv PATH /usr/bin:/bin --chdir "$OUT" /bin/bash "$OUT/cc.sh" > "$OUT/cc.log" 2>&1
t1=$(date +%s.%N)
no=$(ls "$OUT"/obj/*.o 2>/dev/null | wc -l); fails=$(grep -c '^FAIL' "$OUT/cc.log")
# the load test of the compiled library runs in the same sandbox (read-only, no network), not on the host
if [ -s "$OUT/libpkgs.so" ] && [ "$no" -eq "$nf" ] && [ "$fails" -eq 0 ] \
   && "${SBX[@]}" --ro-bind "$OUT" "$OUT" ${RO[@]+"${RO[@]}"} --unshare-all --die-with-parent --new-session --clearenv --setenv HOME /tmp \
        --setenv PATH /usr/bin:/bin --chdir "$OUT" "$TC/bin/lean" --load-dynlib="$OUT/libpkgs.so" --version >> "$OUT/check.log" 2>&1; then
  echo "--load-dynlib=$OUT/libpkgs.so" > "$OUT/ready.tmp" && mv "$OUT/ready.tmp" "$OUT/ready"
  echo "native: READY $nf files -> $(stat -c %s "$OUT/libpkgs.so") bytes in $(echo "$t1 - $t0" | bc | cut -c1-6) s ($J jobs)"
else
  echo "native: NOT used (files=$nf objs=$no fails=$fails); $(tail -3 "$OUT/cc.log" | tr '\n' ' ')"
fi
rm -rf "$OUT/obj"

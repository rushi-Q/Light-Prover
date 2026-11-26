#!/bin/bash
# rebuild-pchk.sh SRC OUT [TC36]  - rebuild ccmp + pleanchecker (release kernel libraries) from the pchk sources SRC
# (fastverify/check/sound/src) with the OFFICIAL Lean 4.36.0 toolchain, exactly as check/sound/README.md
# documents: `PATH=$TC36/bin:/usr/bin:/bin lake build pleanchecker ccmp`. Clean environment (env -i), fresh copy of the
# sources (no .lake), no network needed (no dependencies). Prints host facts and the sha256 of every output + object.
set -eu
SRC=$1; OUT=$2; TC36=${3:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}
mkdir -p "$OUT"; rm -rf "$OUT/src"; mkdir -p "$OUT/src"
( cd "$SRC" && tar --exclude=.lake -cf - . ) | tar -xf - -C "$OUT/src"
{
  echo "host: $(hostname)  date: $(date -u +%FT%TZ)"
  echo "os: $(. /etc/os-release; echo "$PRETTY_NAME")  glibc: $(ldd --version | head -1)"
  echo "tc36: $TC36"; "$TC36/bin/lean" --version; echo "lake: $("$TC36/bin/lake" --version)"
  echo "src tree sha256 (sorted file list):"; ( cd "$OUT/src" && find . -type f | sort | xargs sha256sum | sha256sum )
} | tee "$OUT/host.txt"
t0=$(date +%s)
env -i PATH="$TC36/bin:/usr/bin:/bin" HOME="$OUT/home" LANG=C.UTF-8 "$TC36/bin/lake" -d "$OUT/src" build pleanchecker ccmp > "$OUT/build.log" 2>&1
rc=$?; echo "lake build rc=$rc in $(( $(date +%s) - t0 )) s" | tee -a "$OUT/host.txt"
[ $rc = 0 ] || { tail -30 "$OUT/build.log"; exit 1; }
( cd "$OUT/src/.lake/build" && sha256sum bin/ccmp bin/pleanchecker $(find ir -name '*.o.export' -o -name '*.o.noexport' -o -name '*.c' -o -name '*.olean' | sort) ) > "$OUT/SHA256SUMS.all"
grep -E 'bin/(ccmp|pleanchecker)$' "$OUT/SHA256SUMS.all" | tee -a "$OUT/host.txt"
echo "objects: $(grep -c '\.o\.' "$OUT/SHA256SUMS.all")  c files: $(grep -c '\.c$' "$OUT/SHA256SUMS.all")" | tee -a "$OUT/host.txt"

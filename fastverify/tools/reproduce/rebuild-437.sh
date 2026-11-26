#!/bin/bash
# rebuild-437.sh SRC TC OUT  - fresh-directory Lake rebuild of the 4.37 trusted check (ccmp-437, pleanchecker-437) from SRC
# (a check/sound/src-437 tree; its .lake is NOT copied) with the official toolchain TC (verified against fastverify/toolchains
# by the caller), env -i, offline. Prints sha256 of the two binaries + their glibc/libstdc++ needs.
set -euo pipefail
SRC=$1; TC=$2; OUT=$3
mkdir -p "$OUT"; rm -rf "$OUT/src" "$OUT/home"; mkdir -p "$OUT/home"
rsync -a --exclude .lake "$SRC"/ "$OUT/src"/
( cd "$OUT/src" && find . -type f ! -path './.lake/*' | sort | xargs sha256sum ) > "$OUT/SHA256SUMS.src"
echo "host $(hostname) $(date -u +%FT%TZ) glibc $(ldd --version | head -1)"; "$TC/bin/lean" --version
t0=$(date +%s)
env -i PATH="$TC/bin:/usr/bin:/bin" HOME="$OUT/home" LANG=C.UTF-8 "$TC/bin/lake" -d "$OUT/src" build pleanchecker ccmp 2>&1 | tail -3
echo "build $(( $(date +%s) - t0 )) s"
for b in ccmp pleanchecker; do
  f="$OUT/src/.lake/build/bin/$b"
  echo "$b $(sha256sum "$f" | cut -d' ' -f1) size $(stat -c %s "$f")"
  echo "  NEEDED: $(readelf -d "$f" | awk '/NEEDED/{gsub(/[\[\]]/,"",$5); printf "%s ", $5}')"
  echo "  max GLIBC: $(objdump -T "$f" | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1)  GLIBCXX: $(objdump -T "$f" | grep -o 'GLIBCXX_[0-9.]*' | sort -uV | tail -1 || true)"
done
sha256sum "$OUT/src/.lake/build/bin/ccmp" "$OUT/src/.lake/build/bin/pleanchecker" > "$OUT/SHA256SUMS.bin"

#!/bin/bash
# build.sh [--install] : reproducible static build of prechk from src/prechk.cpp (no network, no third-party code).
# Portable: fully static, default x86-64 target (no -march=native). Prints the sha256 of the result.
# --install copies the result to $PRECHK_BIN (pins.env; node-local, outside the package) and records its sha256 in
# SHA256SUMS (maintainer action). The package itself ships only source + recipe + sha256.
set -euo pipefail
H=$(cd "$(dirname "$0")" && pwd)
CXX=${CXX:-g++}
OUT=$(mktemp -d)/prechk
"$CXX" -O2 -std=c++17 -pthread -static -Wl,--whole-archive -lpthread -Wl,--no-whole-archive \
  -o "$OUT" "$H/src/prechk.cpp" 2> "$OUT.log" || { cat "$OUT.log"; exit 1; }
echo "compiler: $("$CXX" --version | head -1)"
echo "flags: -O2 -std=c++17 -pthread -static (x86-64 baseline)"
echo "src sha256: $(sha256sum "$H/src/prechk.cpp" | cut -d' ' -f1)"
echo "bin sha256: $(sha256sum "$OUT" | cut -d' ' -f1)  $OUT"
"$OUT" --version
if [ "${1:-}" = --install ]; then
  DIR=${PRECHK_DIR:-/scratch/fastverify-next/prechk}
  VER=$("$OUT" --version | awk '{print $2}'); SHA=$(sha256sum "$OUT" | cut -d' ' -f1)
  DST=$DIR/prechk-$VER-${SHA:0:9}
  mkdir -p "$DIR"
  install -m 0555 "$OUT" "$DST.new" && mv -f "$DST.new" "$DST"
  sed -i "s|^PRECHK_BIN=.*|PRECHK_BIN=$DST|" "$H/pins.env"
  { echo "$SHA  prechk"; ( cd "$H" && sha256sum src/prechk.cpp ); } > "$H/SHA256SUMS"
  echo "installed $DST (this host only: copy it to every host, e.g. tools/deploy.sh); pins.env + SHA256SUMS updated"
fi

#!/bin/bash
# portable-tc.sh pack NAME [OUTDIR]          -> OUTDIR/NAME.tar.zst + .sha256 from $SCRATCH/fastverify-next/tc/NAME (verified first)
# portable-tc.sh install TARBALL [TCDIR]     -> unpack into TCDIR/NAME (default $SCRATCH/fastverify-next/tc), read-only, then
#                                               lib/toolchain.py verify-unofficial against the package's pinned manifest
# For hosts that cannot build the portable trees themselves (CI runners, laptops, clusters): the tarball is just the pinned
# tree; trust comes from the file-by-file manifest in toolchains/unofficial/NAME.json, checked after unpacking (and again by
# build.sh before every use). Nothing is fetched from the network by this script.
set -euo pipefail
D=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd); S=${SCRATCH:-/scratch}
case ${1:-} in
  pack)
    n=$2; out=${3:-.}; t=$S/fastverify-next/tc/$n
    python3 -I "$D/lib/toolchain.py" verify-unofficial "$t" "$n" > /dev/null || { echo "portable-tc: $t does not verify" >&2; exit 2; }
    tar -C "$S/fastverify-next/tc" --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner -cf - "$n" | zstd -q -T8 -19 -o "$out/$n.tar.zst"
    (cd "$out" && sha256sum "$n.tar.zst" > "$n.tar.zst.sha256" && cat "$n.tar.zst.sha256") ;;
  install)
    tb=$(readlink -f "$2"); dst=${3:-$S/fastverify-next/tc}; n=$(basename "$tb" .tar.zst)
    [ -f "$D/toolchains/unofficial/$n.json" ] || { echo "portable-tc: no pinned manifest toolchains/unofficial/$n.json" >&2; exit 2; }
    [ -e "$dst/$n" ] && { echo "portable-tc: $dst/$n exists" >&2; exit 2; }
    mkdir -p "$dst"; tmp=$(mktemp -d "$dst/.$n.XXXXXX")
    zstd -dc "$tb" | tar -C "$tmp" -xf - --no-same-owner
    [ -d "$tmp/$n" ] || { rm -rf "$tmp"; echo "portable-tc: tarball does not contain $n/" >&2; exit 2; }
    chmod u+w "$tmp/$n"; mv "$tmp/$n" "$dst/$n"; rmdir "$tmp"; chmod -R a-w "$dst/$n"
    if python3 -I "$D/lib/toolchain.py" verify-unofficial "$dst/$n" "$n" > /dev/null; then echo "installed + verified: $dst/$n"
    else chmod -R u+w "$dst/$n"; rm -rf "$dst/$n"; echo "portable-tc: $n does not match its pinned manifest (removed)" >&2; exit 2; fi ;;
  *) sed -n 2,7p "$0"; exit 2 ;;
esac

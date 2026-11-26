#!/bin/bash
# snapshot_pkg.sh [SRC_PKG] -> prints the path of a frozen copy of the package (without tests/, pipeline/ and the excluded work
# dirs) on this host, named by the sha256 of check/sound/{check-sound.sh,pins.env} + lib/fastverify.py: test a snapshot, never the live tree
set -eu
. "$(dirname "$(readlink -f "$0")")/common.sh"
SRC=${1:-$FV}
T=$(mktemp -d "$W/pkg.tmp.XXXXXX")
rsync -a --exclude tests --exclude pipeline --exclude 'review-*' --exclude __pycache__ "$SRC/" "$T/fastverify/"
K=$(cat "$T/fastverify/check/sound/check-sound.sh" "$T/fastverify/check/sound/pins.env" "$T/fastverify/lib/fastverify.py" | sha256sum | cut -c1-16)
D=$W/pkg/$K
if [ -d "$D" ]; then rm -rf "$T"; else mkdir -p "$W/pkg"; mv "$T" "$D"; fi
echo "$D/fastverify"

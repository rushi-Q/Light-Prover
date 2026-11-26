#!/bin/bash
# tools/build-lean4export.sh VERSION TOOLCHAIN_PREFIX DEST [LEAN4EXPORT_CLONE]   (used by tools/addrelease.py)
# Build the OFFICIAL lean4export for Lean VERSION: leanprover/lean4export at tag vVERSION (a patch / rc release without its
# own tag uses the tag of its line vX.Y.0), from the clone <repository root>/env/tools/lean4export unless LEAN4EXPORT_CLONE is given (read-only use; `git archive`),
# with the release's own official lake, OFFLINE inside bwrap (no network, home hidden, only DEST writable).
# Output: DEST/.lake/build/bin/lean4export (+ .provenance: tag, commit, toolchain, sha256). Exit 0 = built.
set -euo pipefail
V=${1#v}; TC=$(realpath "$2"); DEST=$3
PKG=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); SRC=${4:-$(dirname "$PKG")/env/tools/lean4export}
[ -x "$TC/bin/lake" ] || { echo "build-lean4export: no lake in $TC" >&2; exit 2; }
[ -d "$SRC/.git" ] || { echo "build-lean4export: lean4export clone $SRC missing" >&2; exit 2; }
TAG=v$V
if ! git -C "$SRC" rev-parse -q --verify "refs/tags/$TAG" >/dev/null; then
  TAG=v$(echo "$V" | sed -E 's/^([0-9]+\.[0-9]+)\..*/\1.0/')
  git -C "$SRC" rev-parse -q --verify "refs/tags/$TAG" >/dev/null || { echo "build-lean4export: no lean4export tag for $V" >&2; exit 2; }
fi
rm -rf "$DEST"; mkdir -p "$DEST"; DEST=$(realpath "$DEST")
git -C "$SRC" -c gc.auto=0 archive "$TAG" | tar -x -C "$DEST"
env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --dir /tmp/home --tmpfs /run --dev /dev --proc /proc \
  --ro-bind "$TC" "$TC" --bind "$DEST" "$DEST" --unshare-all --die-with-parent --new-session --chdir "$DEST" \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 -- lake build lean4export >&2
B="$DEST/.lake/build/bin/lean4export"
echo "official lean4export $TAG (commit $(git -C "$SRC" rev-parse "$TAG^{commit}" | cut -c1-12)) built offline in bwrap by the official Lean $V lake ($("$TC/bin/lean" --githash | cut -c1-12)); sha256 $(sha256sum "$B" | cut -d' ' -f1)" > "$B.provenance"
cat "$B.provenance"

#!/bin/bash
# broot.sh ROOTFS [--bind SRC DST]... -- CMD...   run CMD inside an old-glibc userland (e.g. manylinux_2_28 rootfs) with bwrap
# (unprivileged, like `docker run` without the daemon): $PORT_WORK visible at its own path (the recipe's work root: sources,
# builds, compiler environments), /dev /proc /tmp fresh, host network (downloads only).
set -euo pipefail
W=${PORT_WORK:?work root of the portable-toolchain recipe (required)}
R=$1; shift; B=()
while [ "$1" != "--" ]; do [ "$1" = --bind ] && { B+=(--bind "$2" "$3"); shift 3; continue; }; echo "broot: bad arg $1" >&2; exit 2; done; shift
exec bwrap --bind "$R" / --dev /dev --proc /proc --tmpfs /tmp --bind "$W" "$W" \
  --ro-bind /etc/resolv.conf /etc/resolv.conf "${B[@]}" --unshare-pid --die-with-parent \
  --setenv HOME /tmp --setenv PATH /opt/fvcc/bin:/opt/rh/gcc-toolset-13/root/usr/bin:/usr/local/bin:/usr/bin:/bin \
  --setenv LANG C --setenv LC_ALL C --setenv TZ UTC "$@"

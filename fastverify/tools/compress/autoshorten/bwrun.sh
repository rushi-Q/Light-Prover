#!/bin/bash
# bwrun.sh PROJ WORKDIR CMD...  -- run CMD inside bwrap (read-only /, no network, clean env) with LEAN_PATH = the oleans of
# build tree PROJ and the official 4.33.1 toolchain on PATH; WORKDIR (and TOOLS dir, read-only) bound. (S4 sandbox)
# BWRUN_PKGS=WS (optional): a Lake workspace whose .lake/packages/*/.lake/build/lib/lean provide the dependencies
# (fastverify builds bind the trusted workspace's packages instead of copying them into PROJ).
set -e
PROJ=$1; WD=$2; shift 2
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
TOOLS=$(dirname $(readlink -f $0))
LP=$(ls -d $PROJ/.lake/packages/*/.lake/build/lib/lean 2>/dev/null | tr '\n' ':')$PROJ/.lake/build/lib/lean
XB=()
if [ -n "${BWRUN_PKGS:-}" ]; then
  LP=$(ls -d $BWRUN_PKGS/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':')$LP; XB=(--ro-bind "$BWRUN_PKGS" "$BWRUN_PKGS")
fi
exec env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home \
  --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --ro-bind "$PROJ" "$PROJ" "${XB[@]}" \
  --ro-bind "$TOOLS" "$TOOLS" --bind "$WD" "$WD" --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home \
  --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP" --unshare-all --die-with-parent --new-session --chdir "$WD" -- "$@"

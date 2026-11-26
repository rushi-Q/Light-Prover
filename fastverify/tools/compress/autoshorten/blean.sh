#!/bin/bash
# blean.sh PROJ WORKDIR FILE.lean [lean args...]  -- elaborate FILE (inside WORKDIR) with the official 4.33.1 lean against
# the oleans of build tree PROJ, inside bwrap without network (S4). Output: lean's stdout/stderr.
# Project options: $BLEAN_OPTS (lean -D flags) if set, else RH's lakefile options.
set -e
PROJ=$1; WD=$2; F=$3; shift 3
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
LP=$(ls -d $PROJ/.lake/packages/*/.lake/build/lib/lean 2>/dev/null | tr '\n' ':')$PROJ/.lake/build/lib/lean
XB=()
if [ -n "${BWRUN_PKGS:-}" ]; then   # dependencies from a Lake workspace (see bwrun.sh)
  LP=$(ls -d $BWRUN_PKGS/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':')$LP; XB=(--ro-bind "$BWRUN_PKGS" "$BWRUN_PKGS")
fi
OPTS=${BLEAN_OPTS:-"-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true -DmaxHeartbeats=4000000 --tstack=400000"}
exec env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home \
  --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --ro-bind "$PROJ" "$PROJ" "${XB[@]}" \
  --bind "$WD" "$WD" --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 \
  --setenv LEAN_PATH "$LP" --unshare-all --die-with-parent --new-session --chdir "$WD" -- \
  "$TC/bin/lean" $OPTS "$@" "$F"

#!/bin/bash
# leandev.sh DIR FILE.lean [more lean args]: elaborate FILE (relative to DIR) with the official Lean 4.33.1 + the trusted
# Mathlib 0df444a workspace, inside bwrap (no network, home hidden, everything read-only except DIR). Used to check that generated proofs
# elaborate and that generated proofs elaborate before the measured runs (which go through bin/fastverify).
set -eu
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}
ELAN_HOME=${ELAN_HOME:-$HOME/.elan}
D=$(realpath "$1"); shift
T=${LEANTC:-$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1}
WS=${LEANWS:-${FV_PACKAGES:-$LIGHT_LEAN/verify/challenge}/.lake/packages}
LP=""; for p in "$WS"/*/.lake/build/lib/lean; do LP="$LP$p:"; done; LP="$LP$T/lib/lean"
exec env -i bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
  --ro-bind /etc/ld.so.cache /etc/ld.so.cache --proc /proc --dev /dev --tmpfs /tmp --tmpfs /home \
  --ro-bind "$T" "$T" --ro-bind "$WS" "$WS" --bind "$D" "$D" \
  --setenv HOME /tmp --setenv PATH "$T/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP" \
  --chdir "$D" "$T/bin/lean" "$@"

#!/bin/bash
# wsbuild.sh WS CMD... : run CMD (e.g. `lake build +X`) in workspace WS inside bwrap: no network, read-only /, home hidden
# (except the trusted workspace TW, read-only, so that symlinked packages resolve), only WS writable, the official v4.33.1
# toolchain ($TC). Used to build the trusted workspace's extra dependency packages offline.
set -u
WS=$(realpath "$1"); shift
TC=${TC:-$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1}
TWB=(); [ -n "${TW:-}" ] && TWB=(--ro-bind "$TW" "$TW")
cd "$WS" || exit 2
exec env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home \
  --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --unshare-all --die-with-parent --new-session \
  --ro-bind "$TC" "$TC" "${TWB[@]}" --bind "$WS" "$WS" --chdir "$WS" \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 -- "$@"

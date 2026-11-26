#!/bin/bash
# lsand.sh DIR CMD...   run CMD (e.g. lean Solution.lean) inside bwrap: no network, / read-only, home hidden, only DIR writable,
# Lean 4.33.1 on PATH. For quick elaboration tests of the (untrusted) cheat cases. LSAND_RO="p1:p2" = extra read-only binds.
set -u
D=$(readlink -f "$1"); shift
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
RO=()
IFS=: read -r -a extra <<< "${LSAND_RO:-}"
for p in "${extra[@]}"; do [ -n "$p" ] && RO+=(--ro-bind "$p" "$p"); done
exec env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --tmpfs /run --tmpfs /var --dev /dev --proc /proc \
  --ro-bind "$TC" "$TC" "${RO[@]}" --bind "$D" "$D" --unshare-all --die-with-parent --new-session --clearenv \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp --setenv LANG C.UTF-8 --chdir "$D" -- "$@"

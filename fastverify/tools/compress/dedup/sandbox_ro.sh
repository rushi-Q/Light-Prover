#!/bin/bash
# sandbox_ro.sh OUTDIR RO_DIR[:RO_DIR...] -- cmd...   bwrap: no network, read-only system + toolchain + RO dirs,
# only OUTDIR writable. For tools that READ untrusted build artifacts (oleans) without modifying them.
set -euo pipefail
O=$1; RO=$2; shift 3
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
T=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$O"
args=()
IFS=: read -ra dirs <<< "$RO"
for d in "${dirs[@]}"; do args+=(--ro-bind "$d" "$d"); done
exec env -i bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin \
  --ro-bind /etc/ld.so.cache /etc/ld.so.cache --proc /proc --dev /dev --tmpfs /tmp \
  --ro-bind "$TC" "$TC" --ro-bind "$T" "$T" "${args[@]}" --bind "$O" "$O" \
  --setenv HOME /tmp/home --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 --chdir "$O" \
  nice -n 10 "$@"

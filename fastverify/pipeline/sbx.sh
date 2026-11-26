#!/bin/bash
# Usage: sandbox_run.sh <build_dir> <rw_log_dir> <toolchain_wrapped_dir> -- <cmd...>  (same sandbox as sandbox_lake.sh)
# Runs lake inside bwrap: no network, read-only system + toolchain + package deps; only build dir and log dir writable.
# O01 copy of env/sandbox_run.sh: + optional READ-ONLY bind of $SBX_RO (the trusted Mathlib package cache), so the 7.6 GB
# package tree need not be copied into the build dir. Everything else identical.
set -euo pipefail
B=$1; L=$2; TCW=$3; shift 4
REAL=$(readlink -f "$TCW/lib/..")   # real toolchain root (lib is a symlink into it)
REAL=$(dirname "$(readlink "$TCW/lib")")
mkdir -p "$L"
exec env -i bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin \
  --ro-bind /etc/ld.so.cache /etc/ld.so.cache --ro-bind-try /etc/localtime /etc/localtime \
  --ro-bind-try /etc/passwd /etc/passwd --ro-bind-try /etc/group /etc/group \
  --proc /proc --dev /dev --tmpfs /tmp \
  --ro-bind "$REAL" "$REAL" --ro-bind "$TCW" "$TCW" \
  --ro-bind-try "${SBX_RO:-/nonexistent}" "${SBX_RO:-/nonexistent}" \
  --ro-bind-try "${SBX_RO2:-/nonexistent}" "${SBX_RO2:-/nonexistent}" \
  --bind "$B" "$B" \
  --bind "$L" "$L" \
  --setenv HOME /tmp/home --setenv PATH "$TCW/bin:/usr/bin:/bin" --setenv TOOLWRAP_LOG "$L/tools.jsonl" \
  --setenv LANG C.UTF-8 \
  --chdir "$B" \
  nice -n 10 "$@"

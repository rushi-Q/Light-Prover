#!/bin/bash
# kx.sh EXTRA_RO_DIR 'CMD' : the krun sandbox (no network, home invisible, inputs read-only, private /tmp) plus one
# extra read-only bind (node-local scratch dir holding big generated exports)
set -u
X=$1; shift
R=${FV_REPRO_DIR:-$LIGHT_LEAN/repro}; mkdir -p ${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-ktmp
T=$(mktemp -d ${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-ktmp/XXXXXX) || exit 3
trap 'rm -rf "$T"' EXIT
env -i bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin \
  --ro-bind /etc/ld.so.cache /etc/ld.so.cache --ro-bind-try /etc/passwd /etc/passwd --ro-bind-try /etc/alternatives /etc/alternatives \
  --proc /proc --dev /dev --tmpfs /home --bind "$T" /tmp \
  --ro-bind /scratch/bench-inputs /scratch/bench-inputs --ro-bind $R/K $R/K --ro-bind $R/C $R/C --ro-bind-try $R/X $R/X --ro-bind-try /scratch/fastverify /scratch/fastverify \
  --ro-bind-try $ELAN_HOME/toolchains/leanprover--lean4---v4.36.0 $ELAN_HOME/toolchains/leanprover--lean4---v4.36.0 \
  --ro-bind "$X" "$X" \
  --setenv HOME /tmp --setenv TMPDIR /tmp --setenv PATH /usr/bin:/bin --setenv LANG C.UTF-8 \
  --chdir /tmp /bin/sh -c "$*"

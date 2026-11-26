#!/bin/bash
# sbuild.sh DIR 'CMD' : run CMD offline in a bwrap sandbox: no network, home hidden, system read-only, only DIR writable,
# the official Lean 4.36 toolchain ($TC36) and a rustup/cargo installation ($RUST_HOME_DIR with rustup/ and cargo/;
# crates must have been fetched beforehand with `cargo fetch --locked`) bound read-only (cargo registry writable for locks).
#   env: TC36 (default ~/.elan/toolchains/leanprover--lean4---v4.36.0), RUST_HOME_DIR (default /scratch/kdev),
#        RUST_TOOLCHAIN (default 1.97.1)
set -eu
K=${RUST_HOME_DIR:-/scratch/kdev}; SRC=$(realpath "$1"); shift
TC=${TC36:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}
exec env -i bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin \
  --ro-bind /etc/ld.so.cache /etc/ld.so.cache --ro-bind-try /etc/passwd /etc/passwd --ro-bind-try /etc/alternatives /etc/alternatives \
  --proc /proc --dev /dev --tmpfs /tmp --tmpfs /home \
  --ro-bind "$K/rustup" "$K/rustup" --ro-bind "$K/cargo/bin" "$K/cargo/bin" --bind "$K/cargo/registry" "$K/cargo/registry" \
  --bind "$K/cargo/git" "$K/cargo/git" --ro-bind "$TC" "$TC" \
  --bind "$SRC" "$SRC" \
  --setenv HOME /tmp/home --setenv RUSTUP_HOME "$K/rustup" --setenv CARGO_HOME "$K/cargo" --setenv CARGO_NET_OFFLINE true \
  --setenv PATH "$K/cargo/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 --setenv RUSTUP_TOOLCHAIN "${RUST_TOOLCHAIN:-1.97.1}" \
  --chdir "$SRC" /bin/bash -c "$*"

#!/bin/bash
# Builds expaudit (std-only Rust, zero external crates) offline and prints the binary path on the last line.
#   build.sh [TARGET_DIR]   (default: $EXPAUDIT_TARGET, else ${FV_SCRATCH:-${TMPDIR:-/tmp}}/$USER-expaudit-target)
#   RUST_HOME_DIR: optional directory holding a pinned Rust 1.97.1 install (rustup/ and cargo/bin/); when set (and bwrap
#   and cc are available) cargo runs inside bwrap with only that toolchain visible, else the cargo on PATH is used.
set -eu
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
TD=${1:-${EXPAUDIT_TARGET:-}}
[ -n "$TD" ] || TD=${FV_SCRATCH:-${TMPDIR:-/tmp}}/${USER:-u}-expaudit-target
mkdir -p "$TD"
LINKER_ENV=()
if ! command -v cc >/dev/null 2>&1; then
  for cand in /usr/bin/gcc /usr/bin/clang "$HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin/clang" "$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin/clang"; do
    if [ -x "$cand" ]; then LINKER_ENV=(RUSTFLAGS="-C linker=$cand"); break; fi
  done
fi

K=${RUST_HOME_DIR:-}
if [ -n "$K" ] && [ -x /usr/bin/bwrap ] && [ -d "$K/rustup" ] && command -v cc >/dev/null 2>&1; then
  env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
    --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin \
    --ro-bind /etc/ld.so.cache /etc/ld.so.cache --ro-bind-try /etc/passwd /etc/passwd --ro-bind-try /etc/alternatives /etc/alternatives \
    --proc /proc --dev /dev --tmpfs /tmp --tmpfs /home \
    --ro-bind "$K/rustup" "$K/rustup" --ro-bind "$K/cargo/bin" "$K/cargo/bin" \
    --ro-bind "$HERE" "$HERE" --bind "$TD" "$TD" \
    --setenv HOME /tmp/home --setenv RUSTUP_HOME "$K/rustup" --setenv CARGO_HOME /tmp/cargo \
    --setenv CARGO_NET_OFFLINE true --setenv CARGO_TARGET_DIR "$TD" \
    --setenv PATH "$K/cargo/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 --setenv RUSTUP_TOOLCHAIN 1.97.1 \
    --chdir "$HERE" cargo build --release --locked --offline --quiet >&2
else
  (cd "$HERE" && env "${LINKER_ENV[@]}" CARGO_NET_OFFLINE=true CARGO_TARGET_DIR="$TD" cargo build --release --locked --offline --quiet >&2)
fi

B="$TD/release/expaudit"
test -x "$B"
chmod 755 "$B"
sha256sum "$B" >&2
echo "$B"

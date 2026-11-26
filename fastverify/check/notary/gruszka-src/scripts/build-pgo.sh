#!/bin/bash
# Builds Gruszka guided by a profile, as the measured PGO binaries were built
# (milestones 28-31, data/m28/build-pgo.sh in the experiments tree): an
# instrumented release build checks Init at 1 worker, llvm-profdata merges
# what that run measured, and the release build then uses it.
#
# Needs the rustup component llvm-tools (rustup component add llvm-tools),
# or LLVM_PROFDATA set to an llvm-profdata matching rustc's LLVM version.
#
# Usage: scripts/build-pgo.sh [-w WORKERS] INIT.susz [MORE.susz...]
#   -w   workers for the training runs (default 1, as measured)
# The result is $TARGET_DIR/release/gruszka (TARGET_DIR defaults to target).
# FLAGS holds further rustc flags for both builds, e.g.
#   FLAGS="-C target-cpu=native" scripts/build-pgo.sh init.susz
# panic stays unwind (Cargo.toml): Gruszka catches panics to decline.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
workers=1
if [ "${1:-}" = -w ]; then workers=$2; shift 2; fi
[ $# -ge 1 ] || { echo "usage: $0 [-w WORKERS] INIT.susz [MORE.susz...]" >&2; exit 2; }
for t in "$@"; do
    [ -f "$t" ] || { echo "$0: no such file: $t" >&2; exit 2; }
done
flags=${FLAGS:-}
target=${TARGET_DIR:-$root/target}
case "$target" in /*) ;; *) target=$PWD/$target;; esac
# training files may be relative to the caller's directory
train=()
for t in "$@"; do
    case "$t" in /*) train+=("$t");; *) train+=("$PWD/$t");; esac
done

profdata=${LLVM_PROFDATA:-}
if [ -z "$profdata" ]; then
    profdata=$(ls "$(rustc --print sysroot)"/lib/rustlib/*/bin/llvm-profdata 2>/dev/null | head -1 || true)
fi
if [ -z "$profdata" ]; then
    profdata=$(command -v llvm-profdata || true)
fi
[ -n "$profdata" ] && [ -x "$profdata" ] || {
    echo "$0: llvm-profdata not found: rustup component add llvm-tools, or set LLVM_PROFDATA" >&2
    exit 2
}

prof="$target/pgo"
rm -rf "$prof"
mkdir -p "$prof"
cd "$root"
RUSTFLAGS="$flags -Cprofile-generate=$prof" \
    cargo build --release --locked --bin gruszka --target-dir "$target/instrumented"
for t in "${train[@]}"; do
    # every run writes its own raw profile; a verdict other than accepted
    # still trains, but is reported
    v=$(LLVM_PROFILE_FILE="$prof/run-%p-%m.profraw" \
        "$target/instrumented/release/gruszka" "$t" "$workers" 2>/dev/null | tail -1) || true
    echo "train $(basename "$t") w$workers: $v"
done
"$profdata" merge -o "$prof/merged.profdata" "$prof"/*.profraw
rm -f "$prof"/*.profraw
rm -rf "$target/instrumented"
RUSTFLAGS="$flags -Cprofile-use=$prof/merged.profdata" \
    cargo build --release --locked --bin gruszka --target-dir "$target"
echo "built $target/release/gruszka"

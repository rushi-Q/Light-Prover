#!/bin/sh
# BUILD (kind kernel-src): the harness binds the official 4.36 toolchain read-only into kbuild; build against it.
set -eux
# C07: nanoda (official 4c544ed + C07 speedups, nanoda/), offline; crates fetched by the harness from ./Cargo.lock
cargo build --release --locked --offline
ls -la target/release/nanoda_bin
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PATH=$TC/bin:/usr/bin:/bin lake build
ls -la .lake/build/bin

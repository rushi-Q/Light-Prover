#!/bin/bash
# iae-runs.sh ROOT THREADS NAME... : for each project (pinned challenge), --preset sound with the opt-in planner item
# sound-fast-path=importarts-empty instead of sound-fast-path (TAG=iae): the B1-B3 planner then skips Lake's exact
# transitive importArts walk, which only matters for byte-exactness (the sound build is untrusted).
ROOT=$1 T=$2; shift 2
U="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path=importarts-empty,cost-hints,native-pkg,merge,check-tail"
for n in "$@"; do TAG=iae bash "$(dirname "$0")/../../bigprojects/tools/run.sh" "$n" sound "$T" "$ROOT" --unsafe "$U"; done

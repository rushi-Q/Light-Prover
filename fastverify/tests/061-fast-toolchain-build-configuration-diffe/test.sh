#!/bin/bash
# test 061 (kind e2e: the original reproduction, FAST = the package via bin/fastverify, OFFICIAL = lake build 4.33.1 + lean4export + comparator 4.36)
# finding: 061 fast toolchain build configuration differs from the release: System.Platform.target, lean --version, FFI linker flags (libstdc++ vs libc++)
# PASS iff (e2e) for every case the package's final verdict == the official verdict and, when both accept, the exports are identical.
{ # whole script parsed before it runs (safe against edits while running)
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/061.XXXXXX")}; T=$(dirname "$0")/../lib
# part 1: the end-to-end reproduction (package as FAST flow); part 2: the toolchain component rows for 061 (tests/toolchain/run.sh)
bash "$T/xrepro.sh" "$(dirname "$0")" "$W.e2e"; r1=$?
bash "$T/component.sh" 061 "$W.tc" "$(dirname "$0")/../toolchain/run.sh"; r2=$?
cat "$W.e2e.tsv" "$W.tc.tsv" > "$W.tsv" 2>/dev/null; cat "$W.e2e.log" "$W.tc.log" > "$W.log" 2>/dev/null
[ $r1 = 0 ] && [ $r2 = 0 ]
exit $?
}

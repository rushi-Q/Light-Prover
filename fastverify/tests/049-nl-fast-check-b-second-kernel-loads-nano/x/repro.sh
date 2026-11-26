#!/bin/bash
# 049 repro (~1-2 min, any x86-64 host): nl-fast reads ./nano-lean.toml from its WORKING DIRECTORY. Honest toy project
# (proj/, official 4.33.1 build + official lean4export -> challenge.export/solution.export, regenerate with mk.sh).
set -u
H=$(cd "$(dirname "$0")" && pwd); T=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
DK=/scratch/fastverify/checkers/dualkernel; KRUN=${FV_KRUN:-krun}
[ -s "$H/solution.export" ] && [ -s "$H/challenge.export" ] || "$H/mk.sh" || exit 2
G=$DK/target/release/gruszka   # deployed gruszka uses AMD-only SSE4a (finding 001): portable build on Intel nodes
$KRUN "SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $H/solution.export 2" >/dev/null 2>&1
[ $? -eq 132 ] && G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka-v3
echo "gruszka binary: $G"
W=$(mktemp -d /tmp/x01-f049.XXXXXX); trap 'rm -rf "$W"' EXIT; cd "$W"
PATH=$T/bin:$PATH lake comparator --config "$H/comparator.json" --challenge-from-export "$H/challenge.export" --solution-from-export "$H/solution.export" > cmp.log 2>&1
echo "OFFICIAL lake comparator 4.36 (Lean kernel + nanoda)      : exit $?  ($(tail -1 cmp.log))"
$KRUN "sh $H/incwd.sh $H $G"

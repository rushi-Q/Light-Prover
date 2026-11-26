#!/bin/bash
# Carleson: --interface mode for K1-K3 (+ tiny sanity via the g07 test separately)
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
B=$V/carlbase; CHX=$V/carlchx; WS=$V/bp/ws/carleson; CSHA=$(sha256sum $CHX/challenge.export | cut -d' ' -f1)
for tag in K1 K2 K3; do O=$V/carl-incr/${tag}i; rm -rf $O; echo "=== ${tag}i $(date -u +%H:%M:%S)"
  INCR_TC=$V/local/elan/toolchains/leanprover--lean4---v4.33.1 $FVR/tools/incr/incr-reverify.sh $B $V/carl-edits/$tag $CHX $O \
    --challenge-sha256 $CSHA --threads 96 --packages $WS --interface --reuse-plan | tail -1 | cut -c1-600
  cp $O/summary.json $V/results/carleson/${tag}i.json 2>/dev/null
done
